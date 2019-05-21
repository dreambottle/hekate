/*
 * Copyright (c) 2018 naehrwert
 * Copyright (c) 2018 Rajko Stojadinovic
 * Copyright (c) 2018-2019 CTCaer
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms and conditions of the GNU General Public License,
 * version 2, as published by the Free Software Foundation.
 *
 * This program is distributed in the hope it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 * more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include <string.h>
#include <stdlib.h>

#include "fe_emmc_tools.h"
#include "../config/config.h"
#include "../gfx/gfx.h"
#include "../gfx/tui.h"
#include "../libs/fatfs/ff.h"
#define LZ4F_STATIC_LINKING_ONLY
#include "../libs/compr/lz4frame.h"
// #include "../libs/compr/lz4frame.c"
#include "../mem/heap.h"
#include "../sec/se.h"
#include "../storage/nx_emmc.h"
#include "../storage/sdmmc.h"
#include "../utils/btn.h"
#include "../utils/util.h"

#define EMMC_BUF_ALIGNED 0xB5000000
#define SDXC_BUF_ALIGNED 0xB6000000
#define MIXD_BUF_ALIGNED 0xB7000000

// start of available IRAM with current release hekate: 0x4001F800
#define IRAM_AVAILABLE_START (0x40010000)//-(1<<10))
#define IRAM_AVAILABLE_END   0x40040000
#define IRAM_VANILLA_HEKATE_START 0x4001F800
#define IRAM3_START 0x40020000
#define IRAM4_START 0x40030000

#define NUM_SECTORS_PER_ITER 8192 // 4MB Cache.
#define OUT_FILENAME_SZ 80
#define HASH_FILENAME_SZ (OUT_FILENAME_SZ + 11) // 11 == strlen(".sha256sums")
#define SHA256_SZ 0x20

extern sdmmc_t sd_sdmmc;
extern sdmmc_storage_t sd_storage;
extern FATFS sd_fs;
extern hekate_config h_cfg;

extern void mc_enable_ahb_redirect();
extern void mc_disable_ahb_redirect();
extern bool sd_mount();
extern void sd_unmount();
extern void emmcsn_path_impl(char *path, char *sub_dir, char *filename, sdmmc_storage_t *storage);

extern u32 dec_time;
extern u32 dec_hash_time;
extern u32 hed_buf_hits;
extern u32 src_buf_hits;
extern u32 dst_buf_hits;
extern u32 cpy_time;
extern u32 cpy_hash_time;
extern u32 cpy_direct_hits;

void _update_filename(char *outFilename, u32 sdPathLen, u32 numSplitParts, u32 currPartIdx)
{
	if (numSplitParts >= 10 && currPartIdx < 10)
	{
		outFilename[sdPathLen] = '0';
		itoa(currPartIdx, &outFilename[sdPathLen + 1], 10);
	}
	else
		itoa(currPartIdx, &outFilename[sdPathLen], 10);
}

typedef enum
{
	PART_BOOT =   (1 << 0),
	PART_SYSTEM = (1 << 1),
	PART_USER =   (1 << 2),
	PART_RAW =    (1 << 3),
	PART_GP_ALL = (1 << 7)
} emmcPartType_t;

typedef enum
{
	NONE = 0,
	LZ4  = 1,
} compressionType_t;

static size_t _print_lz4_error(size_t lz4err) {
	if (LZ4F_isError(lz4err)) {
		gfx_printf("LZ4 Error %d: %s.\n\n", (u32)lz4err, LZ4F_getErrorName(lz4err));
		return lz4err;
	} else {
		return 0;
	}
}

static int _restore_emmc_part_lz4(char *sd_path, sdmmc_storage_t *storage, emmc_part_t *part)
{
	// init metrics
	dec_time = 0;
	dec_hash_time = 0;
	hed_buf_hits = 0;
	src_buf_hits = 0;
	dst_buf_hits = 0;
	cpy_time = 0;
	cpy_hash_time = 0;
	cpy_direct_hits = 0;

	int res = 0;
	FIL fp;

	// align for sd reads - 0x8 bytes
	u8 *buf_sd = (u8 *)IRAM_AVAILABLE_START - 64;
	size_t buf_sd_size_max = (128 << 10) + 64;
	u8 *buf_em = (u8 *)IRAM4_START;//buf_sd + buf_sd_size_max;
	size_t buf_em_size_max = 64<<10;//IRAM_AVAILABLE_END - (UINT)buf_em;//(127 << 10);

	// NX_EMMC_BLOCKSIZE - block size
	UINT buf_sd_size_cur = 0;
	UINT buf_sd_offset = 0;
	UINT buf_em_offset = 0;
	u32 lba_start = part->lba_start;
	u32 lba_end = part->lba_end + 1;
	u32 lba_total = lba_end - lba_start;
	u32 lba_offset = 0;
	UINT lz4_src_size;
	UINT lz4_dst_size;
	LZ4F_dctx *lz4f_dctx = (void*) IRAM_AVAILABLE_START-264;
	LZ4F_decompressOptions_t lz4f_dopt = { .stableDst = 0, .reserved = { 0, 0, 0 } };
	LZ4F_frameInfo_t lz4f_frame_info = LZ4F_INIT_FRAMEINFO;
	u32 lz4_block_size = 64<<10;
	size_t lz4ret;
	u32 timer_ms;
	
	// hack
	// sd_path = "test4MI.lz4";
	// sd_path = "test64KD.lz4";
	// sd_path = "test64KI.lz4";
	// sd_path = "test16KD.lz4";
	// sd_path = "test16KI.lz4";
	// sd_path = "rawnand16KI.lz4";
	sd_path = "rawnand64KI.lz4";

	gfx_con.fntsz = 8;
	gfx_printf("\nOpening: %s\n", sd_path);
	res = f_open(&fp, sd_path, FA_READ);
	if (res)
	{
		gfx_con.fntsz = 16;
		if (res != FR_NO_FILE)
			EPRINTFARGS("Error (%d) while opening backup. Continuing...\n", res);
		else
			WPRINTFARGS("Error (%d) file not found. Continuing...\n", res);
		return 0;
	}

	gfx_con_getpos(&gfx_con.savedx, &gfx_con.savedy);

	{
		// // sd2ram
		// timer_ms = get_tmr_ms();
		// res = f_read(&fp, buf_sd, buf_sd_size_max, &buf_sd_size_cur);
		// timer_ms = get_tmr_ms() - timer_ms;
		// gfx_printf("SD to RAM  %dMiB: %dms, %d MiB/s\n", buf_sd_size_cur>>20, timer_ms, buf_sd_size_cur/(timer_ms<<10));

		// // memcpy ram2ram
		// timer_ms = get_tmr_ms();
		// memcpy((u8 *)EMMC_BUF_ALIGNED, buf_sd, buf_sd_size_max);
		// timer_ms = get_tmr_ms() - timer_ms;
		// gfx_printf("memcpy RAM2RAM %dMiB: %dms, %d MiB/s\n", buf_sd_size_cur>>20, timer_ms, buf_sd_size_cur/(timer_ms<<10));

		// // memcpy ram2iram
		// timer_ms = get_tmr_ms();
		// for (int i=0;i<128;++i)
		// 	memcpy(buf_em, buf_sd, buf_em_size_max);
		// timer_ms = get_tmr_ms() - timer_ms;
		// gfx_printf("memcpy RAM2IRAM %dMiB: %dms, %d MiB/s\n", buf_sd_size_cur>>20, timer_ms, buf_sd_size_cur/(timer_ms<<10));

		// // memcpy iram2iram
		// timer_us = get_tmr_us();
		// for (int i=0;i<256;++i)
		// 	memcpy(IRAM_AVAILABLE_START, buf_em + (i*32), 32<<10);
		// timer_us = get_tmr_us() - timer_us;
		// gfx_printf("memcpy IRAM2IRAM %dKIB: %dms, %d MB/s\n", 8<<10, timer_us, (8<<20)/(timer_us<<10));

		// // SD2IRAM test
		// timer_ms = get_tmr_ms();
		// for (int i=0;i<128;++i)
		// 	res = f_read(&fp, buf_em, buf_em_size_max, &buf_sd_size_cur);
		// timer_ms = get_tmr_ms() - timer_ms;
		// gfx_printf("SD to IRAM 128*%dKiB: %dms, %d KB/s\n", buf_sd_size_cur>>10, timer_ms, 128*buf_sd_size_cur/timer_ms);
	}

	FSIZE_t file_bytes_total = f_size(&fp);
	gfx_printf("================================\n");
	gfx_printf("Backup file size: %d MiB\n", (file_bytes_total >> 20));
	gfx_printf("LZ4_dctx  : 0x%x\n", lz4f_dctx);
	gfx_printf("Buffer in : 0x%x %dKiB\n", buf_sd, (buf_sd_size_max) >> 10);
	gfx_printf("Buffer out: 0x%x %dKiB\n", buf_em, (buf_em_size_max) >> 10);

	timer_ms = get_tmr_ms();
	res = f_read(&fp, buf_sd, buf_sd_size_max, &buf_sd_size_cur);
	timer_ms = get_tmr_ms() - timer_ms;
	gfx_printf("SD to IRAM %dKiB: %dms, %d KB/s\n", buf_sd_size_cur>>10, timer_ms, (buf_sd_size_cur)/timer_ms);
	gfx_printf("\n\n");
	if (res)
	{
		gfx_con.fntsz = 16;
		EPRINTFARGS("\nFatal error (%d) when reading from SD Card", res);
		EPRINTF("\nYour device may be in an inoperative state!\n\nPress any key...\n");

		f_close(&fp);
		return 0;
	}

	// lz4f_dctx = IRAM2_2K_BUF_0;
	// memset(lz4f_dctx, 0, sizeof(lz4f_dctx)); // 200 bytes
	LZ4Fmod_set_dctx_static_location(lz4f_dctx);
	lz4ret = LZ4F_createDecompressionContext(&lz4f_dctx, LZ4F_VERSION);
	if (_print_lz4_error(lz4ret)) {
		f_close(&fp);
		return 0;
	}
	gfx_printf("LZ4 context allocated at 0x%x\n\n", lz4f_dctx);
	
	gfx_printf("LZ4 FRAME INFO.\n");
	lz4_src_size = buf_sd_size_cur;
	lz4ret = LZ4F_getFrameInfo(lz4f_dctx, &lz4f_frame_info, buf_sd, &lz4_src_size);
	buf_sd_offset = lz4_src_size;
	_print_lz4_error(lz4ret);

	lz4_block_size = LZ4F_getBlockSize(lz4f_frame_info.blockSizeID);
	gfx_printf("lz4ret: %d\n", lz4ret);
	gfx_printf("Content size: %dMiB\n", (u32)(lz4f_frame_info.contentSize >> 20));
	gfx_printf("Content checksum present: %d\n", lz4f_frame_info.contentChecksumFlag);
	gfx_printf("Block size ID: %d (%dKiB)\n", lz4f_frame_info.blockSizeID, lz4_block_size>>10);
	gfx_printf("Block checksum present: %d\n", lz4f_frame_info.blockChecksumFlag);
	gfx_printf("Independent blocks: %d\n", lz4f_frame_info.blockMode);
	gfx_printf("\n");
	// todo fail if blocksizeid is not 64K
	// gfx_printf("dctx sizeof: %d\n", sizeof(LZ4F_dctx)); //200
	// gfx_printf("dctx max block size: %d\n", lz4f_dctx->maxBlockSize);
	// gfx_printf("\n\n");

	gfx_printf("Sectors to write: %d (%dMB)\n", lba_total, lba_total>>11);
	gfx_printf("Processing...\n\n");

	gfx_con_getpos(&gfx_con.savedx, &gfx_con.savedy);


	u32 bytes_read = 0;
	timer_ms = get_tmr_ms();

	u32 timer_sd = 0;
	u32 timer_dec = 0;
	u32 timer_post = 0;

	// u32 dbg_loops = 17;
	// 20s at 600kps
	// u32 dbg_loops = 800;
	// 8s at 600kps
	u32 dbg_loops = 300;
	for(; (lba_offset < lba_total) && lz4ret
	    && dbg_loops
		;--dbg_loops
		)
	{
		u32 tmr = get_tmr_ms();
		if (lz4ret > (buf_sd_size_cur - buf_sd_offset))
		{
			// todo count misaligns
			UINT offset_aligned = buf_sd_offset & ~0x7U;
			UINT remaining_alig = buf_sd_size_cur - offset_aligned;
			memcpy(buf_sd, buf_sd+offset_aligned, remaining_alig);
			res = f_read(&fp, buf_sd + remaining_alig, buf_sd_size_max - remaining_alig, &buf_sd_size_cur);
			// gfx_printf("SD READ [%d] %dB; memcopied %dB\n", res, buf_sd_size_cur, remaining_alig);
			buf_sd_offset = buf_sd_offset & 0x7U;
			bytes_read += buf_sd_size_cur;
			buf_sd_size_cur += remaining_alig;
		}
		timer_sd += get_tmr_ms() - tmr;
		
		tmr = get_tmr_ms();
		lz4_src_size = buf_sd_size_cur - buf_sd_offset;
		lz4_src_size = MIN(lz4_src_size, lz4ret);
		lz4_dst_size = buf_em_size_max - buf_em_offset;

		// gfx_printf("src buf: %d / %d ; pass: %d ; hint: %d \n", buf_sd_offset, buf_sd_size_cur, lz4_src_size, lz4ret);
		// gfx_printf("dst buf: %d / %d ; pass: %d \n", buf_em_offset, buf_em_size_max, lz4_dst_size);
		lz4ret = LZ4F_decompress(lz4f_dctx, buf_em, &lz4_dst_size, buf_sd + buf_sd_offset, &lz4_src_size, &lz4f_dopt);
		// after decompression, lz4_*_size vars store a value of how much was actually read/written to buffers.

		buf_sd_offset += lz4_src_size;
		buf_em_offset += lz4_dst_size;
		timer_dec += get_tmr_ms() - tmr;

		tmr = get_tmr_ms();
		int blocks_ready = buf_em_offset / NX_EMMC_BLOCKSIZE;
		if (
			// buf_em_offset == buf_em_size_max ||
			(buf_em_size_max - buf_em_offset) < (64<<10) ||
		    lz4ret == 0
			) {
			// todo write or verify

			// while (!sdmmc_storage_write(storage, lba_curr, num, buf))
			// {
			// 	gfx_con.fntsz = 16;
			// 	EPRINTFARGS("\nFailed to write %d blocks @ LBA %08X\nfrom eMMC. Aborting..\n",
			// 		num, lba_curr);
			// 	EPRINTF("\nYour device may be in an inoperative state!\n\nPress any key and try again...\n");

			// 	f_close(&fp);
			// 	return 0;
			// }
			
			buf_em_offset = buf_em_offset % NX_EMMC_BLOCKSIZE;
			lba_offset += blocks_ready;
		}
		// gfx_printf("loop# : %d       \n", dbg_loops);
		// gfx_printf("lz4ret: %d       \n", (u32)lz4ret);
		// gfx_printf("Sectors covered: %d/%d  \n\n", lba_offset, lba_total);
		if(_print_lz4_error(lz4ret)) break;
		
		u8 btn = btn_wait_timeout(0, BTN_VOL_DOWN | BTN_VOL_UP);
		if ((btn & BTN_VOL_DOWN) && (btn & BTN_VOL_UP))
		{
			gfx_con.fntsz = 16;
			WPRINTF("\n\nDecompression was cancelled!");
			break;
		}
		timer_post += get_tmr_ms() - tmr;
	}

	timer_ms = get_tmr_ms() - timer_ms;
	u32 kbytes_written = lba_offset>>1;

	gfx_printf("timers LZ4 : dec:%d hash:%d bufHits:%d; srcBufHits:%d;\n", dec_time, dec_hash_time, dst_buf_hits, src_buf_hits);
	gfx_printf("timers LZ4 : cpy:%d hash:%d cpyHits:%d; hedBufHits:%d;\n", cpy_time, cpy_hash_time, cpy_direct_hits, hed_buf_hits);
	gfx_printf("timers loop: sd:%d dec:%d post:%d\n", timer_sd, timer_dec, timer_post);
	gfx_printf("LZ4 dec    : %dms, %d KB/s\n", timer_ms, (u32)((((u64)kbytes_written)<<10)/(u64)timer_ms));
	gfx_printf("Decomp     : src %dKiB => dst %dMiB\n", (bytes_read>>10), kbytes_written>>10);

	gfx_printf("Sectors left: %d (should be 0!)\n\n", lba_total - lba_offset);
	// todo better msg, also try pickup next frame (next file?)
	

	// // memcpy iram2iram
	// timer_us = get_tmr_us();
	// for (int i=0;i<256;++i)
	// 	memcpy((void*)IRAM_AVAILABLE_START, (void*)IRAM_VANILLA_HEKATE_START + (i*32), 64<<10);
	// timer_us = get_tmr_us() - timer_us;
	// gfx_printf("BENCH memcpy IRAM2IRAM %dKiB: %dms, %d MB/s\n", 16<<10, timer_us/1000, (16*1000000)/(timer_us));
	// u32 pernand_s = (1953 * timer_us) / 1000000;
	// gfx_printf("32GB would take: %dm %ds\n", pernand_s/60, pernand_s%60);


	LZ4F_freeDecompressionContext(lz4f_dctx);
	gfx_con.fntsz = 16;
	f_close(&fp);
	return 0;
}

static int _restore_emmc_part(char *sd_path, sdmmc_storage_t *storage, emmc_part_t *part, bool allow_multi_part)
{
	/*
	static const u32 SECTORS_TO_MIB_COEFF = 11;

	u32 totalSectors = part->lba_end - part->lba_start + 1;
	u32 currPartIdx = 0;
	u32 numSplitParts = 0;
	u32 lbaStartPart = part->lba_start;
	int res = 0;
	char *outFilename = sd_path;
	u32 sdPathLen = strlen(sd_path);
	u64 fileSize = 0;
	u64 totalCheckFileSize = 0;
	gfx_con.fntsz = 8;

	FIL fp;
	FILINFO fno;

	gfx_con_getpos(&gfx_con.savedx, &gfx_con.savedy);

	bool use_multipart = false;

	if (allow_multi_part)
	{
		// Check to see if there is a combined file and if so then use that.
		if (f_stat(outFilename, &fno))
		{
			// If not, check if there are partial files and the total size matches.
			gfx_printf("No single file, checking for part files...\n");

			outFilename[sdPathLen++] = '.';

			// Stat total size of the part files.
			while ((u32)((u64)totalCheckFileSize >> (u64)9) != totalSectors)
			{
				_update_filename(outFilename, sdPathLen, 99, numSplitParts);

				gfx_con_setpos(gfx_con.savedx, gfx_con.savedy);
				gfx_printf("\nFilename: %s\n", outFilename);

				if (f_stat(outFilename, &fno))
				{
					WPRINTFARGS("Error (%d) file not found '%s'. Aborting...\n", res, outFilename);
					return 0;
				}
				else
					totalCheckFileSize += (u64)fno.fsize;

				numSplitParts++;
			}

			gfx_printf("\n%X sectors total.\n", (u32)((u64)totalCheckFileSize >> (u64)9));

			if ((u32)((u64)totalCheckFileSize >> (u64)9) != totalSectors)
			{
				gfx_con.fntsz = 16;
				EPRINTF("Size of SD Card split backups does not match,\neMMC's selected part size.\n");

				return 0;
			}
			else
			{
				use_multipart = true;
				_update_filename(outFilename, sdPathLen, numSplitParts, 0);
			}
		}
	}

	res = f_open(&fp, outFilename, FA_READ);
	gfx_con_setpos(gfx_con.savedx, gfx_con.savedy);
	gfx_printf("\nFilename: %s\n", outFilename);
	if (res)
	{
		if (res != FR_NO_FILE)
			EPRINTFARGS("Error (%d) while opening backup. Continuing...\n", res);
		else
			WPRINTFARGS("Error (%d) file not found. Continuing...\n", res);
		gfx_con.fntsz = 16;

		return 0;
	}
	else if (!use_multipart && (((u32)((u64)f_size(&fp) >> (u64)9)) != totalSectors)) // Check total restore size vs emmc size.
	{
		gfx_con.fntsz = 16;
		EPRINTF("Size of the SD Card backup does not match,\neMMC's selected part size.\n");
		f_close(&fp);

		return 0;
	}
	else
	{
		fileSize = (u64)f_size(&fp);
		gfx_printf("\nTotal restore size: %d MiB.\n\n",
			(u32)((use_multipart ? (u64)totalCheckFileSize : fileSize) >> (u64)9) >> SECTORS_TO_MIB_COEFF);
	}

	u8 *buf = (u8 *)MIXD_BUF_ALIGNED;

	u32 lba_curr = part->lba_start;
	u32 bytesWritten = 0;
	u32 prevPct = 200;
	int retryCount = 0;

	u32 num = 0;
	u32 pct = 0;

	gfx_con_getpos(&gfx_con.savedx, &gfx_con.savedy);

	while (totalSectors > 0)
	{
		// If we have more than one part, check the size for the split parts and make sure that the bytes written is not more than that.
		if (numSplitParts != 0 && bytesWritten >= fileSize)
		{
			// If we have more bytes written then close the file pointer and increase the part index we are using
			f_close(&fp);
			memset(&fp, 0, sizeof(fp));
			currPartIdx++;

			if (h_cfg.verification)
			{
				// Verify part.
				if (_dump_emmc_verify(storage, lbaStartPart, outFilename, part))
				{
					EPRINTF("\nPress any key and try again...\n");

					return 0;
				}
			}

			_update_filename(outFilename, sdPathLen, numSplitParts, currPartIdx);

			// Read from next part.
			gfx_con_setpos(gfx_con.savedx, gfx_con.savedy);
			gfx_printf("Filename: %s\n\n", outFilename);

			lbaStartPart = lba_curr;

			// Try to open the next file part
			res = f_open(&fp, outFilename, FA_READ);
			if (res)
			{
				gfx_con.fntsz = 16;
				EPRINTFARGS("Error (%d) opening file %s.\n", res, outFilename);

				return 0;
			}
			fileSize = (u64)f_size(&fp);
			bytesWritten = 0;
		}

		retryCount = 0;
		num = MIN(totalSectors, NUM_SECTORS_PER_ITER);

		res = f_read(&fp, buf, NX_EMMC_BLOCKSIZE * num, NULL);
		if (res)
		{
			gfx_con.fntsz = 16;
			EPRINTFARGS("\nFatal error (%d) when reading from SD Card", res);
			EPRINTF("\nYour device may be in an inoperative state!\n\nPress any key and try again now...\n");

			f_close(&fp);
			return 0;
		}
		while (!sdmmc_storage_write(storage, lba_curr, num, buf))
		{
			EPRINTFARGS("Error writing %d blocks @ LBA %08X\nto eMMC (try %d), retrying...",
				num, lba_curr, ++retryCount);

			msleep(150);
			if (retryCount >= 3)
			{
				gfx_con.fntsz = 16;
				EPRINTFARGS("\nFailed to write %d blocks @ LBA %08X\nfrom eMMC. Aborting..\n",
					num, lba_curr);
				EPRINTF("\nYour device may be in an inoperative state!\n\nPress any key and try again...\n");

				f_close(&fp);
				return 0;
			}
		}
		pct = (u64)((u64)(lba_curr - part->lba_start) * 100u) / (u64)(part->lba_end - part->lba_start);
		if (pct != prevPct)
		{
			tui_pbar(0, gfx_con.y, pct, 0xFFCCCCCC, 0xFF555555);
			prevPct = pct;
		}

		lba_curr += num;
		totalSectors -= num;
		bytesWritten += num * NX_EMMC_BLOCKSIZE;
	}
	tui_pbar(0, gfx_con.y, 100, 0xFFCCCCCC, 0xFF555555);

	// Restore operation ended successfully.
	f_close(&fp);

	if (h_cfg.verification)
	{
		// Verify restored data.
		if (_dump_emmc_verify(storage, lbaStartPart, outFilename, part))
		{
			EPRINTF("\nPress any key and try again...\n");

			return 0;
		}
		else
			tui_pbar(0, gfx_con.y, 100, 0xFF96FF00, 0xFF155500);
	}

	gfx_con.fntsz = 16;
	gfx_puts("\n\n");
	*/

	gfx_puts("disabled\n\n");
	return 1;
}

static void _restore_emmc_selected(emmcPartType_t restoreType, compressionType_t compression)
{
	int res = 0;
	u32 timer = 0;
	gfx_clear_partial_grey(0x1B, 0, 1256);
	tui_sbar(true);
	gfx_con_setpos(0, 0);

	// Disabled. Welcome to the Danger Zone!
	/*
	gfx_printf("%kThis may render your device inoperative!\n\n", 0xFFFFDD00);
	gfx_printf("Are you really sure?\n\n%k", 0xFFCCCCCC);
	if ((restoreType & PART_BOOT) || (restoreType & PART_GP_ALL))
	{
		gfx_puts("The mode you selected will only restore\nthe ");
		if (restoreType & PART_BOOT)
			gfx_puts("boot ");
		gfx_puts("partitions that it can find.\n");
		gfx_puts("If it is not found, it will be skipped\nand continue with the next.\n\n");
	}
	gfx_con_getpos(&gfx_con.savedx, &gfx_con.savedy);

	u8 failsafe_wait = 10;
	while (failsafe_wait > 0)
	{
		gfx_con_setpos(gfx_con.savedx, gfx_con.savedy);
		gfx_printf("%kWait... (%ds)    %k", 0xFF888888, failsafe_wait, 0xFFCCCCCC);
		msleep(1000);
		failsafe_wait--;
	}
	gfx_con_setpos(gfx_con.savedx, gfx_con.savedy);

	gfx_puts("Press POWER to Continue.\nPress VOL to go to the menu.\n\n\n");

	u32 btn = btn_wait();
	if (!(btn & BTN_POWER))
		goto out;
	*/

	if (compression == LZ4)
		mc_enable_ahb_redirect();

	if (!sd_mount())
		goto out;

	sdmmc_storage_t storage;
	sdmmc_t sdmmc;
	if (!sdmmc_storage_init_mmc(&storage, &sdmmc, SDMMC_4, SDMMC_BUS_WIDTH_8, 4))
	{
		EPRINTF("Failed to init eMMC.");
		goto out;
	}

	int i = 0;
	char sdPath[OUT_FILENAME_SZ];

	timer = get_tmr_s();
	if (restoreType & PART_BOOT)
	{
		const u32 BOOT_PART_SIZE = storage.ext_csd.boot_mult << 17;

		emmc_part_t bootPart;
		memset(&bootPart, 0, sizeof(bootPart));
		bootPart.lba_start = 0;
		bootPart.lba_end = (BOOT_PART_SIZE / NX_EMMC_BLOCKSIZE) - 1;
		for (i = 0; i < 2; i++)
		{
			strcpy(bootPart.name, "BOOT0");
			bootPart.name[4] = (u8)('0' + i);

			if (compression == LZ4)
				strcpy(bootPart.name + 5, ".lz4");

			gfx_printf("%k%02d: %s (%07X-%07X)%k\n", 0xFF00DDFF, i,
				bootPart.name, bootPart.lba_start, bootPart.lba_end, 0xFFCCCCCC);

			sdmmc_storage_set_mmc_partition(&storage, i + 1);

			emmcsn_path_impl(sdPath, "/restore", bootPart.name, &storage);

			if (compression == LZ4)
				res = _restore_emmc_part_lz4(sdPath, &storage, &bootPart);
			else
				res = _restore_emmc_part(sdPath, &storage, &bootPart, false);
		}
	}

	if (restoreType & PART_GP_ALL)
	{
		sdmmc_storage_set_mmc_partition(&storage, 0);

		LIST_INIT(gpt);
		nx_emmc_gpt_parse(&gpt, &storage);
		LIST_FOREACH_ENTRY(emmc_part_t, part, &gpt, link)
		{
			gfx_printf("%k%02d: %s (%07X-%07X)%k\n", 0xFF00DDFF, i++,
				part->name, part->lba_start, part->lba_end, 0xFFCCCCCC);

			emmcsn_path_impl(sdPath, "/restore/partitions/", part->name, &storage);
			res = _restore_emmc_part(sdPath, &storage, part, false);
		}
		nx_emmc_gpt_free(&gpt);
	}

	if (restoreType & PART_RAW)
	{
		// Get GP partition size dynamically.
		const u32 RAW_AREA_NUM_SECTORS = storage.sec_cnt;

		emmc_part_t rawPart;
		memset(&rawPart, 0, sizeof(rawPart));
		rawPart.lba_start = 0;
		rawPart.lba_end = RAW_AREA_NUM_SECTORS - 1;
		char *filename = (compression == LZ4) ? "rawnand.bin.lz4" : "rawnand.bin";
		strcpy(rawPart.name, filename);

		{
			gfx_printf("%k%02d: %s (%07X-%07X)%k\n", 0xFF00DDFF, i++,
				rawPart.name, rawPart.lba_start, rawPart.lba_end, 0xFFCCCCCC);

			emmcsn_path_impl(sdPath, "/restore", rawPart.name, &storage);
			if (compression == LZ4)
				res = _restore_emmc_part_lz4(sdPath, &storage, &rawPart);
			else 
				res = _restore_emmc_part(sdPath, &storage, &rawPart, true);
		}
	}

	timer = get_tmr_s() - timer;
	gfx_putc('\n');
	gfx_printf("Time taken: %dm %ds.\n", timer / 60, timer % 60);
	sdmmc_storage_end(&storage);
	if (res && h_cfg.verification)
		gfx_printf("\n%kFinished and verified!%k\nPress any key...\n", 0xFF96FF00, 0xFFCCCCCC);
	else if (res)
		gfx_printf("\nFinished! Press any key...\n");

out:
	sd_unmount();
	if (compression == LZ4)
		mc_disable_ahb_redirect();
	btn_wait();
}

void restore_emmc_boot()        { _restore_emmc_selected(PART_BOOT, NONE); }
void restore_emmc_boot_lz4()    { _restore_emmc_selected(PART_BOOT, LZ4); }
void restore_emmc_rawnand()     { _restore_emmc_selected(PART_RAW, NONE); }
void restore_emmc_rawnand_lz4() { _restore_emmc_selected(PART_RAW, LZ4); }
void restore_emmc_gpp_parts()   { _restore_emmc_selected(PART_GP_ALL, NONE); }
