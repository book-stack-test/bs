/*
  zk.cpp : based on 3.cpp from http://www.ecrypt.eu.org/stream/ciphers/zkcrypt/zkcryptsource.zip
*/

#include <stdio.h>
#include <stdlib.h>

#include <iostream>
#include <string>
#include <sstream>

#include <time.h>

#if (defined _MSC_VER) || (defined __BORLANDC__)
  #include <io.h>
  #include <fcntl.h>
#endif

#ifdef __GNUC__
  #define __int64 long long
#endif

using namespace std;

/* //////////////////////////////////////////// */

typedef unsigned long  int dword;
typedef unsigned      char byte;


FILE *stream;       /* log */
FILE *diehard;      /* output result */


/* /////////////////////////////////////////// */

/* mode */

dword mode;

#define MODE_FB_ENABLE      (1<<0)  /* feedback enable */
#define MODE_FB_A           (1<<1)  /* feedback mode A */
#define MODE_FB_B           (1<<2)  /* feedback mode B */

#define MODE_BRAWNIAN       (1<<3)  /* brawnian enable */

#define ENABLE_SINGLE_TIER  (1<<4)  /* enable single tier select by decoder 10S */
#define TOP_TIER_ALWAYS     (1<<5)  /* force top tier for debugging purpose 10S */
#define MID_TIER_ALWAYS     (1<<6)  /* force mid tier for debugging purpose 10S */
#define BOT_TIER_ALWAYS     (1<<7)  /* force bot tier for debugging purpose 10S */

#define ENABLE_ODDNS        (1<<8)  /* enable ODDN permutations 10S */

#define SAMPLE              (1<<9)  /* sample immunizer & feedback */

/* global variables */

dword top_control;      /* tier control */
dword mid_control;
dword bot_control;
dword com_control;      /* common control */

dword p_random_clock;   /* 4C */

dword control_cfg_FF;   /* control config FF 13C */

dword top_cipher_word;  /* initial value for nLSFRs from 128 bits crypto key preload */
dword mid_cipher_word;
dword bot_cipher_word;

dword top_result;       /* tier result */
dword mid_result;
dword bot_result;

dword bank_result;      /* majority 2/3 result */ /* old version: XORed three results */

dword hash_control;     /* ODDNs */
dword hash_result;

dword imm_data;         /* immunizer data FFs */
dword imm_result;       /* immunizer result */

/*dword sample;*/           /* sample */

dword data_result;
dword message_in;

dword feedback_word;    /* feedback word store */


/* ////////////////////////////////////////////
// nLSFR                                     //
//////////////////////////////////////////// */

/* declare nLSFR */
      dword shift_reg  [6] = { 0,  0,  0,  0,  0,  0};  /* shift registers bank */
const int   shift_len  [6] = {13, 14, 15, 17, 18, 19};  /* registers length */
const dword shift_mask [6] = {  /* feedback masks */
    (1<<0)+(1<<3)+(1<<4)+(1<<6)+(1<<9)+(1<<10),     /* 13 */
    (1<<0)+(1<<2)+(1<<5)+(1<<6)+(1<<9)+(1<<11),     /* 14 */
    (1<<0)+(1<<1)+(1<<2)+(1<<6)+(1<<7)+(1<<11),     /* 15 */
    (1<<0)+(1<<2)+(1<<5)+(1<<8)+(1<<10)+(1<<11)+(1<<13)+(1<<14),     /* 17 */
    (1<<0)+(1<<3)+(1<<5)+(1<<7)+(1<<8) +(1<<11)+(1<<12)+(1<<13)+(1<<14)+(1<<16),     /* 18 */
    (1<<0)+(1<<2)+(1<<5)+(1<<7)+(1<<8) +(1<<9) +(1<<10)+(1<<12)+(1<<15)+(1<<17)      /* 19 */
	};

/* //////////////////////////////////////////// */

#define DEF_LSFR_13     0
#define DEF_LSFR_14     1
#define DEF_LSFR_15     2
#define DEF_LSFR_17     3
#define DEF_LSFR_18     4
#define DEF_LSFR_19     5

/* /////////////////////////////////////////// */

void nLSFR_iteration (dword cipher_word, dword feedback_word, int enable_cipher, int slip, int index)
{
    dword *reg = &shift_reg[index];
    dword next_data;
    dword mask = ((1<<shift_len[index])-1);
    int   feedback_bit;

    if (enable_cipher)
    {
        *reg  = cipher_word;        /* parallel load of top_cipher word */
    }
    else
    {
        next_data  = (*reg << 1);   /* shift left */

        feedback_bit = (*reg >> (shift_len[index]-1));          /* MSB bit */
        feedback_bit = feedback_bit ^ (slip!=0);            /* slip */
        feedback_bit = feedback_bit ^ (((*reg)&(mask>>1))==0);          /* register zero (except MSB bit) */

        if (feedback_bit & 1)
        {
            next_data ^= shift_mask[index];        /* xor mask if feedback */
        }

        next_data ^= feedback_word;

        *reg = next_data & mask;    /* shift iteration */
    }
}

/* /////////////////////////////////////////// */

dword tier_shift (dword input)
{
	dword data;

	data  = input << 1;
	data |= input >> 31;
	data ^= input;

	return data;
}

/* /////////////////////////////////////////// */
/* /////////////////////////////////////////// */
/* /////////////////////////////////////////// */
/* tier control fields */

#define SLIP_LEFT   (1<<0)  
#define SLIP_RIGHT  (1<<1)
#define CLOCK       (1<<2)	/* enable nLSFR iteration */
#define LOAD        (1<<4)	/* enable loading cipher word */
#define BROWN       (1<<5)	/* enable tier reversed pseudo brownian motion bits */

/* /////////////////////////////////////////// */

void top_tier (void)
{
    dword mask_13bits   = ((1<<13)-1);
    
	dword cipher_left   = top_cipher_word & mask_13bits;      // bits [12:0]
    dword feedback_left = feedback_word   & mask_13bits;      // bits [12:0]

    dword cipher_right   = top_cipher_word >> 13;             // bits [31:13]
    dword feedback_right = feedback_word   >> 13;             // bits [31:13]

	if (top_control & LOAD)
	{
		/* load cipher_word to nLSFR */
		nLSFR_iteration (cipher_left,  0, 1, 0, DEF_LSFR_13);     /* left  nLSFR */
		nLSFR_iteration (cipher_right, 0, 1, 0, DEF_LSFR_19);     /* right nLSFR */
	}
	else
	{
		/* iteration with feedback_word */
		nLSFR_iteration (0, feedback_left,  0, com_control & SLIP_LEFT,  DEF_LSFR_13);     /* left  nLSFR */
		nLSFR_iteration (0, feedback_right, 0, com_control & SLIP_RIGHT, DEF_LSFR_19);     /* right nLSFR */
	}

    top_result = shift_reg[DEF_LSFR_13] | (shift_reg[DEF_LSFR_19] << 13);
}

/* /////////////////////////////////////////// */

void mid_tier (void)
{
    dword mask_18bits   = ((1<<18)-1);
    
	dword cipher_left   = mid_cipher_word & mask_18bits;      // bits [17:0]
    dword feedback_left = feedback_word   & mask_18bits;      // bits [17:0]

    dword cipher_right   = mid_cipher_word >> 18;             // bits [31:18]
    dword feedback_right = feedback_word   >> 18;             // bits [31:18]

	if (mid_control & LOAD)
	{
		/* load cipher_word to nLSFR */
		nLSFR_iteration (cipher_left,  0, 1, 0, DEF_LSFR_18);     /* left  nLSFR */
		nLSFR_iteration (cipher_right, 0, 1, 0, DEF_LSFR_14);     /* right nLSFR */
	}
	else
	{
		/* iteration with feedback_word */
		nLSFR_iteration (0, feedback_left,  0, com_control & SLIP_LEFT,  DEF_LSFR_18);     /* left  nLSFR */
		nLSFR_iteration (0, feedback_right, 0, com_control & SLIP_RIGHT, DEF_LSFR_14);     /* right nLSFR */
	}

    mid_result = shift_reg[DEF_LSFR_18] | (shift_reg[DEF_LSFR_14] << 18);
}

/* /////////////////////////////////////////// */

void bot_tier (void)
{
    dword mask_15bits   = ((1<<15)-1);
    
	dword cipher_left   = bot_cipher_word & mask_15bits;      // bits [14:0]
    dword feedback_left = feedback_word   & mask_15bits;      // bits [14:0]

    dword cipher_right   = bot_cipher_word >> 15;             // bits [31:15]
    dword feedback_right = feedback_word   >> 15;             // bits [31:15]

	if (bot_control & LOAD)
	{
		/* load cipher_word to nLSFR */
		nLSFR_iteration (cipher_left,  0, 1, 0, DEF_LSFR_15);     /* left  nLSFR */
		nLSFR_iteration (cipher_right, 0, 1, 0, DEF_LSFR_17);     /* right nLSFR */
	}
	else
	{
		/* iteration with feedback_word */
		nLSFR_iteration (0, feedback_left,  0, com_control & SLIP_LEFT,  DEF_LSFR_15);     /* left  nLSFR */
		nLSFR_iteration (0, feedback_right, 0, com_control & SLIP_RIGHT, DEF_LSFR_17);     /* right nLSFR */
	}

    bot_result = shift_reg[DEF_LSFR_15] | (shift_reg[DEF_LSFR_17] << 15);
}

/* /////////////////////////////////////////// */

dword majority_2_3 (dword a, dword b, dword c)
{
    dword a1 = a & b;
    dword b1 = a & c;
    dword c1 = b & c;
    
    dword res = a1 | b1 | c1;

    return (res);
}

/* /////////////////////////////////////////// */

/* non-linear feedback shift register bank */

void nLSFR_bank (void)
{
    dword top_out, mid_out, bot_out;

    /* top tier */
    if (top_control & CLOCK)
    {
		top_tier ();
		top_out = tier_shift (top_result);	/* top tier reversed pseudo brownian motion bits */
    }
    else
    if (top_control & BROWN)
    {
	    top_out = tier_shift (top_result);
    }
    else
    {
	    top_out = top_result;
    }

    /* middle tier */
    if (mid_control & CLOCK)
    {
		mid_tier ();
		mid_out = tier_shift (mid_result);	/* mid tier reversed pseudo brownian motion bits */
    }
    else
    if (mid_control & BROWN)
    {
	    mid_out = tier_shift (mid_result);
    }
    else
    {
	    mid_out = mid_result;
    }

    /* bottom tier */
    if (bot_control & CLOCK)
    {
		bot_tier ();
		bot_out = tier_shift (bot_result);	/* bot tier reversed pseudo brownian motion bits */
    }
    else
    if (bot_control & BROWN)
    {
	    bot_out = tier_shift (bot_result);
    }
    else
    {
	    bot_out = bot_result;
    }

    /* old version: XOR three tiers output */
    /* bank_result = top_out ^ mid_out ^ bot_out; */

    /* new version 2005.05.11: majority 2/3 */
    bank_result = majority_2_3 (top_out, mid_out, bot_out);
}

/* /////////////////////////////////////////// */

/* Hash matrix & ODDN complementor */
/* This version without bit permutation */

#define TOP_ODDN    (1<<0)
#define MID_ODDN    (1<<1)
#define BOT_ODDN    (1<<2)
#define ODDN4       (1<<3)

#define TOP_ODDN_MASK    ((1<<2)+(1<<5)+(1<<8)+(1<<11)+(1<<14)+(1<<17)+(1<<20)+(1<<23)+(1<<26))
#define MID_ODDN_MASK    ((1<<0)+(1<<1)+(1<<3)+(1<<6)+(1<<9)+(1<<12)+(1<<15)+(1<<18)+(1<<21)+(1<<24)+(1<<27)+(1<<29)+(1<<30))
#define BOT_ODDN_MASK    ((1<<7)+(1<<10)+(1<<13)+(1<<16)+(1<<19)+(1<<22)+(1<<25)+(1<<28)+(1<<31))
#define ODDN4_MASK       (1<<4)

dword mjuggle_hash_toggle; /* 4C */
dword hash_vector;

#define VECTOR_A    (1<<0)
#define VECTOR_B    (1<<1)
#define VECTOR_C    (1<<2)
#define VECTOR_D    (1<<3)

byte hash_table_A [32] = { 9,18, 5,11,22,12,30,19, 7,15,31,25,28,24, 6, 3,17,13,27,23, 1, 2,26,21, 4,20, 8,16, 0,14,10,29};
byte hash_table_B [32] = {30,15, 6,12,25,18,16, 9,19, 7, 3,31, 0,29,27,21,14,28,24,17,23, 5,10, 2,11,22,13,26,20, 8, 4, 1};
byte hash_table_C [32] = {19, 7,14,29, 3,27, 0,13,25,16,15,30,20, 1,26,31, 8, 6, 2, 4, 9,18,12,10,21,11,22, 5,24,23,28,17};

void hash_mix (byte *table)
{
    dword data = 0;
    int i;

    for (i=31; i>=0; i--)
    {
        data <<= 1;
        data |= ((hash_result >> table[i]) & 1);
    }

    hash_result = data;
}

void Hash_matrix (void) /* hash matrix & oddn permute 17P */
{
    hash_result = bank_result;

    /* hash matrix A,B,C */
    if (hash_vector & VECTOR_A)
        hash_mix (hash_table_A);
    else
    if (hash_vector & VECTOR_B)
        hash_mix (hash_table_B);
    else
    if (hash_vector & VECTOR_C)
        hash_mix (hash_table_C);

    /* oddb permute */

    if (hash_control & TOP_ODDN)
		hash_result ^= TOP_ODDN_MASK;

    if (hash_control & MID_ODDN)
		hash_result ^= MID_ODDN_MASK;

    if (hash_control & BOT_ODDN)
		hash_result ^= BOT_ODDN_MASK;

    if (hash_control & ODDN4)
		hash_result ^= ODDN4_MASK;
}

/* /////////////////////////////////////////// */

dword ROL3_func (dword input)  /* rotate left 3 bits */
{
    dword data;
	data  = input << 3;
	data |= input >> (32-3);
    return (data);
}

dword ROR1_func (dword input)  /* rotate right 1 bits */
{
    dword data;
	data  = input >> 1;
	data |= input << (32-1);
    return (data);
}

/* Immunizer */

/* immunizer with two carry
void Immunizer (void)
{
    dword carry;
    dword new_data;

    imm_result = hash_result ^ imm_data;

    if (sample)
    {
        carry    = hash_result & imm_data;
        new_data = hash_result ^ ( ROR1_func(carry) | ROL3_func(carry) );
        imm_data = new_data;
    }
}
*/

void Immunizer (void)
{
    imm_result = hash_result ^ imm_data;    /* generate output */

    if (mode & SAMPLE)
    {
        imm_data = hash_result;
    }
}

/* /////////////////////////////////////////// */

dword top_fbk;
dword mid_fbk;
dword bot_fbk;

/* /////////////////////////////////////////// */

void cypher_machine (void)
{
    /* store MSB of all nLSFR for tier control feedback */

    top_fbk  = (shift_reg [DEF_LSFR_14] >> 13) << 2;
    top_fbk |= (shift_reg [DEF_LSFR_18] >> 17) << 3;

    mid_fbk  = (shift_reg [DEF_LSFR_19] >> 18) << 2;
    mid_fbk |= (shift_reg [DEF_LSFR_13] >> 12) << 3;

    bot_fbk  = (shift_reg [DEF_LSFR_17] >> 16) << 2;
    bot_fbk |= (shift_reg [DEF_LSFR_15] >> 14) << 3;


    nLSFR_bank ();

    Hash_matrix ();

    Immunizer ();

    data_result = message_in ^ imm_result;

    if (mode & SAMPLE)
        if (mode & MODE_FB_ENABLE)
            feedback_word = (mode & MODE_FB_A) ? data_result : imm_result;
}

/* /////////////////////////////////////////// */

dword top_cnt;      /* control counter 4bit */
dword mid_cnt;
dword bot_cnt;

dword top_sfr3;     /* control LSFR 3bit */
dword mid_sfr5;     /* control LSFR 5bit */
dword bot_sfr6;     /* control LSFR 6bit */

byte counter_table [32] = { /* counter upto 15 reload values 13C */
    0x00, 0x01, 0x02, 0x03,
    0x01, 0x00, 0x03, 0x02,
    0x02, 0x03, 0x00, 0x01,
    0x03, 0x02, 0x01, 0x00,
    0x08, 0x09, 0x0A, 0x0B,
    0x09, 0x08, 0x0B, 0x0A,
    0x0A, 0x0B, 0x08, 0x09,
    0x0B, 0x0A, 0x09, 0x08 };

byte sfr3_table [8] = {  /* nLSFR 3bits 13C */
    0x01, 0x03, 0x04, 0x07,
    0x00, 0x02, 0x05, 0x06 };

byte sfr5_table [32] = { /* nLSFR 5bits 14C */
    0x01, 0x02, 0x05, 0x07, 0x08, 0x0A, 0x0D, 0x0F,
    0x10, 0x12, 0x15, 0x17, 0x18, 0x1A, 0x1D, 0x1F,
    0x00, 0x03, 0x04, 0x06, 0x09, 0x0B, 0x0C, 0x0E,
    0x11, 0x13, 0x14, 0x16, 0x19, 0x1B, 0x1C, 0x1E };

byte sfr6_table [64] = { /* nLSFR 6bits 15C */
    0x01, 0x03, 0x04, 0x07, 0x08, 0x0B, 0x0C, 0x0F,
    0x10, 0x13, 0x14, 0x17, 0x18, 0x1B, 0x1C, 0x1F,
    0x20, 0x23, 0x24, 0x27, 0x28, 0x2B, 0x2C, 0x2F,
    0x30, 0x33, 0x34, 0x37, 0x38, 0x3B, 0x3C, 0x3F,
    0x00, 0x02, 0x05, 0x06, 0x09, 0x0A, 0x0D, 0x0E,
    0x11, 0x12, 0x15, 0x16, 0x19, 0x1A, 0x1D, 0x1E,
    0x21, 0x22, 0x25, 0x26, 0x29, 0x2A, 0x2D, 0x2E,
    0x31, 0x32, 0x35, 0x36, 0x39, 0x3A, 0x3D, 0x3E };

/* /////////////////////////////////////////// */

void top_brown (void)
{
    /* generate brown */
    if (mode & MODE_BRAWNIAN)
    {
        if (top_sfr3 & 1)   /* bit 0 of sfr */
            top_control |= BROWN;
    }
}

void top_slip (void)
{
    /* generate slip */
    if (top_cnt == 15)                      
    {
        if (top_sfr3 & 4)   /* bit 2 of sfr */
            top_control |= SLIP_LEFT;
        else
            top_control |= SLIP_RIGHT;
    }
}

void top_controller (void)  /* 13C */
{
    dword a;

    if (top_control & SLIP_LEFT)
    {
        control_cfg_FF ^= 1;        /* switch T-FF if previous SLIP_LEFT was 1 */
    }

    top_control = 0;

    /* counter behavioral */
    if (top_cnt < 15)               
    {
        top_cnt ++;
    }
    else
    {
        a  = top_sfr3 & 3;
        a |= top_fbk;       /* sfr14 bit 13, sfr18 bit 17 */
        a |= (top_sfr3 & 0x02) << 3;
        top_cnt = counter_table [a];
    }

    /* sfr3 behavioral */
    a = sfr3_table [top_sfr3];
    top_sfr3 = a;

    /* generate new controls */
    top_brown ();
    top_slip ();
}

/* /////////////////////////////////////////// */

void mid_brown (void)
{
    /* generate brown */
    if (mode & MODE_BRAWNIAN)
    {
        if (mid_sfr5 & 1)   /* bit 0 of sfr */
            mid_control |= BROWN;
    }
}

void mid_slip (void)
{
    /* generate slip */
    if (mid_cnt == 15)                      
    {
        if (mid_sfr5 & 16)   /* bit 4 of sfr */
            mid_control |= SLIP_LEFT;
        else
            mid_control |= SLIP_RIGHT;
    }
}

void mid_controller (void)  /* 14C */
{
    dword a;

    if (mid_control & SLIP_LEFT)
    {
        control_cfg_FF ^= 2;        /* switch T-FF if previous SLIP_LEFT was 1 */
    }

    mid_control = 0;

    /* counter behavioral */
    if (mid_cnt < 15)               
    {
        mid_cnt ++;
    }
    else
    {
        a  = mid_sfr5 & 3;
        a |= mid_fbk;       /* sfr19 bit 18, sfr13 bit 12 */
        a |= (mid_sfr5 & 0x08) << 1;
        mid_cnt = counter_table [a];
    }

    /* sfr5 behavioral */
    a = sfr5_table [mid_sfr5];
    mid_sfr5 = a;

    /* generate new controls */
    mid_brown ();
    mid_slip ();
}

/* /////////////////////////////////////////// */

void bot_brown (void)
{
    /* generate brown */
    if (mode & MODE_BRAWNIAN)
    {
        if (bot_sfr6 & 1)   /* bit 0 of sfr */
            bot_control |= BROWN;
    }
}

void bot_slip (void)
{
    /* generate slip */
    if (bot_cnt == 15)                      
    {
        if (bot_sfr6 & 32)   /* bit 5 of sfr */
            bot_control |= SLIP_LEFT;
        else
            bot_control |= SLIP_RIGHT;
    }
}

void bot_controller (void)  /* 15C */
{
    dword a;

    if (bot_control & SLIP_LEFT)
    {
        control_cfg_FF ^= 4;        /* switch T-FF if previous SLIP_LEFT was 1 (clock delay) */
    }

    bot_control = 0;

    /* counter behavioral */
    if (bot_cnt < 15)               
    {
        bot_cnt ++;
    }
    else
    {
        a  = bot_sfr6 & 3;
        a |= bot_fbk;       /* sfr17 bit 16, sfr15 bit 14 */
        a |= (bot_sfr6 & 0x10) << 0;
        bot_cnt = counter_table [a];
    }

    /* sfr6 behavioral */
    a = sfr6_table [bot_sfr6];
    bot_sfr6 = a;

    /* generate new controls */
    bot_brown ();
    bot_slip ();
}

/* /////////////////////////////////////////// */

dword clock_sfr5;   /* 4C */
dword clock_sfr2;   /* 4C */
dword clock_p_rand;
dword clock_t_rand;
dword clock_odd4;
dword clock_mjuggle;

byte sfr2_table [8] = {  /* nLSFR 2bits with carry 4C */
    0x03, 0x03, 0x01, 0x02,
    0x03, 0x03, 0x01, 0x03 };

int p_random_clock_generator () /* p_random_clock, ODDN4, MJuggle hash toggle */
{
    dword a,c, odd4;

    /* p_random_clock generation */
/* wrong behavioral because of negedge FF (F2)
    p_random_clock = (clock_t_rand != clock_p_rand);
    clock_p_rand = clock_t_rand;
    if ((clock_sfr5 & 16) || (clock_sfr2 & 2))
    {
        clock_t_rand = (clock_t_rand == 0);
    }
*/

    /* p_random_clock generation */
    p_random_clock = 0;
    if ((clock_sfr5 & 16) || (clock_sfr2 & 2))
    {
        clock_t_rand = (clock_t_rand == 0);
        p_random_clock = 1;
    }

    /* ODDN4 */
    odd4 = clock_odd4;
    clock_odd4 = (clock_sfr5 & 2) ? ODDN4 : 0;

    /* MJuggle hash toggle */
    mjuggle_hash_toggle = clock_mjuggle;
    clock_mjuggle = (clock_sfr5 & 0x10) == 0;

    /* sfr2 behavioral */
    c = ((clock_sfr5 & 0x0F) == 0) ? 4 : 0; /* carry */
    a = sfr2_table [clock_sfr2 + c];
    clock_sfr2 = a;

    /* sfr5 behavioral */
    a = sfr5_table [clock_sfr5];
    clock_sfr5 = a;
    if (com_control & SLIP_RIGHT)
    {
        clock_sfr5 ^= 1;        /* random clock slip from 10S */
    }

    return (odd4);
}

/* /////////////////////////////////////////// */

byte johnson_table [32] = {
    0x01, 0x02, 0x04, 0x01, 0x08, 0x01, 0x01, 0x01, // j=0
    0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
    0x01, 0x08, 0x04, 0x01, 0x02, 0x01, 0x01, 0x01, // j=1
    0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01 };

void johnson_counter (void)
{
    dword a;

    a = hash_vector + (mjuggle_hash_toggle << 4);

    hash_vector = (dword) johnson_table[a];
}

/* /////////////////////////////////////////// */

void tier_controller (void)   /* 10S */
{
    int oddn_4;

    if (p_random_clock)
    {
        top_controller ();      /* generate top_brown, top_left_slip, top_right_slip, top_config_clock */
        mid_controller ();
        bot_controller ();
    }

    /* hash matrix stepper 18S */
    johnson_counter ();

    /* generate (p)random_clock enable */

    oddn_4 = p_random_clock_generator ();  /* p_random_clock,  ODDN4*/

    /* decode 3 config clocks & generate tier clocks */

    if (mode & ENABLE_SINGLE_TIER)
    {
        /* decode 3 config controls */
        switch (control_cfg_FF)
        {
        case 0:
        case 3:
        case 5: top_control |= CLOCK;   /* enable clock iteration */
                top_control |= BROWN;   /* enable (force) browning */
                break;
        case 4:
        case 7: mid_control |= CLOCK;   /* enable clock iteration */
                mid_control |= BROWN;   /* enable (force) browning */
                break;
        case 1:
        case 2:
        case 6: bot_control |= CLOCK;   /* enable clock iteration */
                bot_control |= BROWN;   /* enable (force) browning */
                break;
        }
    }
    else
    {
        if (mode & TOP_TIER_ALWAYS)
            top_control |= CLOCK;   /* enable clock iteration */
        if (mode & MID_TIER_ALWAYS)
            mid_control |= CLOCK;   /* enable clock iteration */
        if (mode & TOP_TIER_ALWAYS)
            bot_control |= CLOCK;   /* enable clock iteration */
    }

    /* added 2005.05.11 no all three browns together */
    if ((top_control & BROWN) && (mid_control & BROWN) && (bot_control & BROWN))
    {
        switch (control_cfg_FF)
        {
            case 0:
            case 3:
            case 5: top_control &= ~BROWN;   /* disable browning */
                    break;
            case 4:
            case 7: mid_control &= ~BROWN;    /* disable browning */
                    break;
            case 1:
            case 2:
            case 6: bot_control &= ~BROWN;    /* disable browning */
                    break;
        }
    }

    /* decode 3 L/R slips & generate left hand slip and right hand slip */

    com_control = 0;

    if ((top_control & SLIP_LEFT) || (mid_control & SLIP_LEFT) || (bot_control & SLIP_RIGHT))
    {
        com_control |= SLIP_LEFT;
    }

    if ((top_control & SLIP_RIGHT) || (mid_control & SLIP_RIGHT) || (bot_control & SLIP_LEFT))
    {
        com_control |= SLIP_RIGHT;
    }

    /* generate 4 ODDN */

    hash_control = 0;   /* TOP_ODDN */

    if (mode & ENABLE_ODDNS)
    {
        hash_control  = control_cfg_FF;     /* top_oddn = top_config_ff, mid = mid, bot = bot */
        hash_control |= oddn_4;             /* 4C */
    }
}

/* /////////////////////////////////////////// */

void system_reset (void)
{
	int i;
	for (i=0; i<6; i++)
	{
		shift_reg [i] = 0;		/* nLSFR */
	}

    top_result = 0;
    mid_result = 0;
    bot_result = 0;

    imm_data = 0;

    feedback_word = 0;  /* also must be 0 if feedback is disabled */

    top_cnt = 0;      /* control counter 4bit */
    mid_cnt = 0;
    bot_cnt = 0;

    top_sfr3 = 0;     /* control LSFR 3bit */
    mid_sfr5 = 0;     /* control LSFR 5bit */
    bot_sfr6 = 0;     /* control LSFR 6bit */

    top_control = 0;
    mid_control = 0;
    bot_control = 0;
    control_cfg_FF = 0;

    clock_sfr5 = 0;   /* 4C */
    clock_sfr2 = 3;   /* 4C */
    clock_p_rand = 0;
    clock_t_rand = 0;
    clock_odd4 = 0;
    clock_mjuggle = 0;

    p_random_clock = 0;         /* p_random_clock enable 4C */
    mjuggle_hash_toggle = 0;    /* 4C */
    hash_vector = VECTOR_D;     /* 18S */
}

/* /////////////////////////////////////////// */

void init_preload (dword *crypto_key)   /* initial value for nLSFRs from 128 bits crypto key preload */
{

    system_reset ();

    top_control = LOAD;
    top_cipher_word = crypto_key[1];    /* [63:32] */
    top_tier ();
    top_control = 0;

    mid_control = LOAD;
    mid_cipher_word = crypto_key[2];    /* [95:64] */
    mid_tier ();
    mid_control = 0;

    bot_control = LOAD;
    bot_cipher_word = crypto_key[3];    /* [127:96] */
    bot_tier ();
    bot_control = 0;

    top_sfr3 = (crypto_key[0] >>  0) & 0x07; /* [ 2: 0] top control LSFR 3bit */
    top_cnt  = (crypto_key[0] >>  3) & 0x0F; /* [ 6: 3] top control counter 4bit */

    mid_sfr5 = (crypto_key[0] >>  7) & 0x1F; /* [11: 7] mid control LSFR 5bit */
    mid_cnt  = (crypto_key[0] >> 12) & 0x0F; /* [15:12] mid control counter 4bit */

    bot_sfr6 = (crypto_key[0] >> 16) & 0x3F; /* [21:16] bot control LSFR 5bit */
    bot_cnt  = (crypto_key[0] >> 22) & 0x0F; /* [25:22] bot control counter 4bit */

            /* (crypto_key[0] >> 26) & 0x03;    [27:26] hash mux driver */

    clock_sfr5 = (crypto_key[0] >> 28) & 0x0F; /* [31:28] (p) random clock LSFR 4bit */

    top_brown ();       /* generate initial browning & slipping */
    top_slip ();
    mid_brown ();
    mid_slip ();
    bot_brown ();
    bot_slip ();

    top_control |= CLOCK;   /* enable initial clock iteration */
    top_control |= BROWN;   /* enable (force) browning */
}

/* /////////////////////////////////////////// */

/* 1 - each clock, N - each N clocks */
#define SAMPLE_PERIOD		1

void host (dword *crypto_key_128)
{
    init_preload (crypto_key_128);

    fprintf (stream, "clk_cycle, clk_sfr5/2, (p)rand_clk, T/M/B_counter, T/M/B_sfr, cfg_FF, Lslip/Rslip, 6xLSFRs, T/M/B_brown, sample, result\n\n");

    for (int i=0; i<10000; i++)  /* 100 iteration */
    {
        message_in = 0;     /* for RNG mode */

		if (SAMPLE_PERIOD != 0)
		{
			/* SAMPLE each N iterations */
			if ((i % SAMPLE_PERIOD)==0)
			  mode |= SAMPLE;
			else
			  mode &= ~SAMPLE;
		}
		else
		{
			/* SAMPLE each iteration */
			mode |= SAMPLE;     /* sample each clock */
		}

        cypher_machine ();

        tier_controller ();     /* 10S */

        /* debug output 
        fprintf (stream, "# ");
        fprintf (stream, "%.4x  ", i);
        fprintf (stream, "%.2x ",  clock_sfr5);
        fprintf (stream, "%.2x  ", clock_sfr2);
        fprintf (stream, "%.1x  ", p_random_clock);
        fprintf (stream, "%.2x ",  top_cnt);
        fprintf (stream, "%.2x ",  mid_cnt);
        fprintf (stream, "%.2x  ", bot_cnt);
        fprintf (stream, "%.2x ",  top_sfr3);
        fprintf (stream, "%.2x ",  mid_sfr5);
        fprintf (stream, "%.2x  ", bot_sfr6);
        fprintf (stream, "%.2x  ", control_cfg_FF);
        fprintf (stream, "%.1x ",  (com_control & SLIP_LEFT)  != 0);
        fprintf (stream, "%.1x  ", (com_control & SLIP_RIGHT) != 0);
        fprintf (stream, "%.8x  ", shift_reg[0]);
        fprintf (stream, "%.8x  ", shift_reg[1]);
        fprintf (stream, "%.8x  ", shift_reg[2]);
        fprintf (stream, "%.8x  ", shift_reg[3]);
        fprintf (stream, "%.8x  ", shift_reg[4]);
        fprintf (stream, "%.8x   ", shift_reg[5]);
        fprintf (stream, "%.1x ",  (top_control & (BROWN|CLOCK))  != 0);
        fprintf (stream, "%.1x ",  (mid_control & (BROWN|CLOCK))  != 0);
        fprintf (stream, "%.1x   ",(bot_control & (BROWN|CLOCK))  != 0);
        fprintf (stream, "%.1x   ",(mode & SAMPLE) != 0);
        fprintf (stream, "%.8x \n", data_result);
*/
        /* diehard output */
        fprintf (diehard, "%.8x", data_result);
        if ((i % 10) == 9)
            fprintf (diehard, "\n");
    }
}


/* /////////////////////////////////////////////////////////////////
void lsfr_test (int index)
{
    int i;

    printf("\nlsfr %.1d test\n", index);

    shift_reg[index] = 0x1;

    printf("00 = %.4x\n", shift_reg[index]);

    for (i=1; i<54; i++)
    {
        nLSFR_iteration (0,         // cipher_word
                         0,         // feedback_word
                         0,         // cipher_reset
                         0,         // enable_cipher (parallel load)
                         0,         // slip
                         index);    // index
        printf("%.2d = %.4x\n", i, shift_reg[index]);
    }
}
*/


///////////////////////////////////////////////////////////
// print time

int Print_Time (FILE *stream)
{
#if 0
    static struct tm *newtime;
    char am_pm[] = "AM";
    time_t long_time;

//    if (init)
//    {
        time( &long_time );                /* Get time as long integer. */
        newtime = localtime( &long_time ); /* Convert to local time. */
//    }
//    else
//    {
        if( newtime->tm_hour > 12 )        /* Set up extension. */
                strcpy( am_pm, "PM" );
        if( newtime->tm_hour > 12 )        /* Convert from 24-hour */
                newtime->tm_hour -= 12;    /*   to 12-hour clock.  */
        if( newtime->tm_hour == 0 )        /*Set hour to 12 if midnight. */
                newtime->tm_hour = 12;

        fprintf (stream, "Starting time: %.19s %s\n\n", asctime( newtime ), am_pm );
//    }
#endif
    return (0);
}


#if 0
int main(int argc, char* argv[])
{
    dword crypto_key_128 [4] = {0x43265778,0x67634546,0x23465373,0x65778786};      /* 128 bits crypto key */

    stream  = fopen ("log.txt", "w");
    diehard = fopen ("diehard.txt", "w");

    Print_Time (stream);      // print start time

    mode =  0
        /* + MODE_FB_ENABLE     */
         + MODE_FB_A          
         + MODE_BRAWNIAN      
         + ENABLE_SINGLE_TIER
         + ENABLE_ODDNS       
        ;
    
    host (crypto_key_128);

    fclose( stream );
    fclose( diehard );
}
#endif

// =========

unsigned char zkKey[16];
unsigned long zkRunCount;

void zkInit() // based on main() and host() functions
{
  zkRunCount = 0;
  mode =  0
  /* + MODE_FB_ENABLE     */
   + MODE_FB_A          
   + MODE_BRAWNIAN      
   + ENABLE_SINGLE_TIER
   + ENABLE_ODDNS;

  unsigned long unikey[4], sum;
  int i,j;
  for(i=0; i<4; i++) // for big-endian support
  {
    sum=0;
    for(j=0; j<4; j++)
      sum |= zkKey[i*4+j] << (j*8);
    unikey[i] = sum;
  }
  init_preload ((unsigned long*) unikey);
}

void zkSetKey(unsigned char* key)
{
  memcpy(zkKey, key, 16);
  zkInit();
}

string KeyToStr()
{
  int i;
  char sss[128];
  string res;
  for(i=0; i<16; i++)
  {
    sprintf(sss, "%02x", zkKey[i]);
    res = res + sss;
  }
  return res;
}

unsigned long zkGetBits() // based on host() function
{
    message_in = 0;     /* for RNG mode */

    if (SAMPLE_PERIOD != 0)
    {
      /* SAMPLE each N iterations */
      if ((zkRunCount % SAMPLE_PERIOD)==0)
        mode |= SAMPLE;
      else
        mode &= ~SAMPLE;
    }
    else
    {
      /* SAMPLE each iteration */
      mode |= SAMPLE;     /* sample each clock */
    }

    cypher_machine ();
    tier_controller ();     /* 10S */

    zkRunCount++;

    /* diehard output */
    return data_result;
}

// ==========================

void PrintHelp()
{
  printf("ZK-Crypt generator. Writes the cipher's output into the stdout.\n");
  printf("Program usage:\n");
  printf("  zk [-k key] -n num -q\n");
  printf("    -k - specifies 128-bit key for the cipher as a hexadecimal number.\n");
  printf("      The prefix 0x is optional. If the parameter is omitted then\n");
  printf("      random generated key is used. The key is printed to stderr by default.\n");
  printf("    -n - specifies the number of bits to produce.\n");
  printf("    -q - quiet mode. Do not print the key to stderr.\n");
  printf("    -? - print this screen.\n");
  printf("Samples:\n");
  printf("  zk -k 0x0123456789abcdeffedcba9876543210 -n 67108864 -q\n");
  printf("  zk -k fedcba98765432100123456789abcdef -n 134217728 >data.bin\n");
  printf("  zk -n 268435456\n");
}

void Quit()
{
  PrintHelp();
  exit(1);
}

int main(int argc, char* argv[])
{
#ifdef _MSC_VER
  _setmode(_fileno(stdout), _O_BINARY);
#endif
#ifdef __BORLANDC__
   setmode(_fileno(stdout), O_BINARY);
#endif

  char digits1[] = "0123456789abcdef";
  char digits2[] = "ABCDEF";
  char back[256];
  memset(back, 100, 256);
  int i, j;
  for(i=0; i<16; i++) back[digits1[i]]=i;
  for(i=0; i<6; i++) back[digits2[i]]=i+10;

// parse commandline parameters
  __int64 nn=-1;
  char kk[16];
  bool qq = false;
  bool randomkey = true;

  for(i=1; i<argc; i++)
  {
    string arg = argv[i];
    bool onemore = argc>i+1;
    if(onemore)
    {
      if(arg=="-k")
      {
        i++;
        arg = argv[i];
        if((arg.length()>2)&&(arg.substr(0,2)=="0x"))
          arg = arg.substr(2);
        if(arg.length()>32)
        {
          printf("ERROR: The length of the key must not exceed 128-bit length.\n");
          Quit();
        }
        memset(kk,0,16);
        for(j=0; j<arg.length(); j++)
        {
          char c = back[arg[j]];
          if(c==100)
          {
            printf("ERROR: The entered key is not a hexadecimal value.\n");
            Quit();
          }
          kk[j/2] |= c << (4*(1-(j%2)));
        }
        randomkey = false;
      } else
      if(arg=="-n")
      {
        i++;
        istringstream is(argv[i]);
        is >> nn;
        if(is.fail()) Quit();
      } else Quit();
    } else
    {
      if(arg=="-q") qq = true;
      else Quit();
    }
  }
  
  if(nn<1)
  {
    printf("ERROR: You shoud enter a positive -n parameter.\n");
    Quit();
  }

  if(randomkey)
  {
    srand( (unsigned)time( NULL ) );
    for(i=0; i<16; i++)
      kk[i] = rand()&0xff;
  }

  zkSetKey((unsigned char*)kk);

  if(!qq)
    fprintf(stderr,"Key used: 0x%s\n",KeyToStr().c_str());

  __int64 k,n;
  n = nn/32;
  unsigned long val;

  for(k=0; k<n; k++)
  {
    val = zkGetBits();
    putchar(val & 0xff);
    putchar((val>>8) & 0xff);
    putchar((val>>16) & 0xff);
    putchar((val>>24) & 0xff);
  }
  val = zkGetBits();

  j = ((nn%32)+7)/8;
  for(i=0; i<j; i++)
  {
    putchar(val& 0xff);
    val >>= 8;
  }

  return 0;
}
