#define rand	pan_rand
#if defined(HAS_CODE) && defined(VERBOSE)
	#ifdef BFS_PAR
		bfs_printf("Pr: %d Tr: %d\n", II, t->forw);
	#else
		cpu_printf("Pr: %d Tr: %d\n", II, t->forw);
	#endif
#endif
	switch (t->forw) {
	default: Uerror("bad forward move");
	case 0:	/* if without executable clauses */
		continue;
	case 1: /* generic 'goto' or 'skip' */
		IfNotBlocked
		_m = 3; goto P999;
	case 2: /* generic 'else' */
		IfNotBlocked
		if (trpt->o_pm&1) continue;
		_m = 3; goto P999;

		 /* PROC P */
	case 3: /* STATE 7 - verify.pml:16 - [D_STEP] */
		IfNotBlocked

		reached[0][7] = 1;
		reached[0][t->st] = 1;
		reached[0][tt] = 1;

		if (TstOnly) return 1;

		sv_save();
		S_000_0: /* 2 */
		now.count = (now.count-1);
#ifdef VAR_RANGES
		logval("count", now.count);
#endif
		;
S_004_0: /* 2 */
S_001_0: /* 2 */
		if (!((now.count>0)))
			goto S_004_1;
S_002_0: /* 2 */
		gate = (((int)gate)+1);
#ifdef VAR_RANGES
		logval("gate", ((int)gate));
#endif
		;
		goto S_005_0;
S_004_1: /* 3 */
S_003_0: /* 2 */
		/* else */;
		goto S_005_0;
S_004_2: /* 3 */
		Uerror("blocking sel in d_step (nr.0, near line 18)");
S_005_0: /* 2 */
		goto S_013_0;
S_013_0: /* 1 */

#if defined(C_States) && (HAS_TRACK==1)
		c_update((uchar *) &(now.c_state[0]));
#endif
		_m = 3; goto P999;

	case 4: /* STATE 14 - verify.pml:24 - [D_STEP] */
		IfNotBlocked

		reached[0][14] = 1;
		reached[0][t->st] = 1;
		reached[0][tt] = 1;

		if (TstOnly) return 1;

		sv_save();
		S_007_0: /* 2 */
		now.count = (now.count+1);
#ifdef VAR_RANGES
		logval("count", now.count);
#endif
		;
S_011_0: /* 2 */
S_008_0: /* 2 */
		if (!((now.count==1)))
			goto S_011_1;
S_009_0: /* 2 */
		gate = (((int)gate)+1);
#ifdef VAR_RANGES
		logval("gate", ((int)gate));
#endif
		;
		goto S_012_0;
S_011_1: /* 3 */
S_010_0: /* 2 */
		/* else */;
		goto S_012_0;
S_011_2: /* 3 */
		Uerror("blocking sel in d_step (nr.1, near line 26)");
S_012_0: /* 2 */
		goto S_015_0;
S_015_0: /* 1 */

#if defined(C_States) && (HAS_TRACK==1)
		c_update((uchar *) &(now.c_state[0]));
#endif
		_m = 3; goto P999;

	case 5: /* STATE 18 - verify.pml:32 - [-end-] (0:0:0 - 1) */
		IfNotBlocked
		reached[0][18] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */
	case  _T5:	/* np_ */
		if (!((!(trpt->o_pm&4) && !(trpt->tau&128))))
			continue;
		/* else fall through */
	case  _T2:	/* true */
		_m = 3; goto P999;
#undef rand
	}

