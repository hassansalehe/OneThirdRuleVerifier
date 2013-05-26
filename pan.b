	switch (t->back) {
	default: Uerror("bad return move");
	case  0: goto R999; /* nothing to undo */

		 /* PROC P */
	case 3: /* STATE 7 */
		sv_restor();
		goto R999;
	case 4: /* STATE 14 */
		sv_restor();
		goto R999;

	case 5: /* STATE 18 */
		;
		p_restor(II);
		;
		;
		goto R999;
	}

