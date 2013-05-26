/* Developed by Hassan S. Matar and Suha Orhun Mutluergil  */
/* 
   Implementation of verification of One-Third Rule Consesus algorithm.
*/

#define NPROCS 3
#define K      2
#define PID

byte gate = ((K == 0) -> 0 : 1);
int count = K;

active [NPROCS] proctype P () {	
	do :: 
		
		d_step {
			count--;
			if
			:: count > 0 -> gate++;
			:: else
			fi;
		}

		d_step {
			count++;
			if
			:: count == 1 -> gate++;
			:: else
			fi;
		}
	od
}

