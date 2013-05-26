/* 
   Implementation of verification of One-Third Rule Consesus algorithm.
*/

/* 
     Developed by Hassan S. Matar and Suha Orhun Mutluergil

     (c) 2013
*/

/* Algorithm pseudocode  */
/*
1. Initialization:
2.      Xp := Vp
3. Round r:
4.      Srp:
5.		   send <Xp> to all processes
6.      Trp:
7.         if | HO (p,r)| > 2n / 3 then
8.            Xp := the smallest most often received value
9.            if more than 2n/3 values received are equal to bar<x> then
10.                DECIDE(bar<x>) 			  
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

