/* 
   Implementation of verification of One-Third Rule Consesus algorithm.

     Developed by Hassan S. Matar and Suha Orhun Mutluergil
     (c) 2013
*/

/* number of processes participating */
#define NPROCS 4

/* define rounds */
#define ROUNDS 10
byte round = 0;
byte startRound = 0;

byte waitSms = 0;

mtype = {FIVE, FOUR, THREE, TWO, ONE};

mtype msg = ONE;

/* message channels */
mtype messages[NPROCS];

/* heard-of set definition*/
typedef HO {
    mtype   recvMsgs[NPROCS];
    //bit      ho_list[NPROCS];
    byte
   size
};


active [NPROCS] proctype P () {

    // propose value
    mtype Xp = _pid + 1;

    // initiate the set
     HO HO_Set;

    // block till everyone comes here
    startRound = startRound+1;
    do
         :: (startRound == NPROCS) -> break;
         :: else skip;
    od;
     
     //send message and update Heard-of set
    atomic {
           messages[_pid] = Xp;
           //HO_Set.ho_list[_pid] = 1;
           HO_Set.size =  0;
     };

     // wait untill everyone attempts to send his message
     waitSms = waitSms + 1;
    do
         :: (waitSms == NPROCS) -> break;
         :: else skip;
    od;

     // start receiving messages from other processes
     atomic { 
         byte process;
         HO_Set.size =  0;
         for (process : 0 .. (NPROCS-1) ) {

            //non-deterministically receive message
            if 
                 :: true -> skip;
                 :: true -> 
                          atomic {
                              HO_Set.recvMsgs[HO_Set.size] = messages[process];
                              //HO_Set.ho_list[process] = 1;
                              HO_Set.size =  HO_Set.size + 1;
                          }
            fi;
       };

          // check Heard-of set to decide on the proposed value
          if
               :: (HO_Set.size > ((2 * NPROCS) / 3)) 
                       -> d_step {

                            mtype hash[NPROCS];
                            byte index;
                            for(index: 0 .. (HO_Set.size-1)) {
                                    hash[ (HO_Set.recvMsgs[index]  - 1)] = hash[ (HO_Set.recvMsgs[index]  - 1) ] + 1; 
                           };
                            byte max= 0;

                            for(index: 0 .. (NPROCS-1)) {
                                    if 
                                        ::(hash[ index] > max) ->
                                                        max = hash[index];
                                                        Xp = index+1;
                                         :: else -> skip;

                                    fi
                           };

                            if
                                 :: (max > ((2 * NPROCS) / 3) ) -> printf("Process %d decided\n", _pid) //DECIDE
                                 :: else -> skip;
                            fi
                       
                       };
               :: else -> skip;
         fi;
       };  
}
