----------------------------- MODULE ticketing3 -----------------------------
EXTENDS Integers, TLC, Sequences, FiniteSets

CONSTANTS NUMCLIENTS, MALICIOUS, NUMSEATS, INITMONEY

\* Min of two naturals/integers (TLA+ has no built-in Min(a,b) operator)
Min2(a, b) == IF a <= b THEN a ELSE b

(* --algorithm ticketing {
    variables
        BankAccount = [x \in AllParticipants |-> IF x = 0 THEN 0 ELSE INITMONEY];
        Channels    = [x \in AllParticipants |-> <<>>];

        seatMap     = [s \in 1..NUMSEATS |-> "available"];

        Tickets     = [c \in 1..NUMCLIENTS |-> {}];

        CState      = [c \in 1..NUMCLIENTS |-> "idle"];
        
        MyTickets   = [m \in AllMalicious |-> {}] 

    define {

        AllMalicious == IF MALICIOUS THEN {-1} ELSE {}
        AllHonest == {i \in 1..NUMCLIENTS : TRUE}
        AllClients == AllHonest \union AllMalicious
        AllParticipants == AllClients \union {0}
        Password == [p \in AllParticipants |-> 2000 + p] \* new security check
        

        Seats == 1..NUMSEATS
        SeatStates == {"available", "paid"}

        IPs == Nat \union {-1} 
        TransactionType == {"buy", "cancel", "confirm", "deny"}
        bankIDType == AllParticipants \union {-2}

       MessageType == [type : TransactionType,
                    from : IPs,
                    seat : Seats,
                    bankID : bankIDType,
                    password : Nat]      \* new field 

       M0 == [type |-> "buy",
               from |-> 0,
               seat |-> 1,
               bankID |-> 0,
               password |-> 0]

        Money(p) == BankAccount[p]

        \* -----------------------------
        \* 
        \* -----------------------------

        TypeOK ==
          /\ BankAccount \in [AllParticipants -> Int]
          /\ Channels \in [AllParticipants -> Seq(MessageType)]
          /\ seatMap \in [Seats -> SeatStates]
          /\ Tickets \in [AllHonest -> SUBSET Seats]
          /\ CState \in [AllHonest -> {"idle","waiting","done"}]
          /\ MyTickets \in [AllMalicious -> SUBSET Seats]

        MoneyTicketsInv ==
          \A c \in AllHonest :
            BankAccount[c] + Cardinality(Tickets[c]) = INITMONEY

        \* all tickets held by honest clients are paid for
        TicketsPaidInv ==
          \A c \in AllHonest :
            \A s \in Tickets[c] : seatMap[s] = "paid"

        \* No double selling of seats
        NoDoubleSell ==
          \A s \in Seats :
            Cardinality({c \in AllHonest : s \in Tickets[c]}) <= 1
        
        \* Stops the code once a malicious client obtens a ticket    
        MaliciousHasNoTickets ==
            \A m \in AllMalicious : MyTickets[m] = {}
            
        \* -----------------------------
        \* Stop condition
        \* -----------------------------
        AllDone ==
          /\ \A c \in AllHonest : CState[c] = "done"
          /\ \A p \in AllParticipants : Len(Channels[p]) = 0

        Terminates == <>AllDone
    }

    fair process (Server = 0)
    variables
        id = 0;
        ip = 0;
        internalReq = M0;
    {
        s1: while (~AllDone) {

            WW:
            await (Len(Channels[ip]) > 0);

            GET:
            internalReq := Head(Channels[ip]);
            Channels[ip] := Tail(Channels[ip]);

            TREAT:
            if (internalReq.type = "buy") {

                if ( seatMap[internalReq.seat] = "available"
                     /\ internalReq.bankID \in AllHonest
                     /\ internalReq.password = Password[internalReq.bankID]
                     /\ BankAccount[internalReq.bankID] > 0) {

                    
                    seatMap[internalReq.seat] := "paid";

                    BankAccount := [BankAccount EXCEPT
                                      ![internalReq.bankID] = @ - 1,
                                      ![0] = @ + 1];

                    Tickets := [Tickets EXCEPT
                                  ![internalReq.bankID] = @ \union {internalReq.seat}];

                    Channels[internalReq.from] :=
                        Append(Channels[internalReq.from],
                               [type |-> "confirm",
                                from |-> 0,
                                seat |-> internalReq.seat,
                                bankID |-> -2,
                                password |-> 0]);
                } else {
                    Channels[internalReq.from] :=
                        Append(Channels[internalReq.from],
                               [type |-> "deny",
                                from |-> 0,
                                seat |-> internalReq.seat,
                                bankID |-> -2,
                                password |-> 0]);
                }

            } else {
                skip; \* without cancel for now
            };
        };

        Done_:
        while (TRUE) { skip; }
    }

    fair process (HClient \in AllHonest)
    variables
        id = self;
        ip = self;

        wantSeat = 1;
        reply = M0;

        target = 0;
        availSeats = {};
    {
        InitTarget:
        target := CHOOSE k \in 0..Min2(INITMONEY, NUMSEATS) : TRUE;

        s1: while (CState[self] # "done") {

            CheckDone:
            if (Cardinality(Tickets[self]) >= target
                \/ (\A s \in Seats : seatMap[s] = "paid")) {
                CState[self] := "done";
            } else {

                BWaitIdle:
                await (CState[self] = "idle");

                BSend:
                CState[self] := "waiting";

                
                availSeats := {s \in Seats : seatMap[s] = "available"};
                wantSeat := CHOOSE s \in availSeats : TRUE;

                Channels[0] := Append(Channels[0],
                                     [type |-> "buy",
                                      from |-> ip,
                                      seat |-> wantSeat,
                                      bankID |-> id,
                                      password |-> Password[id]]);

                BWaitReply:
                await (Len(Channels[ip]) > 0);
                reply := Head(Channels[ip]);
                Channels[ip] := Tail(Channels[ip]);

                
                BUpdate:
                skip;

                CState[self] := "idle";
            }
        };
        
        Done_: 
        while (TRUE) { skip; };
    }
    
   fair process (MClient \in AllMalicious)
    variables
        ip = -1;
        targetID = 0;
        targetSeat = 1;
        reply = M0;
        scamsCount = 0;
      
    {
        MStep: 
            while (scamsCount < 1 /\ ~AllDone) {     
            with (h \in AllHonest, s \in {seat \in Seats : seatMap[seat] = "available"}) {
                targetID := h;
                targetSeat := s;
            };
            
            MSend:
            Channels[0] := Append(Channels[0], [type |-> "buy", from |-> ip, 
                                                 seat |-> targetSeat, bankID |-> targetID,
                                                 password |-> Password[self]]);
            scamsCount := scamsCount + 1;
    
            MGetReply:
            await (Len(Channels[ip]) > 0);
            reply := Head(Channels[ip]);
            Channels[ip] := Tail(Channels[ip]);
    
            MStore: 
            if (reply.type = "confirm") {
                MyTickets[self] := MyTickets[self] \cup {reply.seat};
            
            }
        }
    }
    
    
    
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "18185e" /\ chksum(tla) = "7393185d")
\* Label s1 of process Server at line 98 col 13 changed to s1_
\* Label Done_ of process Server at line 148 col 9 changed to Done__
\* Process variable id of process Server at line 94 col 9 changed to id_
\* Process variable ip of process Server at line 95 col 9 changed to ip_
\* Process variable ip of process HClient at line 154 col 9 changed to ip_H
\* Process variable reply of process HClient at line 157 col 9 changed to reply_
VARIABLES BankAccount, Channels, seatMap, Tickets, CState, MyTickets, pc

(* define statement *)
 AllMalicious == IF MALICIOUS THEN {-1} ELSE {}
 AllHonest == {i \in 1..NUMCLIENTS : TRUE}
 AllClients == AllHonest \union AllMalicious
 AllParticipants == AllClients \union {0}
 Password == [p \in AllParticipants |-> 2000 + p]


 Seats == 1..NUMSEATS
 SeatStates == {"available", "paid"}

 IPs == Nat \union {-1}
 TransactionType == {"buy", "cancel", "confirm", "deny"}
 bankIDType == AllParticipants \union {-2}

MessageType == [type : TransactionType,
             from : IPs,
             seat : Seats,
             bankID : bankIDType,
             password : Nat]

M0 == [type |-> "buy",
        from |-> 0,
        seat |-> 1,
        bankID |-> 0,
        password |-> 0]

 Money(p) == BankAccount[p]





 TypeOK ==
   /\ BankAccount \in [AllParticipants -> Int]
   /\ Channels \in [AllParticipants -> Seq(MessageType)]
   /\ seatMap \in [Seats -> SeatStates]
   /\ Tickets \in [AllHonest -> SUBSET Seats]
   /\ CState \in [AllHonest -> {"idle","waiting","done"}]
   /\ MyTickets \in [AllMalicious -> SUBSET Seats]

 MoneyTicketsInv ==
   \A c \in AllHonest :
     BankAccount[c] + Cardinality(Tickets[c]) = INITMONEY


 TicketsPaidInv ==
   \A c \in AllHonest :
     \A s \in Tickets[c] : seatMap[s] = "paid"


 NoDoubleSell ==
   \A s \in Seats :
     Cardinality({c \in AllHonest : s \in Tickets[c]}) <= 1


 MaliciousHasNoTickets ==
     \A m \in AllMalicious : MyTickets[m] = {}




 AllDone ==
   /\ \A c \in AllHonest : CState[c] = "done"
   /\ \A p \in AllParticipants : Len(Channels[p]) = 0

 Terminates == <>AllDone

VARIABLES id_, ip_, internalReq, id, ip_H, wantSeat, reply_, target, 
          availSeats, ip, targetID, targetSeat, reply, scamsCount

vars == << BankAccount, Channels, seatMap, Tickets, CState, MyTickets, pc, 
           id_, ip_, internalReq, id, ip_H, wantSeat, reply_, target, 
           availSeats, ip, targetID, targetSeat, reply, scamsCount >>

ProcSet == {0} \cup (AllHonest) \cup (AllMalicious)

Init == (* Global variables *)
        /\ BankAccount = [x \in AllParticipants |-> IF x = 0 THEN 0 ELSE INITMONEY]
        /\ Channels = [x \in AllParticipants |-> <<>>]
        /\ seatMap = [s \in 1..NUMSEATS |-> "available"]
        /\ Tickets = [c \in 1..NUMCLIENTS |-> {}]
        /\ CState = [c \in 1..NUMCLIENTS |-> "idle"]
        /\ MyTickets = [m \in AllMalicious |-> {}]
        (* Process Server *)
        /\ id_ = 0
        /\ ip_ = 0
        /\ internalReq = M0
        (* Process HClient *)
        /\ id = [self \in AllHonest |-> self]
        /\ ip_H = [self \in AllHonest |-> self]
        /\ wantSeat = [self \in AllHonest |-> 1]
        /\ reply_ = [self \in AllHonest |-> M0]
        /\ target = [self \in AllHonest |-> 0]
        /\ availSeats = [self \in AllHonest |-> {}]
        (* Process MClient *)
        /\ ip = [self \in AllMalicious |-> -1]
        /\ targetID = [self \in AllMalicious |-> 0]
        /\ targetSeat = [self \in AllMalicious |-> 1]
        /\ reply = [self \in AllMalicious |-> M0]
        /\ scamsCount = [self \in AllMalicious |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "s1_"
                                        [] self \in AllHonest -> "InitTarget"
                                        [] self \in AllMalicious -> "MStep"]

s1_ == /\ pc[0] = "s1_"
       /\ IF ~AllDone
             THEN /\ pc' = [pc EXCEPT ![0] = "WW"]
             ELSE /\ pc' = [pc EXCEPT ![0] = "Done__"]
       /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, CState, 
                       MyTickets, id_, ip_, internalReq, id, ip_H, wantSeat, 
                       reply_, target, availSeats, ip, targetID, targetSeat, 
                       reply, scamsCount >>

WW == /\ pc[0] = "WW"
      /\ (Len(Channels[ip_]) > 0)
      /\ pc' = [pc EXCEPT ![0] = "GET"]
      /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, CState, 
                      MyTickets, id_, ip_, internalReq, id, ip_H, wantSeat, 
                      reply_, target, availSeats, ip, targetID, targetSeat, 
                      reply, scamsCount >>

GET == /\ pc[0] = "GET"
       /\ internalReq' = Head(Channels[ip_])
       /\ Channels' = [Channels EXCEPT ![ip_] = Tail(Channels[ip_])]
       /\ pc' = [pc EXCEPT ![0] = "TREAT"]
       /\ UNCHANGED << BankAccount, seatMap, Tickets, CState, MyTickets, id_, 
                       ip_, id, ip_H, wantSeat, reply_, target, availSeats, ip, 
                       targetID, targetSeat, reply, scamsCount >>

TREAT == /\ pc[0] = "TREAT"
         /\ IF internalReq.type = "buy"
               THEN /\ IF seatMap[internalReq.seat] = "available"
                          /\ internalReq.bankID \in AllHonest
                          /\ internalReq.password = Password[internalReq.bankID]
                          /\ BankAccount[internalReq.bankID] > 0
                          THEN /\ seatMap' = [seatMap EXCEPT ![internalReq.seat] = "paid"]
                               /\ BankAccount' = [BankAccount EXCEPT
                                                    ![internalReq.bankID] = @ - 1,
                                                    ![0] = @ + 1]
                               /\ Tickets' = [Tickets EXCEPT
                                                ![internalReq.bankID] = @ \union {internalReq.seat}]
                               /\ Channels' = [Channels EXCEPT ![internalReq.from] = Append(Channels[internalReq.from],
                                                                                            [type |-> "confirm",
                                                                                             from |-> 0,
                                                                                             seat |-> internalReq.seat,
                                                                                             bankID |-> -2,
                                                                                             password |-> 0])]
                          ELSE /\ Channels' = [Channels EXCEPT ![internalReq.from] = Append(Channels[internalReq.from],
                                                                                            [type |-> "deny",
                                                                                             from |-> 0,
                                                                                             seat |-> internalReq.seat,
                                                                                             bankID |-> -2,
                                                                                             password |-> 0])]
                               /\ UNCHANGED << BankAccount, seatMap, Tickets >>
               ELSE /\ TRUE
                    /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets >>
         /\ pc' = [pc EXCEPT ![0] = "s1_"]
         /\ UNCHANGED << CState, MyTickets, id_, ip_, internalReq, id, ip_H, 
                         wantSeat, reply_, target, availSeats, ip, targetID, 
                         targetSeat, reply, scamsCount >>

Done__ == /\ pc[0] = "Done__"
          /\ TRUE
          /\ pc' = [pc EXCEPT ![0] = "Done__"]
          /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, CState, 
                          MyTickets, id_, ip_, internalReq, id, ip_H, wantSeat, 
                          reply_, target, availSeats, ip, targetID, targetSeat, 
                          reply, scamsCount >>

Server == s1_ \/ WW \/ GET \/ TREAT \/ Done__

InitTarget(self) == /\ pc[self] = "InitTarget"
                    /\ target' = [target EXCEPT ![self] = CHOOSE k \in 0..Min2(INITMONEY, NUMSEATS) : TRUE]
                    /\ pc' = [pc EXCEPT ![self] = "s1"]
                    /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, 
                                    CState, MyTickets, id_, ip_, internalReq, 
                                    id, ip_H, wantSeat, reply_, availSeats, ip, 
                                    targetID, targetSeat, reply, scamsCount >>

s1(self) == /\ pc[self] = "s1"
            /\ IF CState[self] # "done"
                  THEN /\ pc' = [pc EXCEPT ![self] = "CheckDone"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done_"]
            /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, CState, 
                            MyTickets, id_, ip_, internalReq, id, ip_H, 
                            wantSeat, reply_, target, availSeats, ip, targetID, 
                            targetSeat, reply, scamsCount >>

CheckDone(self) == /\ pc[self] = "CheckDone"
                   /\ IF Cardinality(Tickets[self]) >= target[self]
                         \/ (\A s \in Seats : seatMap[s] = "paid")
                         THEN /\ CState' = [CState EXCEPT ![self] = "done"]
                              /\ pc' = [pc EXCEPT ![self] = "s1"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "BWaitIdle"]
                              /\ UNCHANGED CState
                   /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, 
                                   MyTickets, id_, ip_, internalReq, id, ip_H, 
                                   wantSeat, reply_, target, availSeats, ip, 
                                   targetID, targetSeat, reply, scamsCount >>

BWaitIdle(self) == /\ pc[self] = "BWaitIdle"
                   /\ (CState[self] = "idle")
                   /\ pc' = [pc EXCEPT ![self] = "BSend"]
                   /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, 
                                   CState, MyTickets, id_, ip_, internalReq, 
                                   id, ip_H, wantSeat, reply_, target, 
                                   availSeats, ip, targetID, targetSeat, reply, 
                                   scamsCount >>

BSend(self) == /\ pc[self] = "BSend"
               /\ CState' = [CState EXCEPT ![self] = "waiting"]
               /\ availSeats' = [availSeats EXCEPT ![self] = {s \in Seats : seatMap[s] = "available"}]
               /\ wantSeat' = [wantSeat EXCEPT ![self] = CHOOSE s \in availSeats'[self] : TRUE]
               /\ Channels' = [Channels EXCEPT ![0] = Append(Channels[0],
                                                            [type |-> "buy",
                                                             from |-> ip_H[self],
                                                             seat |-> wantSeat'[self],
                                                             bankID |-> id[self],
                                                             password |-> Password[id[self]]])]
               /\ pc' = [pc EXCEPT ![self] = "BWaitReply"]
               /\ UNCHANGED << BankAccount, seatMap, Tickets, MyTickets, id_, 
                               ip_, internalReq, id, ip_H, reply_, target, ip, 
                               targetID, targetSeat, reply, scamsCount >>

BWaitReply(self) == /\ pc[self] = "BWaitReply"
                    /\ (Len(Channels[ip_H[self]]) > 0)
                    /\ reply_' = [reply_ EXCEPT ![self] = Head(Channels[ip_H[self]])]
                    /\ Channels' = [Channels EXCEPT ![ip_H[self]] = Tail(Channels[ip_H[self]])]
                    /\ pc' = [pc EXCEPT ![self] = "BUpdate"]
                    /\ UNCHANGED << BankAccount, seatMap, Tickets, CState, 
                                    MyTickets, id_, ip_, internalReq, id, ip_H, 
                                    wantSeat, target, availSeats, ip, targetID, 
                                    targetSeat, reply, scamsCount >>

BUpdate(self) == /\ pc[self] = "BUpdate"
                 /\ TRUE
                 /\ CState' = [CState EXCEPT ![self] = "idle"]
                 /\ pc' = [pc EXCEPT ![self] = "s1"]
                 /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, 
                                 MyTickets, id_, ip_, internalReq, id, ip_H, 
                                 wantSeat, reply_, target, availSeats, ip, 
                                 targetID, targetSeat, reply, scamsCount >>

Done_(self) == /\ pc[self] = "Done_"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done_"]
               /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, CState, 
                               MyTickets, id_, ip_, internalReq, id, ip_H, 
                               wantSeat, reply_, target, availSeats, ip, 
                               targetID, targetSeat, reply, scamsCount >>

HClient(self) == InitTarget(self) \/ s1(self) \/ CheckDone(self)
                    \/ BWaitIdle(self) \/ BSend(self) \/ BWaitReply(self)
                    \/ BUpdate(self) \/ Done_(self)

MStep(self) == /\ pc[self] = "MStep"
               /\ IF scamsCount[self] < 1 /\ ~AllDone
                     THEN /\ \E h \in AllHonest:
                               \E s \in {seat \in Seats : seatMap[seat] = "available"}:
                                 /\ targetID' = [targetID EXCEPT ![self] = h]
                                 /\ targetSeat' = [targetSeat EXCEPT ![self] = s]
                          /\ pc' = [pc EXCEPT ![self] = "MSend"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ UNCHANGED << targetID, targetSeat >>
               /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, CState, 
                               MyTickets, id_, ip_, internalReq, id, ip_H, 
                               wantSeat, reply_, target, availSeats, ip, reply, 
                               scamsCount >>

MSend(self) == /\ pc[self] = "MSend"
               /\ Channels' = [Channels EXCEPT ![0] = Append(Channels[0], [type |-> "buy", from |-> ip[self],
                                                                            seat |-> targetSeat[self], bankID |-> targetID[self],
                                                                            password |-> Password[self]])]
               /\ scamsCount' = [scamsCount EXCEPT ![self] = scamsCount[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "MGetReply"]
               /\ UNCHANGED << BankAccount, seatMap, Tickets, CState, 
                               MyTickets, id_, ip_, internalReq, id, ip_H, 
                               wantSeat, reply_, target, availSeats, ip, 
                               targetID, targetSeat, reply >>

MGetReply(self) == /\ pc[self] = "MGetReply"
                   /\ (Len(Channels[ip[self]]) > 0)
                   /\ reply' = [reply EXCEPT ![self] = Head(Channels[ip[self]])]
                   /\ Channels' = [Channels EXCEPT ![ip[self]] = Tail(Channels[ip[self]])]
                   /\ pc' = [pc EXCEPT ![self] = "MStore"]
                   /\ UNCHANGED << BankAccount, seatMap, Tickets, CState, 
                                   MyTickets, id_, ip_, internalReq, id, ip_H, 
                                   wantSeat, reply_, target, availSeats, ip, 
                                   targetID, targetSeat, scamsCount >>

MStore(self) == /\ pc[self] = "MStore"
                /\ IF reply[self].type = "confirm"
                      THEN /\ MyTickets' = [MyTickets EXCEPT ![self] = MyTickets[self] \cup {reply[self].seat}]
                      ELSE /\ TRUE
                           /\ UNCHANGED MyTickets
                /\ pc' = [pc EXCEPT ![self] = "MStep"]
                /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, 
                                CState, id_, ip_, internalReq, id, ip_H, 
                                wantSeat, reply_, target, availSeats, ip, 
                                targetID, targetSeat, reply, scamsCount >>

MClient(self) == MStep(self) \/ MSend(self) \/ MGetReply(self)
                    \/ MStore(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Server
           \/ (\E self \in AllHonest: HClient(self))
           \/ (\E self \in AllMalicious: MClient(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Server)
        /\ \A self \in AllHonest : WF_vars(HClient(self))
        /\ \A self \in AllMalicious : WF_vars(MClient(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=================================================================================================
