----------------------------- MODULE tickets -----------------------------
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
        

    define {

        AllMalicious == IF MALICIOUS THEN {-1} ELSE {}
        AllHonest == {i \in 1..NUMCLIENTS : TRUE}
        AllClients == AllHonest \union AllMalicious
        AllParticipants == AllClients \union {0}

        Seats == 1..NUMSEATS
        SeatStates == {"available", "paid"}

        IPs == Nat \union {-1}
        TransactionType == {"buy", "cancel", "confirm", "deny"}
        bankIDType == AllParticipants \union {-2}

        MessageType == [type : TransactionType,
                        from : IPs,
                        seat : Seats,
                        bankID : bankIDType]

        M0 == [type |-> "buy",
               from |-> 0,
               seat |-> 0,
               bankID |-> 0]

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
            
            

         \*-----------------------------
        \* Stop condition
        \* -----------------------------
        AllDone ==
          /\ \A c \in AllHonest : CState[c] = "done"
\*          /\ \A p \in AllParticipants : Len(Channels[p]) = 0

        Terminates == <>AllDone
    }

    fair process (Server = 0)
    variables
        id = 0;
        ip = 0;
        internalReq = M0;
        
    {   
        s1: while (TRUE) {
            WW:
            await Len(Channels[0]) > 0;
            

            GET:
            internalReq := Head(Channels[0]);
            Channels[ip] := Tail(Channels[0]);
         
            
            TREAT:
            if (internalReq.type = "buy") {

                if ( seatMap[internalReq.seat] = "available"
                     /\ BankAccount[internalReq.bankID] > 0) {

                    
                    seatMap[internalReq.seat] := "paid";

                    BankAccount := [BankAccount EXCEPT ![internalReq.bankID] = BankAccount[internalReq.bankID] - 1,
                                                       ![0] = BankAccount[0] + 1];

                    Tickets := [Tickets EXCEPT
                                  ![internalReq.bankID] = @ \union {internalReq.seat}];

                    Channels[internalReq.from] :=
                        Append(Channels[internalReq.from],
                               [type |-> "confirm",
                                from |-> 0,
                                seat |-> internalReq.seat,
                                bankID |-> -2]);
                } else {
                    Channels[internalReq.from] :=
                        Append(Channels[internalReq.from],
                               [type |-> "deny",
                                from |-> 0,
                                seat |-> internalReq.seat,
                                bankID |-> -2]);

                }

            } else if (internalReq.type = "cancel") {
                if (seatMap[internalReq.seat] = "paid") {
                    seatMap[internalReq.seat] := "available";
                    BankAccount := [BankAccount EXCEPT ![internalReq.bankID] = BankAccount[internalReq.bankID] + 1,
                                                       ![0] = BankAccount[0] - 1];
                                                       
                    Tickets := [Tickets EXCEPT
                        ![internalReq.bankID] = @ \ {internalReq.seat}];
                    Channels[internalReq.from] := Append(Channels[internalReq.from], 
                                                 [type |-> "confirm", 
                                                  from |-> 0, 
                                                  seat |-> internalReq.seat, 
                                                  bankID |-> -2]);
                } else {
                    Channels[internalReq.from] := Append(Channels[internalReq.from], 
                                                 [type |-> "deny", 
                                                  from |-> 0, 
                                                  seat |-> internalReq.seat, 
                                                  bankID |-> -2]);
                }
            }
        };
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
        target := CHOOSE k \in 1..Min2(INITMONEY, NUMSEATS) : TRUE;

        s1: while (CState[self] # "done") {

            CheckDone:
            if (Cardinality(Tickets[self]) >= target
                \/ (\A s \in Seats : seatMap[s] = "paid")) {
                CState[self] := "done";
            } else {

                BWaitIdle:
                await (CState[self] = "idle");

                ActionChoice:
                either {
                    
                    BSendBuy:
                    CState[self] := "waiting";
                    
                    availSeats := {s \in Seats : seatMap[s] = "available"};
                    if (availSeats # {}) {
                        wantSeat := CHOOSE s \in availSeats : TRUE;
                        Channels[0] := Append(Channels[0],
                                             [type |-> "buy",
                                              from |-> ip,
                                              seat |-> wantSeat,
                                              bankID |-> id]);
                                              
                                                          
                    } else {
                        BNoSeats:           
                        CState[self] := "idle";
                        goto CheckDone;
                    };
                }
                or {
                    BCancel:
                    if (Tickets[self] = {}){
                        BNoTicketsToCancel:
                        CState[self] := "idle";
                        goto BSendBuy;
                    }
                    else {
                        BSendCancel:
                        await Tickets[self] # {};
                        CState[self] := "waiting";
                        
                        wantSeat := CHOOSE s \in Tickets[self] : TRUE;
                        Channels[0] := Append(Channels[0],
                                             [type |-> "cancel",
                                              from |-> ip,
                                              seat |-> wantSeat,
                                              bankID |-> id]);
                     }                     
                };

                BWaitReply:
                await (Len(Channels[ip]) > 0);

                BProcessing:
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
            id = self;
            ip = self;
            targetSeat = 0;
        {
            M1: while (TRUE) {
                \* Look for a seat that an honest client has paid for
                await \E s \in Seats : seatMap[s] = "paid";
                
                FindTarget:
                targetSeat := CHOOSE s \in Seats : seatMap[s] = "paid";
                
                \* Attack: Send a cancel request for someone else's seat
                MExploit:
                Channels[0] := Append(Channels[0],
                                     [type |-> "cancel",
                                      from |-> ip,
                                      seat |-> targetSeat,
                                      bankID |-> id]);
                
                MWait:
                await Len(Channels[ip]) > 0;
                
                MDiscard:
                Channels[ip] := Tail(Channels[ip]);
            }
        }
        
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "76a148d9" /\ chksum(tla) = "76fee4de")
\* Label s1 of process Server at line 93 col 13 changed to s1_
\* Process variable id of process Server at line 88 col 9 changed to id_
\* Process variable ip of process Server at line 89 col 9 changed to ip_
\* Process variable id of process HClient at line 161 col 9 changed to id_H
\* Process variable ip of process HClient at line 162 col 9 changed to ip_H
VARIABLES BankAccount, Channels, seatMap, Tickets, CState, Flag, pc

(* define statement *)
AllMalicious == IF MALICIOUS THEN {-1} ELSE {}
AllHonest == {i \in 1..NUMCLIENTS : TRUE}
AllClients == AllHonest \union AllMalicious
AllParticipants == AllClients \union {0}

Seats == 1..NUMSEATS
SeatStates == {"available", "paid"}

IPs == Nat \union {-1}
TransactionType == {"buy", "cancel", "confirm", "deny"}
bankIDType == AllParticipants \union {-2}

MessageType == [type : TransactionType,
                from : IPs,
                seat : Seats,
                bankID : bankIDType]

M0 == [type |-> "buy",
       from |-> 0,
       seat |-> 0,
       bankID |-> 0]

Money(p) == BankAccount[p]





TypeOK ==
  /\ BankAccount \in [AllParticipants -> Int]
  /\ Channels \in [AllParticipants -> Seq(MessageType)]
  /\ seatMap \in [Seats -> SeatStates]
  /\ Tickets \in [AllHonest -> SUBSET Seats]
  /\ CState \in [AllHonest -> {"idle","waiting","done"}]

MoneyTicketsInv ==
  \A c \in AllHonest :
    BankAccount[c] + Cardinality(Tickets[c]) = INITMONEY


TicketsPaidInv ==
  \A c \in AllHonest :
    \A s \in Tickets[c] : seatMap[s] = "paid"


NoDoubleSell ==
  \A s \in Seats :
    Cardinality({c \in AllHonest : s \in Tickets[c]}) <= 1

Inv == Flag = 0





AllDone ==
  /\ \A c \in AllHonest : CState[c] = "done"


Terminates == <>AllDone

VARIABLES id_, ip_, internalReq, id_H, ip_H, wantSeat, reply, target, 
          availSeats, id, ip, targetSeat

vars == << BankAccount, Channels, seatMap, Tickets, CState, Flag, pc, id_, 
           ip_, internalReq, id_H, ip_H, wantSeat, reply, target, availSeats, 
           id, ip, targetSeat >>

ProcSet == {0} \cup (AllHonest) \cup (AllMalicious)

Init == (* Global variables *)
        /\ BankAccount = [x \in AllParticipants |-> IF x = 0 THEN 0 ELSE INITMONEY]
        /\ Channels = [x \in AllParticipants |-> <<>>]
        /\ seatMap = [s \in 1..NUMSEATS |-> "available"]
        /\ Tickets = [c \in 1..NUMCLIENTS |-> {}]
        /\ CState = [c \in 1..NUMCLIENTS |-> "idle"]
        /\ Flag = 0
        (* Process Server *)
        /\ id_ = 0
        /\ ip_ = 0
        /\ internalReq = M0
        (* Process HClient *)
        /\ id_H = [self \in AllHonest |-> self]
        /\ ip_H = [self \in AllHonest |-> self]
        /\ wantSeat = [self \in AllHonest |-> 1]
        /\ reply = [self \in AllHonest |-> M0]
        /\ target = [self \in AllHonest |-> 0]
        /\ availSeats = [self \in AllHonest |-> {}]
        (* Process MClient *)
        /\ id = [self \in AllMalicious |-> self]
        /\ ip = [self \in AllMalicious |-> self]
        /\ targetSeat = [self \in AllMalicious |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "s1_"
                                        [] self \in AllHonest -> "InitTarget"
                                        [] self \in AllMalicious -> "M1"]

s1_ == /\ pc[0] = "s1_"
       /\ pc' = [pc EXCEPT ![0] = "WW"]
       /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, CState, Flag, 
                       id_, ip_, internalReq, id_H, ip_H, wantSeat, reply, 
                       target, availSeats, id, ip, targetSeat >>

WW == /\ pc[0] = "WW"
      /\ Len(Channels[0]) > 0
      /\ pc' = [pc EXCEPT ![0] = "GET"]
      /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, CState, Flag, 
                      id_, ip_, internalReq, id_H, ip_H, wantSeat, reply, 
                      target, availSeats, id, ip, targetSeat >>

GET == /\ pc[0] = "GET"
       /\ internalReq' = Head(Channels[0])
       /\ Channels' = [Channels EXCEPT ![ip_] = Tail(Channels[0])]
       /\ pc' = [pc EXCEPT ![0] = "TREAT"]
       /\ UNCHANGED << BankAccount, seatMap, Tickets, CState, Flag, id_, ip_, 
                       id_H, ip_H, wantSeat, reply, target, availSeats, id, ip, 
                       targetSeat >>

TREAT == /\ pc[0] = "TREAT"
         /\ IF internalReq.type = "buy"
               THEN /\ IF seatMap[internalReq.seat] = "available"
                          /\ BankAccount[internalReq.bankID] > 0
                          THEN /\ seatMap' = [seatMap EXCEPT ![internalReq.seat] = "paid"]
                               /\ BankAccount' = [BankAccount EXCEPT ![internalReq.bankID] = BankAccount[internalReq.bankID] - 1,
                                                                     ![0] = BankAccount[0] + 1]
                               /\ Tickets' = [Tickets EXCEPT
                                                ![internalReq.bankID] = @ \union {internalReq.seat}]
                               /\ Channels' = [Channels EXCEPT ![internalReq.from] = Append(Channels[internalReq.from],
                                                                                            [type |-> "confirm",
                                                                                             from |-> 0,
                                                                                             seat |-> internalReq.seat,
                                                                                             bankID |-> -2])]
                          ELSE /\ Channels' = [Channels EXCEPT ![internalReq.from] = Append(Channels[internalReq.from],
                                                                                            [type |-> "deny",
                                                                                             from |-> 0,
                                                                                             seat |-> internalReq.seat,
                                                                                             bankID |-> -2])]
                               /\ UNCHANGED << BankAccount, seatMap, Tickets >>
                    /\ Flag' = Flag
               ELSE /\ IF internalReq.type = "cancel"
                          THEN /\ Flag' = 1
                               /\ IF seatMap[internalReq.seat] = "paid"
                                     THEN /\ seatMap' = [seatMap EXCEPT ![internalReq.seat] = "available"]
                                          /\ BankAccount' = [BankAccount EXCEPT ![internalReq.bankID] = BankAccount[internalReq.bankID] + 1,
                                                                                ![0] = BankAccount[0] - 1]
                                          /\ Tickets' =        [Tickets EXCEPT
                                                        ![internalReq.bankID] = @ \ {internalReq.seat}]
                                          /\ Channels' = [Channels EXCEPT ![internalReq.from] =  Append(Channels[internalReq.from],
                                                                                                [type |-> "confirm",
                                                                                                 from |-> 0,
                                                                                                 seat |-> internalReq.seat,
                                                                                                 bankID |-> -2])]
                                     ELSE /\ Channels' = [Channels EXCEPT ![internalReq.from] =  Append(Channels[internalReq.from],
                                                                                                [type |-> "deny",
                                                                                                 from |-> 0,
                                                                                                 seat |-> internalReq.seat,
                                                                                                 bankID |-> -2])]
                                          /\ UNCHANGED << BankAccount, seatMap, 
                                                          Tickets >>
                          ELSE /\ TRUE
                               /\ UNCHANGED << BankAccount, Channels, seatMap, 
                                               Tickets, Flag >>
         /\ pc' = [pc EXCEPT ![0] = "s1_"]
         /\ UNCHANGED << CState, id_, ip_, internalReq, id_H, ip_H, wantSeat, 
                         reply, target, availSeats, id, ip, targetSeat >>

Server == s1_ \/ WW \/ GET \/ TREAT

InitTarget(self) == /\ pc[self] = "InitTarget"
                    /\ target' = [target EXCEPT ![self] = CHOOSE k \in 1..Min2(INITMONEY, NUMSEATS) : TRUE]
                    /\ pc' = [pc EXCEPT ![self] = "s1"]
                    /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, 
                                    CState, Flag, id_, ip_, internalReq, id_H, 
                                    ip_H, wantSeat, reply, availSeats, id, ip, 
                                    targetSeat >>

s1(self) == /\ pc[self] = "s1"
            /\ IF CState[self] # "done"
                  THEN /\ pc' = [pc EXCEPT ![self] = "CheckDone"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done_"]
            /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, CState, 
                            Flag, id_, ip_, internalReq, id_H, ip_H, wantSeat, 
                            reply, target, availSeats, id, ip, targetSeat >>

CheckDone(self) == /\ pc[self] = "CheckDone"
                   /\ IF Cardinality(Tickets[self]) >= target[self]
                         \/ (\A s \in Seats : seatMap[s] = "paid")
                         THEN /\ CState' = [CState EXCEPT ![self] = "done"]
                              /\ pc' = [pc EXCEPT ![self] = "s1"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "BWaitIdle"]
                              /\ UNCHANGED CState
                   /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, 
                                   Flag, id_, ip_, internalReq, id_H, ip_H, 
                                   wantSeat, reply, target, availSeats, id, ip, 
                                   targetSeat >>

BWaitIdle(self) == /\ pc[self] = "BWaitIdle"
                   /\ (CState[self] = "idle")
                   /\ pc' = [pc EXCEPT ![self] = "ActionChoice"]
                   /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, 
                                   CState, Flag, id_, ip_, internalReq, id_H, 
                                   ip_H, wantSeat, reply, target, availSeats, 
                                   id, ip, targetSeat >>

ActionChoice(self) == /\ pc[self] = "ActionChoice"
                      /\ \/ /\ pc' = [pc EXCEPT ![self] = "BSendBuy"]
                         \/ /\ pc' = [pc EXCEPT ![self] = "BCancel"]
                      /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, 
                                      CState, Flag, id_, ip_, internalReq, 
                                      id_H, ip_H, wantSeat, reply, target, 
                                      availSeats, id, ip, targetSeat >>

BSendBuy(self) == /\ pc[self] = "BSendBuy"
                  /\ CState' = [CState EXCEPT ![self] = "waiting"]
                  /\ availSeats' = [availSeats EXCEPT ![self] = {s \in Seats : seatMap[s] = "available"}]
                  /\ IF availSeats'[self] # {}
                        THEN /\ wantSeat' = [wantSeat EXCEPT ![self] = CHOOSE s \in availSeats'[self] : TRUE]
                             /\ Channels' = [Channels EXCEPT ![0] = Append(Channels[0],
                                                                          [type |-> "buy",
                                                                           from |-> ip_H[self],
                                                                           seat |-> wantSeat'[self],
                                                                           bankID |-> id_H[self]])]
                             /\ pc' = [pc EXCEPT ![self] = "BWaitReply"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "BNoSeats"]
                             /\ UNCHANGED << Channels, wantSeat >>
                  /\ UNCHANGED << BankAccount, seatMap, Tickets, Flag, id_, 
                                  ip_, internalReq, id_H, ip_H, reply, target, 
                                  id, ip, targetSeat >>

BNoSeats(self) == /\ pc[self] = "BNoSeats"
                  /\ CState' = [CState EXCEPT ![self] = "idle"]
                  /\ pc' = [pc EXCEPT ![self] = "CheckDone"]
                  /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, 
                                  Flag, id_, ip_, internalReq, id_H, ip_H, 
                                  wantSeat, reply, target, availSeats, id, ip, 
                                  targetSeat >>

BCancel(self) == /\ pc[self] = "BCancel"
                 /\ IF Tickets[self] = {}
                       THEN /\ pc' = [pc EXCEPT ![self] = "BNoTicketsToCancel"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "BSendCancel"]
                 /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, 
                                 CState, Flag, id_, ip_, internalReq, id_H, 
                                 ip_H, wantSeat, reply, target, availSeats, id, 
                                 ip, targetSeat >>

BNoTicketsToCancel(self) == /\ pc[self] = "BNoTicketsToCancel"
                            /\ CState' = [CState EXCEPT ![self] = "idle"]
                            /\ pc' = [pc EXCEPT ![self] = "BSendBuy"]
                            /\ UNCHANGED << BankAccount, Channels, seatMap, 
                                            Tickets, Flag, id_, ip_, 
                                            internalReq, id_H, ip_H, wantSeat, 
                                            reply, target, availSeats, id, ip, 
                                            targetSeat >>

BSendCancel(self) == /\ pc[self] = "BSendCancel"
                     /\ Tickets[self] # {}
                     /\ CState' = [CState EXCEPT ![self] = "waiting"]
                     /\ wantSeat' = [wantSeat EXCEPT ![self] = CHOOSE s \in Tickets[self] : TRUE]
                     /\ Channels' = [Channels EXCEPT ![0] = Append(Channels[0],
                                                                  [type |-> "cancel",
                                                                   from |-> ip_H[self],
                                                                   seat |-> wantSeat'[self],
                                                                   bankID |-> id_H[self]])]
                     /\ pc' = [pc EXCEPT ![self] = "BWaitReply"]
                     /\ UNCHANGED << BankAccount, seatMap, Tickets, Flag, id_, 
                                     ip_, internalReq, id_H, ip_H, reply, 
                                     target, availSeats, id, ip, targetSeat >>

BWaitReply(self) == /\ pc[self] = "BWaitReply"
                    /\ (Len(Channels[ip_H[self]]) > 0)
                    /\ pc' = [pc EXCEPT ![self] = "BProcessing"]
                    /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, 
                                    CState, Flag, id_, ip_, internalReq, id_H, 
                                    ip_H, wantSeat, reply, target, availSeats, 
                                    id, ip, targetSeat >>

BProcessing(self) == /\ pc[self] = "BProcessing"
                     /\ reply' = [reply EXCEPT ![self] = Head(Channels[ip_H[self]])]
                     /\ Channels' = [Channels EXCEPT ![ip_H[self]] = Tail(Channels[ip_H[self]])]
                     /\ pc' = [pc EXCEPT ![self] = "BUpdate"]
                     /\ UNCHANGED << BankAccount, seatMap, Tickets, CState, 
                                     Flag, id_, ip_, internalReq, id_H, ip_H, 
                                     wantSeat, target, availSeats, id, ip, 
                                     targetSeat >>

BUpdate(self) == /\ pc[self] = "BUpdate"
                 /\ TRUE
                 /\ CState' = [CState EXCEPT ![self] = "idle"]
                 /\ pc' = [pc EXCEPT ![self] = "s1"]
                 /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, Flag, 
                                 id_, ip_, internalReq, id_H, ip_H, wantSeat, 
                                 reply, target, availSeats, id, ip, targetSeat >>

Done_(self) == /\ pc[self] = "Done_"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done_"]
               /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, CState, 
                               Flag, id_, ip_, internalReq, id_H, ip_H, 
                               wantSeat, reply, target, availSeats, id, ip, 
                               targetSeat >>

HClient(self) == InitTarget(self) \/ s1(self) \/ CheckDone(self)
                    \/ BWaitIdle(self) \/ ActionChoice(self)
                    \/ BSendBuy(self) \/ BNoSeats(self) \/ BCancel(self)
                    \/ BNoTicketsToCancel(self) \/ BSendCancel(self)
                    \/ BWaitReply(self) \/ BProcessing(self)
                    \/ BUpdate(self) \/ Done_(self)

M1(self) == /\ pc[self] = "M1"
            /\ \E s \in Seats : seatMap[s] = "paid"
            /\ pc' = [pc EXCEPT ![self] = "FindTarget"]
            /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, CState, 
                            Flag, id_, ip_, internalReq, id_H, ip_H, wantSeat, 
                            reply, target, availSeats, id, ip, targetSeat >>

FindTarget(self) == /\ pc[self] = "FindTarget"
                    /\ targetSeat' = [targetSeat EXCEPT ![self] = CHOOSE s \in Seats : seatMap[s] = "paid"]
                    /\ pc' = [pc EXCEPT ![self] = "MExploit"]
                    /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, 
                                    CState, Flag, id_, ip_, internalReq, id_H, 
                                    ip_H, wantSeat, reply, target, availSeats, 
                                    id, ip >>

MExploit(self) == /\ pc[self] = "MExploit"
                  /\ Channels' = [Channels EXCEPT ![0] = Append(Channels[0],
                                                               [type |-> "cancel",
                                                                from |-> ip[self],
                                                                seat |-> targetSeat[self],
                                                                bankID |-> id[self]])]
                  /\ pc' = [pc EXCEPT ![self] = "MWait"]
                  /\ UNCHANGED << BankAccount, seatMap, Tickets, CState, Flag, 
                                  id_, ip_, internalReq, id_H, ip_H, wantSeat, 
                                  reply, target, availSeats, id, ip, 
                                  targetSeat >>

MWait(self) == /\ pc[self] = "MWait"
               /\ Len(Channels[ip[self]]) > 0
               /\ pc' = [pc EXCEPT ![self] = "MDiscard"]
               /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, CState, 
                               Flag, id_, ip_, internalReq, id_H, ip_H, 
                               wantSeat, reply, target, availSeats, id, ip, 
                               targetSeat >>

MDiscard(self) == /\ pc[self] = "MDiscard"
                  /\ Channels' = [Channels EXCEPT ![ip[self]] = Tail(Channels[ip[self]])]
                  /\ pc' = [pc EXCEPT ![self] = "M1"]
                  /\ UNCHANGED << BankAccount, seatMap, Tickets, CState, Flag, 
                                  id_, ip_, internalReq, id_H, ip_H, wantSeat, 
                                  reply, target, availSeats, id, ip, 
                                  targetSeat >>

MClient(self) == M1(self) \/ FindTarget(self) \/ MExploit(self)
                    \/ MWait(self) \/ MDiscard(self)

Next == Server
           \/ (\E self \in AllHonest: HClient(self))
           \/ (\E self \in AllMalicious: MClient(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Server)
        /\ \A self \in AllHonest : WF_vars(HClient(self))
        /\ \A self \in AllMalicious : WF_vars(MClient(self))

\* END TRANSLATION 


=================================================================================================
