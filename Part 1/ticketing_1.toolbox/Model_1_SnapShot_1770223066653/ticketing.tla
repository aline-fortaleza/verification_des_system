----------------------------- MODULE ticketing -----------------------------
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
        
        getFlag = 0; 

    define {

        AllMalicious == IF MALICIOUS THEN {-1} ELSE {}
        AllHonest == {i \in 1..NUMCLIENTS : TRUE}
        AllClients == AllHonest \union AllMalicious
        AllParticipants == AllClients \union {0}

        Seats == 1..NUMSEATS
        SeatStates == {"available", "paid"}

        IPs == Nat
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
            
        \* Intencionalmente FALSA: quebra logo após o 1º buy ser enviado ao servidor
        BadInv_NoRequestsToServer ==
            getFlag = 0
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
            test: getFlag := 1;
            WW:
            getFlag := 1;
            await Len(Channels[0]) > 0;

            GET:
            internalReq := Head(Channels[0]);
            Channels[ip] := Tail(Channels[0]);

            TREAT:
            if (internalReq.type = "buy") {

                if ( seatMap[internalReq.seat] = "available"
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
                                bankID |-> -2]);
                } else {
                    Channels[internalReq.from] :=
                        Append(Channels[internalReq.from],
                               [type |-> "deny",
                                from |-> 0,
                                seat |-> internalReq.seat,
                                bankID |-> -2]);
                }

            } else {
                skip; \* without cancel for now
            };
        };

\*        Done_:
\*        while (TRUE) { skip; }
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

                BSend:
                CState[self] := "waiting";

                
                availSeats := {s \in Seats : seatMap[s] = "available"};
                wantSeat := CHOOSE s \in availSeats : TRUE;

                Channels[0] := Append(Channels[0],
                                     [type |-> "buy",
                                      from |-> ip,
                                      seat |-> wantSeat,
                                      bankID |-> id]);

                BWaitReply:
                await (Len(Channels[ip]) > 0);

                BBuying:
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
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "428318bd" /\ chksum(tla) = "f6694d09")
\* Label s1 of process Server at line 93 col 13 changed to s1_
\* Process variable id of process Server at line 88 col 9 changed to id_
\* Process variable ip of process Server at line 89 col 9 changed to ip_
VARIABLES BankAccount, Channels, seatMap, Tickets, CState, getFlag, pc

(* define statement *)
AllMalicious == IF MALICIOUS THEN {-1} ELSE {}
AllHonest == {i \in 1..NUMCLIENTS : TRUE}
AllClients == AllHonest \union AllMalicious
AllParticipants == AllClients \union {0}

Seats == 1..NUMSEATS
SeatStates == {"available", "paid"}

IPs == Nat
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


BadInv_NoRequestsToServer ==
    getFlag = 0



AllDone ==
  /\ \A c \in AllHonest : CState[c] = "done"


Terminates == <>AllDone

VARIABLES id_, ip_, internalReq, id, ip, wantSeat, reply, target, availSeats

vars == << BankAccount, Channels, seatMap, Tickets, CState, getFlag, pc, id_, 
           ip_, internalReq, id, ip, wantSeat, reply, target, availSeats >>

ProcSet == {0} \cup (AllHonest)

Init == (* Global variables *)
        /\ BankAccount = [x \in AllParticipants |-> IF x = 0 THEN 0 ELSE INITMONEY]
        /\ Channels = [x \in AllParticipants |-> <<>>]
        /\ seatMap = [s \in 1..NUMSEATS |-> "available"]
        /\ Tickets = [c \in 1..NUMCLIENTS |-> {}]
        /\ CState = [c \in 1..NUMCLIENTS |-> "idle"]
        /\ getFlag = 0
        (* Process Server *)
        /\ id_ = 0
        /\ ip_ = 0
        /\ internalReq = M0
        (* Process HClient *)
        /\ id = [self \in AllHonest |-> self]
        /\ ip = [self \in AllHonest |-> self]
        /\ wantSeat = [self \in AllHonest |-> 1]
        /\ reply = [self \in AllHonest |-> M0]
        /\ target = [self \in AllHonest |-> 0]
        /\ availSeats = [self \in AllHonest |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "s1_"
                                        [] self \in AllHonest -> "InitTarget"]

s1_ == /\ pc[0] = "s1_"
       /\ pc' = [pc EXCEPT ![0] = "test"]
       /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, CState, 
                       getFlag, id_, ip_, internalReq, id, ip, wantSeat, reply, 
                       target, availSeats >>

test == /\ pc[0] = "test"
        /\ getFlag' = 1
        /\ pc' = [pc EXCEPT ![0] = "WW"]
        /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, CState, id_, 
                        ip_, internalReq, id, ip, wantSeat, reply, target, 
                        availSeats >>

WW == /\ pc[0] = "WW"
      /\ getFlag' = 1
      /\ Len(Channels[0]) > 0
      /\ pc' = [pc EXCEPT ![0] = "GET"]
      /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, CState, id_, 
                      ip_, internalReq, id, ip, wantSeat, reply, target, 
                      availSeats >>

GET == /\ pc[0] = "GET"
       /\ internalReq' = Head(Channels[0])
       /\ Channels' = [Channels EXCEPT ![ip_] = Tail(Channels[0])]
       /\ pc' = [pc EXCEPT ![0] = "TREAT"]
       /\ UNCHANGED << BankAccount, seatMap, Tickets, CState, getFlag, id_, 
                       ip_, id, ip, wantSeat, reply, target, availSeats >>

TREAT == /\ pc[0] = "TREAT"
         /\ IF internalReq.type = "buy"
               THEN /\ IF seatMap[internalReq.seat] = "available"
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
                                                                                             bankID |-> -2])]
                          ELSE /\ Channels' = [Channels EXCEPT ![internalReq.from] = Append(Channels[internalReq.from],
                                                                                            [type |-> "deny",
                                                                                             from |-> 0,
                                                                                             seat |-> internalReq.seat,
                                                                                             bankID |-> -2])]
                               /\ UNCHANGED << BankAccount, seatMap, Tickets >>
               ELSE /\ TRUE
                    /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets >>
         /\ pc' = [pc EXCEPT ![0] = "s1_"]
         /\ UNCHANGED << CState, getFlag, id_, ip_, internalReq, id, ip, 
                         wantSeat, reply, target, availSeats >>

Server == s1_ \/ test \/ WW \/ GET \/ TREAT

InitTarget(self) == /\ pc[self] = "InitTarget"
                    /\ target' = [target EXCEPT ![self] = CHOOSE k \in 1..Min2(INITMONEY, NUMSEATS) : TRUE]
                    /\ pc' = [pc EXCEPT ![self] = "s1"]
                    /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, 
                                    CState, getFlag, id_, ip_, internalReq, id, 
                                    ip, wantSeat, reply, availSeats >>

s1(self) == /\ pc[self] = "s1"
            /\ IF CState[self] # "done"
                  THEN /\ pc' = [pc EXCEPT ![self] = "CheckDone"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done_"]
            /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, CState, 
                            getFlag, id_, ip_, internalReq, id, ip, wantSeat, 
                            reply, target, availSeats >>

CheckDone(self) == /\ pc[self] = "CheckDone"
                   /\ IF Cardinality(Tickets[self]) >= target[self]
                         \/ (\A s \in Seats : seatMap[s] = "paid")
                         THEN /\ CState' = [CState EXCEPT ![self] = "done"]
                              /\ pc' = [pc EXCEPT ![self] = "s1"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "BWaitIdle"]
                              /\ UNCHANGED CState
                   /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, 
                                   getFlag, id_, ip_, internalReq, id, ip, 
                                   wantSeat, reply, target, availSeats >>

BWaitIdle(self) == /\ pc[self] = "BWaitIdle"
                   /\ (CState[self] = "idle")
                   /\ pc' = [pc EXCEPT ![self] = "BSend"]
                   /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, 
                                   CState, getFlag, id_, ip_, internalReq, id, 
                                   ip, wantSeat, reply, target, availSeats >>

BSend(self) == /\ pc[self] = "BSend"
               /\ CState' = [CState EXCEPT ![self] = "waiting"]
               /\ availSeats' = [availSeats EXCEPT ![self] = {s \in Seats : seatMap[s] = "available"}]
               /\ wantSeat' = [wantSeat EXCEPT ![self] = CHOOSE s \in availSeats'[self] : TRUE]
               /\ Channels' = [Channels EXCEPT ![0] = Append(Channels[0],
                                                            [type |-> "buy",
                                                             from |-> ip[self],
                                                             seat |-> wantSeat'[self],
                                                             bankID |-> id[self]])]
               /\ pc' = [pc EXCEPT ![self] = "BWaitReply"]
               /\ UNCHANGED << BankAccount, seatMap, Tickets, getFlag, id_, 
                               ip_, internalReq, id, ip, reply, target >>

BWaitReply(self) == /\ pc[self] = "BWaitReply"
                    /\ (Len(Channels[ip[self]]) > 0)
                    /\ pc' = [pc EXCEPT ![self] = "BBuying"]
                    /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, 
                                    CState, getFlag, id_, ip_, internalReq, id, 
                                    ip, wantSeat, reply, target, availSeats >>

BBuying(self) == /\ pc[self] = "BBuying"
                 /\ reply' = [reply EXCEPT ![self] = Head(Channels[ip[self]])]
                 /\ Channels' = [Channels EXCEPT ![ip[self]] = Tail(Channels[ip[self]])]
                 /\ pc' = [pc EXCEPT ![self] = "BUpdate"]
                 /\ UNCHANGED << BankAccount, seatMap, Tickets, CState, 
                                 getFlag, id_, ip_, internalReq, id, ip, 
                                 wantSeat, target, availSeats >>

BUpdate(self) == /\ pc[self] = "BUpdate"
                 /\ TRUE
                 /\ CState' = [CState EXCEPT ![self] = "idle"]
                 /\ pc' = [pc EXCEPT ![self] = "s1"]
                 /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, 
                                 getFlag, id_, ip_, internalReq, id, ip, 
                                 wantSeat, reply, target, availSeats >>

Done_(self) == /\ pc[self] = "Done_"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done_"]
               /\ UNCHANGED << BankAccount, Channels, seatMap, Tickets, CState, 
                               getFlag, id_, ip_, internalReq, id, ip, 
                               wantSeat, reply, target, availSeats >>

HClient(self) == InitTarget(self) \/ s1(self) \/ CheckDone(self)
                    \/ BWaitIdle(self) \/ BSend(self) \/ BWaitReply(self)
                    \/ BBuying(self) \/ BUpdate(self) \/ Done_(self)

Next == Server
           \/ (\E self \in AllHonest: HClient(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Server)
        /\ \A self \in AllHonest : WF_vars(HClient(self))

\* END TRANSLATION 


=================================================================================================
