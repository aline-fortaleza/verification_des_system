----------------------------- MODULE ticketing -----------------------------
EXTENDS Integers, TLC, Sequences, FiniteSets

CONSTANTS NUMCLIENTS, MALICIOUS, NUMSEATS, INITMONEY

\* Min of two naturals/integers (TLA+ has no built-in Min(a,b) operator)
Min2(a, b) == IF a <= b THEN a ELSE b

(* --algorithm ticketing {
    variables
        BankAccount = [x \in AllParticipants |-> IF x = 0 THEN 0 ELSE INITMONEY];
        Channels = [x \in AllParticipants |-> <<>>]; \* Channels[ip] is the queue for messages TO ip

    define {

        AllMalicious == IF MALICIOUS THEN {-1} ELSE {}
        AllHonest == {i \in 1..NUMCLIENTS : TRUE}
        AllClients == AllHonest \union AllMalicious
        AllParticipants == AllClients \union {0} \* 0 is the server

        Seats == 1..NUMSEATS
        SeatStates == {"available", "paid"}
        seatMapType == [Seats -> SeatStates]

        IPs == Nat \* IP addresses are natural numbers
        TransactionType == {"buy", "cancel", "confirm", "deny"}
        bankIDType == AllParticipants \union {-2} \* -2 is for "not given"

        MessageType == [type : TransactionType,
                        from : IPs,
                        seat : Seats,
                        bankID : bankIDType]

        M0 == [type |-> "buy",
               from |-> 0,
               seat |-> 1,
               bankID |-> 0]

        Money(p) == BankAccount[p]

        \* -------- Invariants --------
        \* Create your invariants here

        \* -------- Temporal Properties --------
        \* Create meaningful temporal properties if possible
    }

    fair process (Server = 0) \* Server has process ID 0
    variables
        seatMap = [s \in Seats |-> "available"]; \* All seats start as available
        id = 0; \* Server's BankID
        ip = 0; \* Server's IP address
        internalReq = M0; \* Dummy var 
    {
        \* Inline "AllDone":
        \*   All clients done AND all channels empty
        s1: while (~( /\ \A c \in AllHonest : state[c] = "done"
                     /\ \A p \in AllParticipants : Len(Channels[p]) = 0)) {

            WW:
            await (Len(Channels[ip]) > 0);

            GET:
            internalReq := Head(Channels[ip]);
            Channels[ip] := Tail(Channels[ip]);

            TREAT:
            if (internalReq.type = "buy") {
                if (seatMap[internalReq.seat] = "available"
                    /\ BankAccount[internalReq.bankID] > 0) {

                    seatMap[internalReq.seat] := "paid";
                    BankAccount := [BankAccount EXCEPT
                                      ![internalReq.bankID] = BankAccount[internalReq.bankID] - 1,
                                      ![0] = BankAccount[0] + 1];

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
                skip; \* ignore cancel/other types in Part 1
            };
        };

        Done_:
        while (TRUE) { skip; }
    }

    fair process (HClient \in AllHonest)
    variables
        tickets = {};
        id = self; \* Client's BankID
        ip = self; \* Client's IP address
        state = "idle"; \* Client's state
        wantSeat = 1; \* Seat the client wants to buy
        reply = M0; \* Dummy var
        lastReqType = "buy";
        target = 0;
    {
        InitTarget:
        \* Each client picks how many tickets it wants (cannot exceed money or total seats)
        target := CHOOSE k \in 0..Min2(INITMONEY, NUMSEATS) : TRUE;

        s1: while (state # "done") {

            CheckDone:
            \* Inline "NoSeatLeft": all seats are paid
            if (Cardinality(tickets) >= target
                \/ (\A s \in Seats : seatMap[s] = "paid")) {
                state := "done";
            } else {

                BWaitIdle:
                await (state = "idle");

                BSend:
                state := "waiting";
                wantSeat := CHOOSE s \in Seats : TRUE;
                lastReqType := "buy";

                Channels[0] := Append(Channels[0],
                                     [type |-> "buy",
                                      from |-> ip,
                                      seat |-> wantSeat,
                                      bankID |-> id]);

                BWaitRead:
                await (Len(Channels[ip]) > 0);
                reply := Head(Channels[ip]);

                BPop:
                Channels[ip] := Tail(Channels[ip]);

                BUpdate:
                if (reply.type = "confirm") {
                    tickets := tickets \union {reply.seat};
                };
                state := "idle";
            };
        };

        ClientDone:
        while (TRUE) { skip; }
    }
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "610ff71e" /\ chksum(tla) = "3bc2bcaf")
\* Label s1 of process Server at line 57 col 13 changed to s1_
\* Process variable id of process Server at line 51 col 9 changed to id_
\* Process variable ip of process Server at line 52 col 9 changed to ip_
VARIABLES BankAccount, Channels, pc

(* define statement *)
AllMalicious == IF MALICIOUS THEN {-1} ELSE {}
AllHonest == {i \in 1..NUMCLIENTS : TRUE}
AllClients == AllHonest \union AllMalicious
AllParticipants == AllClients \union {0}

Seats == 1..NUMSEATS
SeatStates == {"available", "paid"}
seatMapType == [Seats -> SeatStates]

IPs == Nat
TransactionType == {"buy", "cancel", "confirm", "deny"}
bankIDType == AllParticipants \union {-2}

MessageType == [type : TransactionType,
                from : IPs,
                seat : Seats,
                bankID : bankIDType]

M0 == [type |-> "buy",
       from |-> 0,
       seat |-> 1,
       bankID |-> 0]

Money(p) == BankAccount[p]

VARIABLES seatMap, id_, ip_, internalReq, tickets, id, ip, state, wantSeat, 
          reply, lastReqType, target

vars == << BankAccount, Channels, pc, seatMap, id_, ip_, internalReq, tickets, 
           id, ip, state, wantSeat, reply, lastReqType, target >>

ProcSet == {0} \cup (AllHonest)

Init == (* Global variables *)
        /\ BankAccount = [x \in AllParticipants |-> IF x = 0 THEN 0 ELSE INITMONEY]
        /\ Channels = [x \in AllParticipants |-> <<>>]
        (* Process Server *)
        /\ seatMap = [s \in Seats |-> "available"]
        /\ id_ = 0
        /\ ip_ = 0
        /\ internalReq = M0
        (* Process HClient *)
        /\ tickets = [self \in AllHonest |-> {}]
        /\ id = [self \in AllHonest |-> self]
        /\ ip = [self \in AllHonest |-> self]
        /\ state = [self \in AllHonest |-> "idle"]
        /\ wantSeat = [self \in AllHonest |-> 1]
        /\ reply = [self \in AllHonest |-> M0]
        /\ lastReqType = [self \in AllHonest |-> "buy"]
        /\ target = [self \in AllHonest |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "s1_"
                                        [] self \in AllHonest -> "InitTarget"]

s1_ == /\ pc[0] = "s1_"
       /\ IF ~( /\ \A c \in AllHonest : state[0][c] = "done"
               /\ \A p \in AllParticipants : Len(Channels[p]) = 0)
             THEN /\ pc' = [pc EXCEPT ![0] = "WW"]
             ELSE /\ pc' = [pc EXCEPT ![0] = "Done_"]
       /\ UNCHANGED << BankAccount, Channels, seatMap, id_, ip_, internalReq, 
                       tickets, id, ip, state, wantSeat, reply, lastReqType, 
                       target >>

WW == /\ pc[0] = "WW"
      /\ (Len(Channels[ip_]) > 0)
      /\ pc' = [pc EXCEPT ![0] = "GET"]
      /\ UNCHANGED << BankAccount, Channels, seatMap, id_, ip_, internalReq, 
                      tickets, id, ip, state, wantSeat, reply, lastReqType, 
                      target >>

GET == /\ pc[0] = "GET"
       /\ internalReq' = Head(Channels[ip_])
       /\ Channels' = [Channels EXCEPT ![ip_] = Tail(Channels[ip_])]
       /\ pc' = [pc EXCEPT ![0] = "TREAT"]
       /\ UNCHANGED << BankAccount, seatMap, id_, ip_, tickets, id, ip, state, 
                       wantSeat, reply, lastReqType, target >>

TREAT == /\ pc[0] = "TREAT"
         /\ IF internalReq.type = "buy"
               THEN /\ IF seatMap[internalReq.seat] = "available"
                          /\ BankAccount[internalReq.bankID] > 0
                          THEN /\ seatMap' = [seatMap EXCEPT ![internalReq.seat] = "paid"]
                               /\ BankAccount' = [BankAccount EXCEPT
                                                    ![internalReq.bankID] = BankAccount[internalReq.bankID] - 1,
                                                    ![0] = BankAccount[0] + 1]
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
                               /\ UNCHANGED << BankAccount, seatMap >>
               ELSE /\ TRUE
                    /\ UNCHANGED << BankAccount, Channels, seatMap >>
         /\ pc' = [pc EXCEPT ![0] = "s1_"]
         /\ UNCHANGED << id_, ip_, internalReq, tickets, id, ip, state, 
                         wantSeat, reply, lastReqType, target >>

Done_ == /\ pc[0] = "Done_"
         /\ TRUE
         /\ pc' = [pc EXCEPT ![0] = "Done_"]
         /\ UNCHANGED << BankAccount, Channels, seatMap, id_, ip_, internalReq, 
                         tickets, id, ip, state, wantSeat, reply, lastReqType, 
                         target >>

Server == s1_ \/ WW \/ GET \/ TREAT \/ Done_

InitTarget(self) == /\ pc[self] = "InitTarget"
                    /\ target' = [target EXCEPT ![self] = CHOOSE k \in 0..Min2(INITMONEY, NUMSEATS) : TRUE]
                    /\ pc' = [pc EXCEPT ![self] = "s1"]
                    /\ UNCHANGED << BankAccount, Channels, seatMap, id_, ip_, 
                                    internalReq, tickets, id, ip, state, 
                                    wantSeat, reply, lastReqType >>

s1(self) == /\ pc[self] = "s1"
            /\ IF state[self] # "done"
                  THEN /\ pc' = [pc EXCEPT ![self] = "CheckDone"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "ClientDone"]
            /\ UNCHANGED << BankAccount, Channels, seatMap, id_, ip_, 
                            internalReq, tickets, id, ip, state, wantSeat, 
                            reply, lastReqType, target >>

CheckDone(self) == /\ pc[self] = "CheckDone"
                   /\ IF Cardinality(tickets[self]) >= target[self]
                         \/ (\A s \in Seats : seatMap[s] = "paid")
                         THEN /\ state' = [state EXCEPT ![self] = "done"]
                              /\ pc' = [pc EXCEPT ![self] = "s1"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "BWaitIdle"]
                              /\ state' = state
                   /\ UNCHANGED << BankAccount, Channels, seatMap, id_, ip_, 
                                   internalReq, tickets, id, ip, wantSeat, 
                                   reply, lastReqType, target >>

BWaitIdle(self) == /\ pc[self] = "BWaitIdle"
                   /\ (state[self] = "idle")
                   /\ pc' = [pc EXCEPT ![self] = "BSend"]
                   /\ UNCHANGED << BankAccount, Channels, seatMap, id_, ip_, 
                                   internalReq, tickets, id, ip, state, 
                                   wantSeat, reply, lastReqType, target >>

BSend(self) == /\ pc[self] = "BSend"
               /\ state' = [state EXCEPT ![self] = "waiting"]
               /\ wantSeat' = [wantSeat EXCEPT ![self] = CHOOSE s \in Seats : TRUE]
               /\ lastReqType' = [lastReqType EXCEPT ![self] = "buy"]
               /\ Channels' = [Channels EXCEPT ![0] = Append(Channels[0],
                                                            [type |-> "buy",
                                                             from |-> ip[self],
                                                             seat |-> wantSeat'[self],
                                                             bankID |-> id[self]])]
               /\ pc' = [pc EXCEPT ![self] = "BWaitRead"]
               /\ UNCHANGED << BankAccount, seatMap, id_, ip_, internalReq, 
                               tickets, id, ip, reply, target >>

BWaitRead(self) == /\ pc[self] = "BWaitRead"
                   /\ (Len(Channels[ip[self]]) > 0)
                   /\ reply' = [reply EXCEPT ![self] = Head(Channels[ip[self]])]
                   /\ pc' = [pc EXCEPT ![self] = "BPop"]
                   /\ UNCHANGED << BankAccount, Channels, seatMap, id_, ip_, 
                                   internalReq, tickets, id, ip, state, 
                                   wantSeat, lastReqType, target >>

BPop(self) == /\ pc[self] = "BPop"
              /\ Channels' = [Channels EXCEPT ![ip[self]] = Tail(Channels[ip[self]])]
              /\ pc' = [pc EXCEPT ![self] = "BUpdate"]
              /\ UNCHANGED << BankAccount, seatMap, id_, ip_, internalReq, 
                              tickets, id, ip, state, wantSeat, reply, 
                              lastReqType, target >>

BUpdate(self) == /\ pc[self] = "BUpdate"
                 /\ IF reply[self].type = "confirm"
                       THEN /\ tickets' = [tickets EXCEPT ![self] = tickets[self] \union {reply[self].seat}]
                       ELSE /\ TRUE
                            /\ UNCHANGED tickets
                 /\ state' = [state EXCEPT ![self] = "idle"]
                 /\ pc' = [pc EXCEPT ![self] = "s1"]
                 /\ UNCHANGED << BankAccount, Channels, seatMap, id_, ip_, 
                                 internalReq, id, ip, wantSeat, reply, 
                                 lastReqType, target >>

ClientDone(self) == /\ pc[self] = "ClientDone"
                    /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "ClientDone"]
                    /\ UNCHANGED << BankAccount, Channels, seatMap, id_, ip_, 
                                    internalReq, tickets, id, ip, state, 
                                    wantSeat, reply, lastReqType, target >>

HClient(self) == InitTarget(self) \/ s1(self) \/ CheckDone(self)
                    \/ BWaitIdle(self) \/ BSend(self) \/ BWaitRead(self)
                    \/ BPop(self) \/ BUpdate(self) \/ ClientDone(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Server
           \/ (\E self \in AllHonest: HClient(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Server)
        /\ \A self \in AllHonest : WF_vars(HClient(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
RECURSIVE SetSum(_)

SetSum(S) ==
  IF S = {}
  THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN  x + SetSum(S \ {x})

Clients == AllHonest

InitTotalMoney == Cardinality(AllHonest) * INITMONEY

TotalMoney == SetSum({ BankAccount[p] : p \in AllParticipants })


Inv_NoNegativeMoney ==
  \A c \in Clients : BankAccount[c] >= 0

Inv_TotalMoneyConserved ==
  TotalMoney = InitTotalMoney

Inv_TicketSeatsArePaid ==
  \A c \in Clients : \A s \in tickets[c] : seatMap[s] = "paid"


Inv_UniqueOwnership ==
  \A s \in Seats :
    Cardinality({ c \in Clients : s \in tickets[c] }) <= 1

Inv_NoMoreThanInitial ==
  \A c \in Clients : BankAccount[c] <= INITMONEY

Inv_TicketsSubsetSeats ==
  \A c \in Clients : tickets[c] \subseteq Seats

Invariants ==
  /\ Inv_NoNegativeMoney
  /\ Inv_TotalMoneyConserved
  /\ Inv_TicketSeatsArePaid
  /\ Inv_UniqueOwnership
  /\ Inv_NoMoreThanInitial
  /\ Inv_TicketsSubsetSeats
=============================================================================


