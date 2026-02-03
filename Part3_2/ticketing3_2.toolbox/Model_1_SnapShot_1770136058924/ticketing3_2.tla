----------------------------- MODULE ticketing3_2 -----------------------------
EXTENDS Integers, TLC, Sequences, FiniteSets

CONSTANTS NUMCLIENTS, MALICIOUS, NUMSEATS, INITMONEY

Min2(a, b) == IF a <= b THEN a ELSE b

(* --algorithm ticketing {
    variables
        BankAccount = [x \in AllParticipants |-> IF x = 0 THEN 0 ELSE INITMONEY];
        Channels    = [x \in AllParticipants |-> <<>>];

        seatMap     = [s \in 1..NUMSEATS |-> "available"];

        ResOwner    = [s \in Seats |-> -2];  \* reservation owner (-2 = nobody)

        Tickets     = [c \in 1..NUMCLIENTS |-> {}];

        CState      = [c \in 1..NUMCLIENTS |-> "idle"];

        MyTickets   = [m \in AllMalicious |-> {}];

        ipOf        = [c \in AllHonest |-> c];  \* server replies to ipOf[bankID]

    define {

        AllMalicious == IF MALICIOUS THEN {-1} ELSE {}
        AllHonest == {i \in 1..NUMCLIENTS : TRUE}
        AllClients == AllHonest \union AllMalicious
        AllParticipants == AllClients \union {0}

        \* secret per-client credential (assumed not known by the attacker)
        Password == [p \in AllParticipants |-> 2000 + p]

        Seats == 1..NUMSEATS
        SeatStates == {"available", "reserved", "paid"}

        IPs == Nat \union {-1}

        \* protocol messages (list/listResp removed)
        TransactionType ==
          {"reserve", "pay", "cancel", "updateIP", "confirm", "deny"}

        bankIDType == AllParticipants \union {-2}

        \* keep the 'seats' field to minimize refactoring (unused => always {})
        MessageType == [ type     : TransactionType,
                         from     : IPs,
                         seat     : Seats,
                         bankID   : bankIDType,
                         password : Nat,
                         seats    : SUBSET Seats ]

        \* dummy message (seats always empty)
        M0 == [ type |-> "reserve",
                from |-> 0,
                seat |-> 1,
                bankID |-> 0,
                password |-> 0,
                seats |-> {} ]

        Money(p) == BankAccount[p]

        \* -----------------------------
        \* Invariants / typing
        \* -----------------------------
        TypeOK ==
          /\ BankAccount \in [AllParticipants -> Int]
          /\ Channels \in [AllParticipants -> Seq(MessageType)]
          /\ seatMap \in [Seats -> SeatStates]
          /\ ResOwner \in [Seats -> (AllHonest \cup {-2})]
          /\ Tickets \in [AllHonest -> SUBSET Seats]
          /\ CState \in [AllHonest -> {"idle","waiting","done"}]
          /\ MyTickets \in [AllMalicious -> SUBSET Seats]
          /\ ipOf \in [AllHonest -> IPs]

        MoneyTicketsInv ==
          \A c \in AllHonest :
            BankAccount[c] + Cardinality(Tickets[c]) = INITMONEY

        TicketsPaidInv ==
          \A c \in AllHonest :
            \A s \in Tickets[c] : seatMap[s] = "paid"

        NoDoubleSell ==
          \A s \in Seats :
            Cardinality({c \in AllHonest : s \in Tickets[c]}) <= 1

        \* attacker should never obtain tickets (safety)
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
            \* updateIP: authenticated IP change
            if (internalReq.type = "updateIP") {
                if (internalReq.bankID \in AllHonest
                    /\ internalReq.password = Password[internalReq.bankID]) {

                    \* store the new IP for that bankID
                    ipOf := [ipOf EXCEPT ![internalReq.bankID] = internalReq.from];

                    \* IMPORTANT: reply to the new IP directly (avoid orphan replies)
                    Channels[internalReq.from] :=
                      Append(Channels[internalReq.from],
                             [type |-> "confirm", from |-> 0, seat |-> 1,
                              bankID |-> -2, password |-> 0, seats |-> {}]);
                } else {
                    \* deny to the sender's IP
                    Channels[internalReq.from] :=
                      Append(Channels[internalReq.from],
                             [type |-> "deny", from |-> 0, seat |-> 1,
                              bankID |-> -2, password |-> 0, seats |-> {}]);
                };

            \* reserve: reserve an available seat
            } else if (internalReq.type = "reserve") {
                if (internalReq.bankID \in AllHonest
                    /\ internalReq.password = Password[internalReq.bankID]
                    /\ seatMap[internalReq.seat] = "available") {

                    seatMap[internalReq.seat] := "reserved";
                    ResOwner[internalReq.seat] := internalReq.bankID;

                    Channels[ipOf[internalReq.bankID]] :=
                      Append(Channels[ipOf[internalReq.bankID]],
                             [type |-> "confirm", from |-> 0,
                              seat |-> internalReq.seat,
                              bankID |-> -2, password |-> 0, seats |-> {}]);
                } else {
                    \* if bankID is honest, reply to its current ipOf
                    if (internalReq.bankID \in AllHonest) {
                        Channels[ipOf[internalReq.bankID]] :=
                          Append(Channels[ipOf[internalReq.bankID]],
                                 [type |-> "deny", from |-> 0,
                                  seat |-> internalReq.seat,
                                  bankID |-> -2, password |-> 0, seats |-> {}]);
                    } else {
                        \* unknown/non-honest id: reply to sender IP
                        Channels[internalReq.from] :=
                          Append(Channels[internalReq.from],
                                 [type |-> "deny", from |-> 0,
                                  seat |-> internalReq.seat,
                                  bankID |-> -2, password |-> 0, seats |-> {}]);
                    };
                };

            \* pay: pay only if the seat is reserved by this client
            } else if (internalReq.type = "pay") {
                if (internalReq.bankID \in AllHonest
                    /\ internalReq.password = Password[internalReq.bankID]
                    /\ seatMap[internalReq.seat] = "reserved"
                    /\ ResOwner[internalReq.seat] = internalReq.bankID
                    /\ BankAccount[internalReq.bankID] > 0) {

                    seatMap[internalReq.seat] := "paid";
                    ResOwner[internalReq.seat] := -2;

                    BankAccount := [BankAccount EXCEPT
                                      ![internalReq.bankID] = @ - 1,
                                      ![0] = @ + 1];

                    Tickets := [Tickets EXCEPT
                                  ![internalReq.bankID] = @ \union {internalReq.seat}];

                    Channels[ipOf[internalReq.bankID]] :=
                      Append(Channels[ipOf[internalReq.bankID]],
                             [type |-> "confirm", from |-> 0,
                              seat |-> internalReq.seat,
                              bankID |-> -2, password |-> 0, seats |-> {}]);
                } else {
                    if (internalReq.bankID \in AllHonest) {
                        Channels[ipOf[internalReq.bankID]] :=
                          Append(Channels[ipOf[internalReq.bankID]],
                                 [type |-> "deny", from |-> 0,
                                  seat |-> internalReq.seat,
                                  bankID |-> -2, password |-> 0, seats |-> {}]);
                    } else {
                        Channels[internalReq.from] :=
                          Append(Channels[internalReq.from],
                                 [type |-> "deny", from |-> 0,
                                  seat |-> internalReq.seat,
                                  bankID |-> -2, password |-> 0, seats |-> {}]);
                    };
                };

            \* cancel: cancel only reservations owned by this client
            } else if (internalReq.type = "cancel") {
                if (internalReq.bankID \in AllHonest
                    /\ internalReq.password = Password[internalReq.bankID]
                    /\ seatMap[internalReq.seat] = "reserved"
                    /\ ResOwner[internalReq.seat] = internalReq.bankID) {

                    seatMap[internalReq.seat] := "available";
                    ResOwner[internalReq.seat] := -2;

                    Channels[ipOf[internalReq.bankID]] :=
                      Append(Channels[ipOf[internalReq.bankID]],
                             [type |-> "confirm", from |-> 0,
                              seat |-> internalReq.seat,
                              bankID |-> -2, password |-> 0, seats |-> {}]);
                } else {
                    if (internalReq.bankID \in AllHonest) {
                        Channels[ipOf[internalReq.bankID]] :=
                          Append(Channels[ipOf[internalReq.bankID]],
                                 [type |-> "deny", from |-> 0,
                                  seat |-> internalReq.seat,
                                  bankID |-> -2, password |-> 0, seats |-> {}]);
                    } else {
                        Channels[internalReq.from] :=
                          Append(Channels[internalReq.from],
                                 [type |-> "deny", from |-> 0,
                                  seat |-> internalReq.seat,
                                  bankID |-> -2, password |-> 0, seats |-> {}]);
                    };
                };

            } else {
                skip;
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
        reservedSeat = 1;
        doCancel = FALSE;

        ipChanges = 0;  \* NEW: bound IP changes to preserve termination
    {
        InitTarget:
        target := CHOOSE k \in 0..Min2(INITMONEY, NUMSEATS) : TRUE;

        s1: while (CState[self] # "done") {

            CheckDone:
            if (Cardinality(Tickets[self]) >= target
                \/ (\A s \in Seats : seatMap[s] = "paid")) {
                CState[self] := "done";
            } else {

                either {
                    \* authenticated IP change (only once)
                    ChWaitIdle:
                    await (CState[self] = "idle" /\ ipChanges < 1);

                    ChSend:
                    CState[self] := "waiting";
                    ip := CHOOSE new \in IPs : new # ip;  \* pick a different IP
                    ipChanges := ipChanges + 1;

                    Channels[0] := Append(Channels[0],
                        [type |-> "updateIP", from |-> ip, seat |-> 1,
                         bankID |-> id, password |-> Password[id], seats |-> {}]);

                    ChWait:
                    await (Len(Channels[ip]) > 0);
                    reply := Head(Channels[ip]);
                    Channels[ip] := Tail(Channels[ip]);

                    ChDone:
                    CState[self] := "idle";

                } or {

                    \* step 1: reserve a random seat
                    BWaitIdle:
                    await (CState[self] = "idle");

                    BSendReserve:
                    CState[self] := "waiting";
                    wantSeat := CHOOSE s \in Seats : TRUE;

                    Channels[0] := Append(Channels[0],
                        [type |-> "reserve", from |-> ip, seat |-> wantSeat,
                         bankID |-> id, password |-> Password[id], seats |-> {}]);

                    RWait:
                    await (Len(Channels[ip]) > 0);
                    reply := Head(Channels[ip]);
                    Channels[ip] := Tail(Channels[ip]);

                    \* decide whether to cancel or pay after a successful reservation
                    doCancel := CHOOSE b \in {TRUE, FALSE} : TRUE;

                    PostReserve:
                    if (reply.type = "confirm") {
                        reservedSeat := wantSeat;

                        if (doCancel) {
                            CancelSend:
                            Channels[0] := Append(Channels[0],
                                [type |-> "cancel", from |-> ip, seat |-> reservedSeat,
                                 bankID |-> id, password |-> Password[id], seats |-> {}]);
                        } else {
                            PaySend:
                            Channels[0] := Append(Channels[0],
                                [type |-> "pay", from |-> ip, seat |-> reservedSeat,
                                 bankID |-> id, password |-> Password[id], seats |-> {}]);
                        };

                        PostWait:
                        await (Len(Channels[ip]) > 0);
                        reply := Head(Channels[ip]);
                        Channels[ip] := Tail(Channels[ip]);
                    } else {
                        skip;
                    };

                    JoinAfterChoice:
                    CState[self] := "idle";
                };
            };
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
        \* attacker tries to act as someone else (wrong password) -> should be denied.
        MStep:
        while (scamsCount < 1 /\ ~AllDone) {
            with (h \in AllHonest, s \in Seats) {
                targetID := h;
                targetSeat := s;
            };

            MSend:
            Channels[0] := Append(Channels[0],
                [type |-> "reserve", from |-> ip, seat |-> targetSeat,
                 bankID |-> targetID, password |-> Password[self], seats |-> {}]);

            scamsCount := scamsCount + 1;

            MGetReply:
            await (Len(Channels[ip]) > 0);
            reply := Head(Channels[ip]);
            Channels[ip] := Tail(Channels[ip]);

            MStore:
            if (reply.type = "confirm") {
                MyTickets[self] := MyTickets[self] \cup {reply.seat};
            };
        };

        Done_:
        while (TRUE) { skip; };
    }
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "8e67b8da" /\ chksum(tla) = "4f9090f0")
\* Label s1 of process Server at line 108 col 13 changed to s1_
\* Label Done_ of process Server at line 247 col 9 changed to Done__
\* Label Done_ of process HClient at line 350 col 9 changed to Done__H
\* Process variable ip of process Server at line 105 col 9 changed to ip_
\* Process variable ip of process HClient at line 253 col 9 changed to ip_H
\* Process variable reply of process HClient at line 256 col 9 changed to reply_
VARIABLES BankAccount, Channels, seatMap, ResOwner, Tickets, CState, 
          MyTickets, ipOf, pc

(* define statement *)
AllMalicious == IF MALICIOUS THEN {-1} ELSE {}
AllHonest == {i \in 1..NUMCLIENTS : TRUE}
AllClients == AllHonest \union AllMalicious
AllParticipants == AllClients \union {0}


Password == [p \in AllParticipants |-> 2000 + p]

Seats == 1..NUMSEATS
SeatStates == {"available", "reserved", "paid"}

IPs == Nat \union {-1}


TransactionType ==
  {"reserve", "pay", "cancel", "updateIP", "confirm", "deny"}

bankIDType == AllParticipants \union {-2}


MessageType == [ type     : TransactionType,
                 from     : IPs,
                 seat     : Seats,
                 bankID   : bankIDType,
                 password : Nat,
                 seats    : SUBSET Seats ]


M0 == [ type |-> "reserve",
        from |-> 0,
        seat |-> 1,
        bankID |-> 0,
        password |-> 0,
        seats |-> {} ]

Money(p) == BankAccount[p]




TypeOK ==
  /\ BankAccount \in [AllParticipants -> Int]
  /\ Channels \in [AllParticipants -> Seq(MessageType)]
  /\ seatMap \in [Seats -> SeatStates]
  /\ ResOwner \in [Seats -> (AllHonest \cup {-2})]
  /\ Tickets \in [AllHonest -> SUBSET Seats]
  /\ CState \in [AllHonest -> {"idle","waiting","done"}]
  /\ MyTickets \in [AllMalicious -> SUBSET Seats]
  /\ ipOf \in [AllHonest -> IPs]

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

VARIABLES ip_, internalReq, id, ip_H, wantSeat, reply_, target, reservedSeat, 
          doCancel, ipChanges, ip, targetID, targetSeat, reply, scamsCount

vars == << BankAccount, Channels, seatMap, ResOwner, Tickets, CState, 
           MyTickets, ipOf, pc, ip_, internalReq, id, ip_H, wantSeat, reply_, 
           target, reservedSeat, doCancel, ipChanges, ip, targetID, 
           targetSeat, reply, scamsCount >>

ProcSet == {0} \cup (AllHonest) \cup (AllMalicious)

Init == (* Global variables *)
        /\ BankAccount = [x \in AllParticipants |-> IF x = 0 THEN 0 ELSE INITMONEY]
        /\ Channels = [x \in AllParticipants |-> <<>>]
        /\ seatMap = [s \in 1..NUMSEATS |-> "available"]
        /\ ResOwner = [s \in Seats |-> -2]
        /\ Tickets = [c \in 1..NUMCLIENTS |-> {}]
        /\ CState = [c \in 1..NUMCLIENTS |-> "idle"]
        /\ MyTickets = [m \in AllMalicious |-> {}]
        /\ ipOf = [c \in AllHonest |-> c]
        (* Process Server *)
        /\ ip_ = 0
        /\ internalReq = M0
        (* Process HClient *)
        /\ id = [self \in AllHonest |-> self]
        /\ ip_H = [self \in AllHonest |-> self]
        /\ wantSeat = [self \in AllHonest |-> 1]
        /\ reply_ = [self \in AllHonest |-> M0]
        /\ target = [self \in AllHonest |-> 0]
        /\ reservedSeat = [self \in AllHonest |-> 1]
        /\ doCancel = [self \in AllHonest |-> FALSE]
        /\ ipChanges = [self \in AllHonest |-> 0]
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
       /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, Tickets, 
                       CState, MyTickets, ipOf, ip_, internalReq, id, ip_H, 
                       wantSeat, reply_, target, reservedSeat, doCancel, 
                       ipChanges, ip, targetID, targetSeat, reply, scamsCount >>

WW == /\ pc[0] = "WW"
      /\ (Len(Channels[ip_]) > 0)
      /\ pc' = [pc EXCEPT ![0] = "GET"]
      /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, Tickets, 
                      CState, MyTickets, ipOf, ip_, internalReq, id, ip_H, 
                      wantSeat, reply_, target, reservedSeat, doCancel, 
                      ipChanges, ip, targetID, targetSeat, reply, scamsCount >>

GET == /\ pc[0] = "GET"
       /\ internalReq' = Head(Channels[ip_])
       /\ Channels' = [Channels EXCEPT ![ip_] = Tail(Channels[ip_])]
       /\ pc' = [pc EXCEPT ![0] = "TREAT"]
       /\ UNCHANGED << BankAccount, seatMap, ResOwner, Tickets, CState, 
                       MyTickets, ipOf, ip_, id, ip_H, wantSeat, reply_, 
                       target, reservedSeat, doCancel, ipChanges, ip, targetID, 
                       targetSeat, reply, scamsCount >>

TREAT == /\ pc[0] = "TREAT"
         /\ IF internalReq.type = "updateIP"
               THEN /\ IF internalReq.bankID \in AllHonest
                          /\ internalReq.password = Password[internalReq.bankID]
                          THEN /\ ipOf' = [ipOf EXCEPT ![internalReq.bankID] = internalReq.from]
                               /\ Channels' = [Channels EXCEPT ![internalReq.from] = Append(Channels[internalReq.from],
                                                                                            [type |-> "confirm", from |-> 0, seat |-> 1,
                                                                                             bankID |-> -2, password |-> 0, seats |-> {}])]
                          ELSE /\ Channels' = [Channels EXCEPT ![internalReq.from] = Append(Channels[internalReq.from],
                                                                                            [type |-> "deny", from |-> 0, seat |-> 1,
                                                                                             bankID |-> -2, password |-> 0, seats |-> {}])]
                               /\ ipOf' = ipOf
                    /\ UNCHANGED << BankAccount, seatMap, ResOwner, Tickets >>
               ELSE /\ IF internalReq.type = "reserve"
                          THEN /\ IF internalReq.bankID \in AllHonest
                                     /\ internalReq.password = Password[internalReq.bankID]
                                     /\ seatMap[internalReq.seat] = "available"
                                     THEN /\ seatMap' = [seatMap EXCEPT ![internalReq.seat] = "reserved"]
                                          /\ ResOwner' = [ResOwner EXCEPT ![internalReq.seat] = internalReq.bankID]
                                          /\ Channels' = [Channels EXCEPT ![ipOf[internalReq.bankID]] = Append(Channels[ipOf[internalReq.bankID]],
                                                                                                               [type |-> "confirm", from |-> 0,
                                                                                                                seat |-> internalReq.seat,
                                                                                                                bankID |-> -2, password |-> 0, seats |-> {}])]
                                     ELSE /\ IF internalReq.bankID \in AllHonest
                                                THEN /\ Channels' = [Channels EXCEPT ![ipOf[internalReq.bankID]] = Append(Channels[ipOf[internalReq.bankID]],
                                                                                                                          [type |-> "deny", from |-> 0,
                                                                                                                           seat |-> internalReq.seat,
                                                                                                                           bankID |-> -2, password |-> 0, seats |-> {}])]
                                                ELSE /\ Channels' = [Channels EXCEPT ![internalReq.from] = Append(Channels[internalReq.from],
                                                                                                                  [type |-> "deny", from |-> 0,
                                                                                                                   seat |-> internalReq.seat,
                                                                                                                   bankID |-> -2, password |-> 0, seats |-> {}])]
                                          /\ UNCHANGED << seatMap, ResOwner >>
                               /\ UNCHANGED << BankAccount, Tickets >>
                          ELSE /\ IF internalReq.type = "pay"
                                     THEN /\ IF internalReq.bankID \in AllHonest
                                                /\ internalReq.password = Password[internalReq.bankID]
                                                /\ seatMap[internalReq.seat] = "reserved"
                                                /\ ResOwner[internalReq.seat] = internalReq.bankID
                                                /\ BankAccount[internalReq.bankID] > 0
                                                THEN /\ seatMap' = [seatMap EXCEPT ![internalReq.seat] = "paid"]
                                                     /\ ResOwner' = [ResOwner EXCEPT ![internalReq.seat] = -2]
                                                     /\ BankAccount' = [BankAccount EXCEPT
                                                                          ![internalReq.bankID] = @ - 1,
                                                                          ![0] = @ + 1]
                                                     /\ Tickets' = [Tickets EXCEPT
                                                                      ![internalReq.bankID] = @ \union {internalReq.seat}]
                                                     /\ Channels' = [Channels EXCEPT ![ipOf[internalReq.bankID]] = Append(Channels[ipOf[internalReq.bankID]],
                                                                                                                          [type |-> "confirm", from |-> 0,
                                                                                                                           seat |-> internalReq.seat,
                                                                                                                           bankID |-> -2, password |-> 0, seats |-> {}])]
                                                ELSE /\ IF internalReq.bankID \in AllHonest
                                                           THEN /\ Channels' = [Channels EXCEPT ![ipOf[internalReq.bankID]] = Append(Channels[ipOf[internalReq.bankID]],
                                                                                                                                     [type |-> "deny", from |-> 0,
                                                                                                                                      seat |-> internalReq.seat,
                                                                                                                                      bankID |-> -2, password |-> 0, seats |-> {}])]
                                                           ELSE /\ Channels' = [Channels EXCEPT ![internalReq.from] = Append(Channels[internalReq.from],
                                                                                                                             [type |-> "deny", from |-> 0,
                                                                                                                              seat |-> internalReq.seat,
                                                                                                                              bankID |-> -2, password |-> 0, seats |-> {}])]
                                                     /\ UNCHANGED << BankAccount, 
                                                                     seatMap, 
                                                                     ResOwner, 
                                                                     Tickets >>
                                     ELSE /\ IF internalReq.type = "cancel"
                                                THEN /\ IF internalReq.bankID \in AllHonest
                                                           /\ internalReq.password = Password[internalReq.bankID]
                                                           /\ seatMap[internalReq.seat] = "reserved"
                                                           /\ ResOwner[internalReq.seat] = internalReq.bankID
                                                           THEN /\ seatMap' = [seatMap EXCEPT ![internalReq.seat] = "available"]
                                                                /\ ResOwner' = [ResOwner EXCEPT ![internalReq.seat] = -2]
                                                                /\ Channels' = [Channels EXCEPT ![ipOf[internalReq.bankID]] = Append(Channels[ipOf[internalReq.bankID]],
                                                                                                                                     [type |-> "confirm", from |-> 0,
                                                                                                                                      seat |-> internalReq.seat,
                                                                                                                                      bankID |-> -2, password |-> 0, seats |-> {}])]
                                                           ELSE /\ IF internalReq.bankID \in AllHonest
                                                                      THEN /\ Channels' = [Channels EXCEPT ![ipOf[internalReq.bankID]] = Append(Channels[ipOf[internalReq.bankID]],
                                                                                                                                                [type |-> "deny", from |-> 0,
                                                                                                                                                 seat |-> internalReq.seat,
                                                                                                                                                 bankID |-> -2, password |-> 0, seats |-> {}])]
                                                                      ELSE /\ Channels' = [Channels EXCEPT ![internalReq.from] = Append(Channels[internalReq.from],
                                                                                                                                        [type |-> "deny", from |-> 0,
                                                                                                                                         seat |-> internalReq.seat,
                                                                                                                                         bankID |-> -2, password |-> 0, seats |-> {}])]
                                                                /\ UNCHANGED << seatMap, 
                                                                                ResOwner >>
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED << Channels, 
                                                                     seatMap, 
                                                                     ResOwner >>
                                          /\ UNCHANGED << BankAccount, Tickets >>
                    /\ ipOf' = ipOf
         /\ pc' = [pc EXCEPT ![0] = "s1_"]
         /\ UNCHANGED << CState, MyTickets, ip_, internalReq, id, ip_H, 
                         wantSeat, reply_, target, reservedSeat, doCancel, 
                         ipChanges, ip, targetID, targetSeat, reply, 
                         scamsCount >>

Done__ == /\ pc[0] = "Done__"
          /\ TRUE
          /\ pc' = [pc EXCEPT ![0] = "Done__"]
          /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, Tickets, 
                          CState, MyTickets, ipOf, ip_, internalReq, id, ip_H, 
                          wantSeat, reply_, target, reservedSeat, doCancel, 
                          ipChanges, ip, targetID, targetSeat, reply, 
                          scamsCount >>

Server == s1_ \/ WW \/ GET \/ TREAT \/ Done__

InitTarget(self) == /\ pc[self] = "InitTarget"
                    /\ target' = [target EXCEPT ![self] = CHOOSE k \in 0..Min2(INITMONEY, NUMSEATS) : TRUE]
                    /\ pc' = [pc EXCEPT ![self] = "s1"]
                    /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, 
                                    Tickets, CState, MyTickets, ipOf, ip_, 
                                    internalReq, id, ip_H, wantSeat, reply_, 
                                    reservedSeat, doCancel, ipChanges, ip, 
                                    targetID, targetSeat, reply, scamsCount >>

s1(self) == /\ pc[self] = "s1"
            /\ IF CState[self] # "done"
                  THEN /\ pc' = [pc EXCEPT ![self] = "CheckDone"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done__H"]
            /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, Tickets, 
                            CState, MyTickets, ipOf, ip_, internalReq, id, 
                            ip_H, wantSeat, reply_, target, reservedSeat, 
                            doCancel, ipChanges, ip, targetID, targetSeat, 
                            reply, scamsCount >>

CheckDone(self) == /\ pc[self] = "CheckDone"
                   /\ IF Cardinality(Tickets[self]) >= target[self]
                         \/ (\A s \in Seats : seatMap[s] = "paid")
                         THEN /\ CState' = [CState EXCEPT ![self] = "done"]
                              /\ pc' = [pc EXCEPT ![self] = "s1"]
                         ELSE /\ \/ /\ pc' = [pc EXCEPT ![self] = "ChWaitIdle"]
                                 \/ /\ pc' = [pc EXCEPT ![self] = "BWaitIdle"]
                              /\ UNCHANGED CState
                   /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, 
                                   Tickets, MyTickets, ipOf, ip_, internalReq, 
                                   id, ip_H, wantSeat, reply_, target, 
                                   reservedSeat, doCancel, ipChanges, ip, 
                                   targetID, targetSeat, reply, scamsCount >>

ChWaitIdle(self) == /\ pc[self] = "ChWaitIdle"
                    /\ (CState[self] = "idle" /\ ipChanges[self] < 1)
                    /\ pc' = [pc EXCEPT ![self] = "ChSend"]
                    /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, 
                                    Tickets, CState, MyTickets, ipOf, ip_, 
                                    internalReq, id, ip_H, wantSeat, reply_, 
                                    target, reservedSeat, doCancel, ipChanges, 
                                    ip, targetID, targetSeat, reply, 
                                    scamsCount >>

ChSend(self) == /\ pc[self] = "ChSend"
                /\ CState' = [CState EXCEPT ![self] = "waiting"]
                /\ ip_H' = [ip_H EXCEPT ![self] = CHOOSE new \in IPs : new # ip_H[self]]
                /\ ipChanges' = [ipChanges EXCEPT ![self] = ipChanges[self] + 1]
                /\ Channels' = [Channels EXCEPT ![0] =            Append(Channels[0],
                                                       [type |-> "updateIP", from |-> ip_H'[self], seat |-> 1,
                                                        bankID |-> id[self], password |-> Password[id[self]], seats |-> {}])]
                /\ pc' = [pc EXCEPT ![self] = "ChWait"]
                /\ UNCHANGED << BankAccount, seatMap, ResOwner, Tickets, 
                                MyTickets, ipOf, ip_, internalReq, id, 
                                wantSeat, reply_, target, reservedSeat, 
                                doCancel, ip, targetID, targetSeat, reply, 
                                scamsCount >>

ChWait(self) == /\ pc[self] = "ChWait"
                /\ (Len(Channels[ip_H[self]]) > 0)
                /\ reply_' = [reply_ EXCEPT ![self] = Head(Channels[ip_H[self]])]
                /\ Channels' = [Channels EXCEPT ![ip_H[self]] = Tail(Channels[ip_H[self]])]
                /\ pc' = [pc EXCEPT ![self] = "ChDone"]
                /\ UNCHANGED << BankAccount, seatMap, ResOwner, Tickets, 
                                CState, MyTickets, ipOf, ip_, internalReq, id, 
                                ip_H, wantSeat, target, reservedSeat, doCancel, 
                                ipChanges, ip, targetID, targetSeat, reply, 
                                scamsCount >>

ChDone(self) == /\ pc[self] = "ChDone"
                /\ CState' = [CState EXCEPT ![self] = "idle"]
                /\ pc' = [pc EXCEPT ![self] = "s1"]
                /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, 
                                Tickets, MyTickets, ipOf, ip_, internalReq, id, 
                                ip_H, wantSeat, reply_, target, reservedSeat, 
                                doCancel, ipChanges, ip, targetID, targetSeat, 
                                reply, scamsCount >>

BWaitIdle(self) == /\ pc[self] = "BWaitIdle"
                   /\ (CState[self] = "idle")
                   /\ pc' = [pc EXCEPT ![self] = "BSendReserve"]
                   /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, 
                                   Tickets, CState, MyTickets, ipOf, ip_, 
                                   internalReq, id, ip_H, wantSeat, reply_, 
                                   target, reservedSeat, doCancel, ipChanges, 
                                   ip, targetID, targetSeat, reply, scamsCount >>

BSendReserve(self) == /\ pc[self] = "BSendReserve"
                      /\ CState' = [CState EXCEPT ![self] = "waiting"]
                      /\ wantSeat' = [wantSeat EXCEPT ![self] = CHOOSE s \in Seats : TRUE]
                      /\ Channels' = [Channels EXCEPT ![0] =            Append(Channels[0],
                                                             [type |-> "reserve", from |-> ip_H[self], seat |-> wantSeat'[self],
                                                              bankID |-> id[self], password |-> Password[id[self]], seats |-> {}])]
                      /\ pc' = [pc EXCEPT ![self] = "RWait"]
                      /\ UNCHANGED << BankAccount, seatMap, ResOwner, Tickets, 
                                      MyTickets, ipOf, ip_, internalReq, id, 
                                      ip_H, reply_, target, reservedSeat, 
                                      doCancel, ipChanges, ip, targetID, 
                                      targetSeat, reply, scamsCount >>

RWait(self) == /\ pc[self] = "RWait"
               /\ (Len(Channels[ip_H[self]]) > 0)
               /\ reply_' = [reply_ EXCEPT ![self] = Head(Channels[ip_H[self]])]
               /\ Channels' = [Channels EXCEPT ![ip_H[self]] = Tail(Channels[ip_H[self]])]
               /\ doCancel' = [doCancel EXCEPT ![self] = CHOOSE b \in {TRUE, FALSE} : TRUE]
               /\ pc' = [pc EXCEPT ![self] = "PostReserve"]
               /\ UNCHANGED << BankAccount, seatMap, ResOwner, Tickets, CState, 
                               MyTickets, ipOf, ip_, internalReq, id, ip_H, 
                               wantSeat, target, reservedSeat, ipChanges, ip, 
                               targetID, targetSeat, reply, scamsCount >>

PostReserve(self) == /\ pc[self] = "PostReserve"
                     /\ IF reply_[self].type = "confirm"
                           THEN /\ reservedSeat' = [reservedSeat EXCEPT ![self] = wantSeat[self]]
                                /\ IF doCancel[self]
                                      THEN /\ pc' = [pc EXCEPT ![self] = "CancelSend"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "PaySend"]
                           ELSE /\ TRUE
                                /\ pc' = [pc EXCEPT ![self] = "JoinAfterChoice"]
                                /\ UNCHANGED reservedSeat
                     /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, 
                                     Tickets, CState, MyTickets, ipOf, ip_, 
                                     internalReq, id, ip_H, wantSeat, reply_, 
                                     target, doCancel, ipChanges, ip, targetID, 
                                     targetSeat, reply, scamsCount >>

PostWait(self) == /\ pc[self] = "PostWait"
                  /\ (Len(Channels[ip_H[self]]) > 0)
                  /\ reply_' = [reply_ EXCEPT ![self] = Head(Channels[ip_H[self]])]
                  /\ Channels' = [Channels EXCEPT ![ip_H[self]] = Tail(Channels[ip_H[self]])]
                  /\ pc' = [pc EXCEPT ![self] = "JoinAfterChoice"]
                  /\ UNCHANGED << BankAccount, seatMap, ResOwner, Tickets, 
                                  CState, MyTickets, ipOf, ip_, internalReq, 
                                  id, ip_H, wantSeat, target, reservedSeat, 
                                  doCancel, ipChanges, ip, targetID, 
                                  targetSeat, reply, scamsCount >>

CancelSend(self) == /\ pc[self] = "CancelSend"
                    /\ Channels' = [Channels EXCEPT ![0] =            Append(Channels[0],
                                                           [type |-> "cancel", from |-> ip_H[self], seat |-> reservedSeat[self],
                                                            bankID |-> id[self], password |-> Password[id[self]], seats |-> {}])]
                    /\ pc' = [pc EXCEPT ![self] = "PostWait"]
                    /\ UNCHANGED << BankAccount, seatMap, ResOwner, Tickets, 
                                    CState, MyTickets, ipOf, ip_, internalReq, 
                                    id, ip_H, wantSeat, reply_, target, 
                                    reservedSeat, doCancel, ipChanges, ip, 
                                    targetID, targetSeat, reply, scamsCount >>

PaySend(self) == /\ pc[self] = "PaySend"
                 /\ Channels' = [Channels EXCEPT ![0] =            Append(Channels[0],
                                                        [type |-> "pay", from |-> ip_H[self], seat |-> reservedSeat[self],
                                                         bankID |-> id[self], password |-> Password[id[self]], seats |-> {}])]
                 /\ pc' = [pc EXCEPT ![self] = "PostWait"]
                 /\ UNCHANGED << BankAccount, seatMap, ResOwner, Tickets, 
                                 CState, MyTickets, ipOf, ip_, internalReq, id, 
                                 ip_H, wantSeat, reply_, target, reservedSeat, 
                                 doCancel, ipChanges, ip, targetID, targetSeat, 
                                 reply, scamsCount >>

JoinAfterChoice(self) == /\ pc[self] = "JoinAfterChoice"
                         /\ CState' = [CState EXCEPT ![self] = "idle"]
                         /\ pc' = [pc EXCEPT ![self] = "s1"]
                         /\ UNCHANGED << BankAccount, Channels, seatMap, 
                                         ResOwner, Tickets, MyTickets, ipOf, 
                                         ip_, internalReq, id, ip_H, wantSeat, 
                                         reply_, target, reservedSeat, 
                                         doCancel, ipChanges, ip, targetID, 
                                         targetSeat, reply, scamsCount >>

Done__H(self) == /\ pc[self] = "Done__H"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT ![self] = "Done__H"]
                 /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, 
                                 Tickets, CState, MyTickets, ipOf, ip_, 
                                 internalReq, id, ip_H, wantSeat, reply_, 
                                 target, reservedSeat, doCancel, ipChanges, ip, 
                                 targetID, targetSeat, reply, scamsCount >>

HClient(self) == InitTarget(self) \/ s1(self) \/ CheckDone(self)
                    \/ ChWaitIdle(self) \/ ChSend(self) \/ ChWait(self)
                    \/ ChDone(self) \/ BWaitIdle(self)
                    \/ BSendReserve(self) \/ RWait(self)
                    \/ PostReserve(self) \/ PostWait(self)
                    \/ CancelSend(self) \/ PaySend(self)
                    \/ JoinAfterChoice(self) \/ Done__H(self)

MStep(self) == /\ pc[self] = "MStep"
               /\ IF scamsCount[self] < 1 /\ ~AllDone
                     THEN /\ \E h \in AllHonest:
                               \E s \in Seats:
                                 /\ targetID' = [targetID EXCEPT ![self] = h]
                                 /\ targetSeat' = [targetSeat EXCEPT ![self] = s]
                          /\ pc' = [pc EXCEPT ![self] = "MSend"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done_"]
                          /\ UNCHANGED << targetID, targetSeat >>
               /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, 
                               Tickets, CState, MyTickets, ipOf, ip_, 
                               internalReq, id, ip_H, wantSeat, reply_, target, 
                               reservedSeat, doCancel, ipChanges, ip, reply, 
                               scamsCount >>

MSend(self) == /\ pc[self] = "MSend"
               /\ Channels' = [Channels EXCEPT ![0] =            Append(Channels[0],
                                                      [type |-> "reserve", from |-> ip[self], seat |-> targetSeat[self],
                                                       bankID |-> targetID[self], password |-> Password[self], seats |-> {}])]
               /\ scamsCount' = [scamsCount EXCEPT ![self] = scamsCount[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "MGetReply"]
               /\ UNCHANGED << BankAccount, seatMap, ResOwner, Tickets, CState, 
                               MyTickets, ipOf, ip_, internalReq, id, ip_H, 
                               wantSeat, reply_, target, reservedSeat, 
                               doCancel, ipChanges, ip, targetID, targetSeat, 
                               reply >>

MGetReply(self) == /\ pc[self] = "MGetReply"
                   /\ (Len(Channels[ip[self]]) > 0)
                   /\ reply' = [reply EXCEPT ![self] = Head(Channels[ip[self]])]
                   /\ Channels' = [Channels EXCEPT ![ip[self]] = Tail(Channels[ip[self]])]
                   /\ pc' = [pc EXCEPT ![self] = "MStore"]
                   /\ UNCHANGED << BankAccount, seatMap, ResOwner, Tickets, 
                                   CState, MyTickets, ipOf, ip_, internalReq, 
                                   id, ip_H, wantSeat, reply_, target, 
                                   reservedSeat, doCancel, ipChanges, ip, 
                                   targetID, targetSeat, scamsCount >>

MStore(self) == /\ pc[self] = "MStore"
                /\ IF reply[self].type = "confirm"
                      THEN /\ MyTickets' = [MyTickets EXCEPT ![self] = MyTickets[self] \cup {reply[self].seat}]
                      ELSE /\ TRUE
                           /\ UNCHANGED MyTickets
                /\ pc' = [pc EXCEPT ![self] = "MStep"]
                /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, 
                                Tickets, CState, ipOf, ip_, internalReq, id, 
                                ip_H, wantSeat, reply_, target, reservedSeat, 
                                doCancel, ipChanges, ip, targetID, targetSeat, 
                                reply, scamsCount >>

Done_(self) == /\ pc[self] = "Done_"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done_"]
               /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, 
                               Tickets, CState, MyTickets, ipOf, ip_, 
                               internalReq, id, ip_H, wantSeat, reply_, target, 
                               reservedSeat, doCancel, ipChanges, ip, targetID, 
                               targetSeat, reply, scamsCount >>

MClient(self) == MStep(self) \/ MSend(self) \/ MGetReply(self)
                    \/ MStore(self) \/ Done_(self)

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
=============================================================================
