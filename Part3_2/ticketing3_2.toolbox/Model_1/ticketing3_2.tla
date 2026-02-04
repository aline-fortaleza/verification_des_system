----------------------------- MODULE ticketing3_2 -----------------------------
EXTENDS Integers, TLC, Sequences, FiniteSets

CONSTANTS NUMCLIENTS, MALICIOUS, NUMSEATS, INITMONEY

Min2(a, b) == IF a <= b THEN a ELSE b

(* --algorithm ticketing {
    variables
        BankAccount = [x \in AllParticipants |-> IF x = 0 THEN 0 ELSE INITMONEY];
        Channels    = [x \in AllParticipants |-> <<>>];

        seatMap     = [s \in 1..NUMSEATS |-> "available"];
        ResOwner    = [s \in 1..NUMSEATS |-> -2];      \* -2 = nobody

        Tickets     = [c \in AllClients |-> {}];

        CState      = [c \in 1..NUMCLIENTS |-> "idle"];

    define {

        AllMalicious == IF MALICIOUS THEN {-1} ELSE {}
        AllHonest == {i \in 1..NUMCLIENTS : TRUE}
        AllClients == AllHonest \union AllMalicious
        AllParticipants == AllClients \union {0}

        Seats == 1..NUMSEATS
        SeatStates == {"available", "reserved","paid"}

        IPs == Nat \union {-1}
        bankIDType == AllParticipants \union {-2}

        \* messages carry a set of seats
        MessageType ==
          [ type   : {"reserve", "cancelRes", "buy", "cancelPaid", "confirm", "deny"},
            from   : IPs,
            seats  : SUBSET Seats,
            bankID : bankIDType ]

        M0 == [type |-> "buy",
               from |-> 0,
               seats |-> {},
               bankID |-> 0]

        \* helpers for sets / batch updates
        SetSeats(map, S, v) ==
          [x \in DOMAIN map |-> IF x \in S THEN v ELSE map[x]]

        SetOwners(own, S, p) ==
          [x \in DOMAIN own |-> IF x \in S THEN p ELSE own[x]]

        AllAvailable(S) == \A s \in S : seatMap[s] = "available"
        AllReservedBy(S, p) == \A s \in S : seatMap[s] = "reserved" /\ ResOwner[s] = p
        AllPaidBy(S, p) == \A s \in S : seatMap[s] = "paid" /\ s \in Tickets[p]
        Cost(S) == Cardinality(S)

        \* safety / typing
        TypeOK ==
          /\ BankAccount \in [AllParticipants -> Int]
          /\ Channels \in [AllParticipants -> Seq(MessageType)]
          /\ ResOwner \in [Seats -> AllParticipants \union {-2}]
          /\ seatMap  \in [Seats -> SeatStates]
          /\ Tickets \in [AllClients -> SUBSET Seats]
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

        
        ReservedConsistent ==
          \A s \in Seats :
            (seatMap[s] = "reserved") => (ResOwner[s] \in AllClients)

        PaidNoOwner ==
          \A s \in Seats :
            seatMap[s] = "paid" => ResOwner[s] = -2

        \* stop condition
        AllDone ==
          /\ \A c \in AllHonest : CState[c] = "done"

        Terminates == <> AllDone
    }

    fair process (Server = 0)
    variables
        internalReq = M0;
    {
        s1: while (~AllDone) {

            WW:
            await (Len(Channels[0]) > 0 \/ AllDone);
            if (AllDone) {
                goto End;
            };

            GET:
            internalReq := Head(Channels[0]);
            Channels[0] := Tail(Channels[0]);

            TREAT:
            if (internalReq.type = "reserve") {

                if (internalReq.seats # {}
                    /\ AllAvailable(internalReq.seats)) {

                    seatMap  := SetSeats(seatMap, internalReq.seats, "reserved");
                    ResOwner := SetOwners(ResOwner, internalReq.seats, internalReq.bankID);

                    Channels[internalReq.from] :=
                      Append(Channels[internalReq.from],
                             [type |-> "confirm", from |-> 0, seats |-> internalReq.seats, bankID |-> -2]);
                } else {
                    Channels[internalReq.from] :=
                      Append(Channels[internalReq.from],
                             [type |-> "deny", from |-> 0, seats |-> internalReq.seats, bankID |-> -2]);
                };

            } else if (internalReq.type = "cancelRes") {

                if (internalReq.seats # {}
                    /\ AllReservedBy(internalReq.seats, internalReq.bankID)) {

                    seatMap  := SetSeats(seatMap, internalReq.seats, "available");
                    ResOwner := SetOwners(ResOwner, internalReq.seats, -2);

                    Channels[internalReq.from] :=
                      Append(Channels[internalReq.from],
                             [type |-> "confirm", from |-> 0, seats |-> internalReq.seats, bankID |-> -2]);
                } else {
                    Channels[internalReq.from] :=
                      Append(Channels[internalReq.from],
                             [type |-> "deny", from |-> 0, seats |-> internalReq.seats, bankID |-> -2]);
                };

            } else if (internalReq.type = "buy") {

                if (internalReq.seats # {}
                    /\ AllReservedBy(internalReq.seats, internalReq.bankID)
                    /\ BankAccount[internalReq.bankID] >= Cost(internalReq.seats)) {

                    seatMap  := SetSeats(seatMap, internalReq.seats, "paid");
                    ResOwner := SetOwners(ResOwner, internalReq.seats, -2);

                    BankAccount :=
                      [BankAccount EXCEPT
                        ![internalReq.bankID] = @ - Cost(internalReq.seats),
                        ![0]                 = @ + Cost(internalReq.seats)];

                    Tickets :=
                      [Tickets EXCEPT
                        ![internalReq.bankID] = @ \union internalReq.seats];

                    Channels[internalReq.from] :=
                      Append(Channels[internalReq.from],
                             [type |-> "confirm", from |-> 0, seats |-> internalReq.seats, bankID |-> -2]);
                } else {
                    Channels[internalReq.from] :=
                      Append(Channels[internalReq.from],
                             [type |-> "deny", from |-> 0, seats |-> internalReq.seats, bankID |-> -2]);
                };

            } else if (internalReq.type = "cancelPaid") {

                if (internalReq.seats # {}
                    /\ AllPaidBy(internalReq.seats, internalReq.bankID)) {

                    seatMap := SetSeats(seatMap, internalReq.seats, "available");

                    BankAccount :=
                      [BankAccount EXCEPT
                        ![internalReq.bankID] = @ + Cost(internalReq.seats),
                        ![0]                 = @ - Cost(internalReq.seats)];

                    Tickets :=
                      [Tickets EXCEPT
                        ![internalReq.bankID] = @ \ internalReq.seats];

                    Channels[internalReq.from] :=
                      Append(Channels[internalReq.from],
                             [type |-> "confirm", from |-> 0, seats |-> internalReq.seats, bankID |-> -2]);
                } else {
                    Channels[internalReq.from] :=
                      Append(Channels[internalReq.from],
                             [type |-> "deny", from |-> 0, seats |-> internalReq.seats, bankID |-> -2]);
                };

            } else {
                skip;
            };

            End:
                skip;


        };
    }

    fair process (HClient \in AllHonest)
    variables
        id = self;
        ip = self;

        wantSeat = 1;
        wantSeats = {};
        k = 0;
        tmp = {};

        reply = M0;
        target = 0;
        availSeats = {};
    {
        InitTarget:
        target := CHOOSE t \in 1..Min2(INITMONEY, NUMSEATS) : TRUE;

        s1: while (CState[self] # "done") {

            CheckDone:
            if (Cardinality(Tickets[self]) >= target
                \/ (\A s \in Seats : seatMap[s] = "paid")) {
                CState[self] := "done";
            } else {

                BWaitIdle:
                await (CState[self] = "idle");

                
                ActionChoice:
                if (Tickets[self] = {}) {
                    goto BReserveBuy;
                } else {
                    either {
                        goto BReserveBuy;
                    } or {
                        goto BCancelPaid;
                    };
                };
            
                \* reserve + Buy a SET of seats
                BReserveBuy:
                CState[self] := "waiting";
                availSeats := {s \in Seats : seatMap[s] = "available"};
                k := Min2(target - Cardinality(Tickets[self]),
                          Cardinality(availSeats));
                
                Label1:
                if (k = 0) {
                    CState[self] := "idle";
                    goto CheckDone;
                };
                
                Label2: 
                wantSeats := {};
                tmp := availSeats;
                PickLoop:
                while (Cardinality(wantSeats) < k) {
                    wantSeat := CHOOSE s \in tmp : TRUE;
                    wantSeats := wantSeats \union {wantSeat};
                    tmp := tmp \ {wantSeat};
                };
                \* 1 - reserve set
                Channels[0] := Append(Channels[0],
                                     [type |-> "reserve",
                                      from |-> ip,
                                      seats |-> wantSeats,
                                      bankID |-> id]);
                WaitResReply:
                await Len(Channels[ip]) > 0;
                reply := Head(Channels[ip]);
                Channels[ip] := Tail(Channels[ip]);
                
                Label3:
                if (reply.type = "confirm") {
                    \* 2 - buy same set
                    Channels[0] := Append(Channels[0],
                                         [type |-> "buy",
                                          from |-> ip,
                                          seats |-> wantSeats,
                                          bankID |-> id]);
                    WaitBuyReply:
                    await Len(Channels[ip]) > 0;
                    reply := Head(Channels[ip]);
                    Channels[ip] := Tail(Channels[ip]);
                };
                
                Label4:
                CState[self] := "idle";
                goto CheckDone;
            
                \* cancel just one paid seat (as a set of size 1) 
                BCancelPaid:
                if (Tickets[self] = {}) {
                    CState[self] := "idle";
                    goto CheckDone;
                };
                
                Label5:
                CState[self] := "waiting";
                wantSeat := CHOOSE s \in Tickets[self] : TRUE;
                wantSeats := {wantSeat};
                Channels[0] := Append(Channels[0],
                                     [type |-> "cancelPaid",
                                      from |-> ip,
                                      seats |-> wantSeats,
                                      bankID |-> id]);
                WaitCancelReply:
                await Len(Channels[ip]) > 0;
                reply := Head(Channels[ip]);
                Channels[ip] := Tail(Channels[ip]);
                CState[self] := "idle";
                goto CheckDone;
                };

            };
        };
}
        Done_:
        while (TRUE) { skip; };
    }

    fair process (MClient \in AllMalicious)
    variables
        id = self;
        ip = self;
        targetSeat = 0;
    {
        M1:
        await \E s \in Seats : seatMap[s] = "paid";

        FindTarget:
        targetSeat := CHOOSE s \in Seats : seatMap[s] = "paid";

        \* tries to cancel someone else's paid seat (should be denied)
        MExploit:
        Channels[0] := Append(Channels[0],
                             [type |-> "cancelPaid",
                              from |-> ip,
                              seats |-> {targetSeat},
                              bankID |-> id]);

        MWait:
        await Len(Channels[ip]) > 0;

        MDiscard:
        Channels[ip] := Tail(Channels[ip]);

        Done_:
        while (TRUE) { skip; };
    }

} *)
\* BEGIN TRANSLATION (chksum(pcal) = "4ae9a836" /\ chksum(tla) = "b394543a")
\* Label s1 of process Server at line 98 col 13 changed to s1_
VARIABLES BankAccount, Channels, seatMap, ResOwner, Tickets, CState, pc

(* define statement *)
AllMalicious == IF MALICIOUS THEN {-1} ELSE {}
AllHonest == {i \in 1..NUMCLIENTS : TRUE}
AllClients == AllHonest \union AllMalicious
AllParticipants == AllClients \union {0}

Seats == 1..NUMSEATS
SeatStates == {"available", "reserved","paid"}

IPs == Nat \union {-1}
bankIDType == AllParticipants \union {-2}


MessageType ==
  [ type   : {"reserve", "cancelRes", "buy", "cancelPaid", "confirm", "deny"},
    from   : IPs,
    seats  : SUBSET Seats,
    bankID : bankIDType ]

M0 == [type |-> "buy",
       from |-> 0,
       seats |-> {},
       bankID |-> 0]


SetSeats(map, S, v) ==
  [x \in DOMAIN map |-> IF x \in S THEN v ELSE map[x]]

SetOwners(own, S, p) ==
  [x \in DOMAIN own |-> IF x \in S THEN p ELSE own[x]]

AllAvailable(S) == \A s \in S : seatMap[s] = "available"
AllReservedBy(S, p) == \A s \in S : seatMap[s] = "reserved" /\ ResOwner[s] = p
AllPaidBy(S, p) == \A s \in S : seatMap[s] = "paid" /\ s \in Tickets[p]
Cost(S) == Cardinality(S)


TypeOK ==
  /\ BankAccount \in [AllParticipants -> Int]
  /\ Channels \in [AllParticipants -> Seq(MessageType)]
  /\ ResOwner \in [Seats -> AllParticipants \union {-2}]
  /\ seatMap  \in [Seats -> SeatStates]
  /\ Tickets \in [AllClients -> SUBSET Seats]
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


ReservedConsistent ==
  \A s \in Seats :
    (seatMap[s] = "reserved") => (ResOwner[s] \in AllClients)

PaidNoOwner ==
  \A s \in Seats :
    seatMap[s] = "paid" => ResOwner[s] = -2


AllDone ==
  /\ \A c \in AllHonest : CState[c] = "done"

Terminates == <> AllDone

VARIABLES internalReq, id, ip, wantSeat, wantSeats, k, tmp, reply, target, 
          availSeats

vars == << BankAccount, Channels, seatMap, ResOwner, Tickets, CState, pc, 
           internalReq, id, ip, wantSeat, wantSeats, k, tmp, reply, target, 
           availSeats >>

ProcSet == {0} \cup (AllHonest)

Init == (* Global variables *)
        /\ BankAccount = [x \in AllParticipants |-> IF x = 0 THEN 0 ELSE INITMONEY]
        /\ Channels = [x \in AllParticipants |-> <<>>]
        /\ seatMap = [s \in 1..NUMSEATS |-> "available"]
        /\ ResOwner = [s \in 1..NUMSEATS |-> -2]
        /\ Tickets = [c \in AllClients |-> {}]
        /\ CState = [c \in 1..NUMCLIENTS |-> "idle"]
        (* Process Server *)
        /\ internalReq = M0
        (* Process HClient *)
        /\ id = [self \in AllHonest |-> self]
        /\ ip = [self \in AllHonest |-> self]
        /\ wantSeat = [self \in AllHonest |-> 1]
        /\ wantSeats = [self \in AllHonest |-> {}]
        /\ k = [self \in AllHonest |-> 0]
        /\ tmp = [self \in AllHonest |-> {}]
        /\ reply = [self \in AllHonest |-> M0]
        /\ target = [self \in AllHonest |-> 0]
        /\ availSeats = [self \in AllHonest |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "s1_"
                                        [] self \in AllHonest -> "InitTarget"]

s1_ == /\ pc[0] = "s1_"
       /\ IF ~AllDone
             THEN /\ pc' = [pc EXCEPT ![0] = "WW"]
             ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
       /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, Tickets, 
                       CState, internalReq, id, ip, wantSeat, wantSeats, k, 
                       tmp, reply, target, availSeats >>

WW == /\ pc[0] = "WW"
      /\ (Len(Channels[0]) > 0 \/ AllDone)
      /\ IF AllDone
            THEN /\ pc' = [pc EXCEPT ![0] = "End"]
            ELSE /\ pc' = [pc EXCEPT ![0] = "GET"]
      /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, Tickets, 
                      CState, internalReq, id, ip, wantSeat, wantSeats, k, tmp, 
                      reply, target, availSeats >>

GET == /\ pc[0] = "GET"
       /\ internalReq' = Head(Channels[0])
       /\ Channels' = [Channels EXCEPT ![0] = Tail(Channels[0])]
       /\ pc' = [pc EXCEPT ![0] = "TREAT"]
       /\ UNCHANGED << BankAccount, seatMap, ResOwner, Tickets, CState, id, ip, 
                       wantSeat, wantSeats, k, tmp, reply, target, availSeats >>

TREAT == /\ pc[0] = "TREAT"
         /\ IF internalReq.type = "reserve"
               THEN /\ IF internalReq.seats # {}
                          /\ AllAvailable(internalReq.seats)
                          THEN /\ seatMap' = SetSeats(seatMap, internalReq.seats, "reserved")
                               /\ ResOwner' = SetOwners(ResOwner, internalReq.seats, internalReq.bankID)
                               /\ Channels' = [Channels EXCEPT ![internalReq.from] = Append(Channels[internalReq.from],
                                                                                            [type |-> "confirm", from |-> 0, seats |-> internalReq.seats, bankID |-> -2])]
                          ELSE /\ Channels' = [Channels EXCEPT ![internalReq.from] = Append(Channels[internalReq.from],
                                                                                            [type |-> "deny", from |-> 0, seats |-> internalReq.seats, bankID |-> -2])]
                               /\ UNCHANGED << seatMap, ResOwner >>
                    /\ UNCHANGED << BankAccount, Tickets >>
               ELSE /\ IF internalReq.type = "cancelRes"
                          THEN /\ IF internalReq.seats # {}
                                     /\ AllReservedBy(internalReq.seats, internalReq.bankID)
                                     THEN /\ seatMap' = SetSeats(seatMap, internalReq.seats, "available")
                                          /\ ResOwner' = SetOwners(ResOwner, internalReq.seats, -2)
                                          /\ Channels' = [Channels EXCEPT ![internalReq.from] = Append(Channels[internalReq.from],
                                                                                                       [type |-> "confirm", from |-> 0, seats |-> internalReq.seats, bankID |-> -2])]
                                     ELSE /\ Channels' = [Channels EXCEPT ![internalReq.from] = Append(Channels[internalReq.from],
                                                                                                       [type |-> "deny", from |-> 0, seats |-> internalReq.seats, bankID |-> -2])]
                                          /\ UNCHANGED << seatMap, ResOwner >>
                               /\ UNCHANGED << BankAccount, Tickets >>
                          ELSE /\ IF internalReq.type = "buy"
                                     THEN /\ IF internalReq.seats # {}
                                                /\ AllReservedBy(internalReq.seats, internalReq.bankID)
                                                /\ BankAccount[internalReq.bankID] >= Cost(internalReq.seats)
                                                THEN /\ seatMap' = SetSeats(seatMap, internalReq.seats, "paid")
                                                     /\ ResOwner' = SetOwners(ResOwner, internalReq.seats, -2)
                                                     /\ BankAccount' = [BankAccount EXCEPT
                                                                         ![internalReq.bankID] = @ - Cost(internalReq.seats),
                                                                         ![0]                 = @ + Cost(internalReq.seats)]
                                                     /\ Tickets' = [Tickets EXCEPT
                                                                     ![internalReq.bankID] = @ \union internalReq.seats]
                                                     /\ Channels' = [Channels EXCEPT ![internalReq.from] = Append(Channels[internalReq.from],
                                                                                                                  [type |-> "confirm", from |-> 0, seats |-> internalReq.seats, bankID |-> -2])]
                                                ELSE /\ Channels' = [Channels EXCEPT ![internalReq.from] = Append(Channels[internalReq.from],
                                                                                                                  [type |-> "deny", from |-> 0, seats |-> internalReq.seats, bankID |-> -2])]
                                                     /\ UNCHANGED << BankAccount, 
                                                                     seatMap, 
                                                                     ResOwner, 
                                                                     Tickets >>
                                     ELSE /\ IF internalReq.type = "cancelPaid"
                                                THEN /\ IF internalReq.seats # {}
                                                           /\ AllPaidBy(internalReq.seats, internalReq.bankID)
                                                           THEN /\ seatMap' = SetSeats(seatMap, internalReq.seats, "available")
                                                                /\ BankAccount' = [BankAccount EXCEPT
                                                                                    ![internalReq.bankID] = @ + Cost(internalReq.seats),
                                                                                    ![0]                 = @ - Cost(internalReq.seats)]
                                                                /\ Tickets' = [Tickets EXCEPT
                                                                                ![internalReq.bankID] = @ \ internalReq.seats]
                                                                /\ Channels' = [Channels EXCEPT ![internalReq.from] = Append(Channels[internalReq.from],
                                                                                                                             [type |-> "confirm", from |-> 0, seats |-> internalReq.seats, bankID |-> -2])]
                                                           ELSE /\ Channels' = [Channels EXCEPT ![internalReq.from] = Append(Channels[internalReq.from],
                                                                                                                             [type |-> "deny", from |-> 0, seats |-> internalReq.seats, bankID |-> -2])]
                                                                /\ UNCHANGED << BankAccount, 
                                                                                seatMap, 
                                                                                Tickets >>
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED << BankAccount, 
                                                                     Channels, 
                                                                     seatMap, 
                                                                     Tickets >>
                                          /\ UNCHANGED ResOwner
         /\ pc' = [pc EXCEPT ![0] = "End"]
         /\ UNCHANGED << CState, internalReq, id, ip, wantSeat, wantSeats, k, 
                         tmp, reply, target, availSeats >>

End == /\ pc[0] = "End"
       /\ TRUE
       /\ pc' = [pc EXCEPT ![0] = "s1_"]
       /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, Tickets, 
                       CState, internalReq, id, ip, wantSeat, wantSeats, k, 
                       tmp, reply, target, availSeats >>

Server == s1_ \/ WW \/ GET \/ TREAT \/ End

InitTarget(self) == /\ pc[self] = "InitTarget"
                    /\ target' = [target EXCEPT ![self] = CHOOSE t \in 1..Min2(INITMONEY, NUMSEATS) : TRUE]
                    /\ pc' = [pc EXCEPT ![self] = "s1"]
                    /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, 
                                    Tickets, CState, internalReq, id, ip, 
                                    wantSeat, wantSeats, k, tmp, reply, 
                                    availSeats >>

s1(self) == /\ pc[self] = "s1"
            /\ IF CState[self] # "done"
                  THEN /\ pc' = [pc EXCEPT ![self] = "CheckDone"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, Tickets, 
                            CState, internalReq, id, ip, wantSeat, wantSeats, 
                            k, tmp, reply, target, availSeats >>

CheckDone(self) == /\ pc[self] = "CheckDone"
                   /\ IF Cardinality(Tickets[self]) >= target[self]
                         \/ (\A s \in Seats : seatMap[s] = "paid")
                         THEN /\ CState' = [CState EXCEPT ![self] = "done"]
                              /\ pc' = [pc EXCEPT ![self] = "s1"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "BWaitIdle"]
                              /\ UNCHANGED CState
                   /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, 
                                   Tickets, internalReq, id, ip, wantSeat, 
                                   wantSeats, k, tmp, reply, target, 
                                   availSeats >>

BWaitIdle(self) == /\ pc[self] = "BWaitIdle"
                   /\ (CState[self] = "idle")
                   /\ pc' = [pc EXCEPT ![self] = "ActionChoice"]
                   /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, 
                                   Tickets, CState, internalReq, id, ip, 
                                   wantSeat, wantSeats, k, tmp, reply, target, 
                                   availSeats >>

ActionChoice(self) == /\ pc[self] = "ActionChoice"
                      /\ IF Tickets[self] = {}
                            THEN /\ pc' = [pc EXCEPT ![self] = "BReserveBuy"]
                            ELSE /\ \/ /\ pc' = [pc EXCEPT ![self] = "BReserveBuy"]
                                    \/ /\ pc' = [pc EXCEPT ![self] = "BCancelPaid"]
                      /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, 
                                      Tickets, CState, internalReq, id, ip, 
                                      wantSeat, wantSeats, k, tmp, reply, 
                                      target, availSeats >>

BReserveBuy(self) == /\ pc[self] = "BReserveBuy"
                     /\ CState' = [CState EXCEPT ![self] = "waiting"]
                     /\ availSeats' = [availSeats EXCEPT ![self] = {s \in Seats : seatMap[s] = "available"}]
                     /\ k' = [k EXCEPT ![self] = Min2(target[self] - Cardinality(Tickets[self]),
                                                      Cardinality(availSeats'[self]))]
                     /\ pc' = [pc EXCEPT ![self] = "Label1"]
                     /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, 
                                     Tickets, internalReq, id, ip, wantSeat, 
                                     wantSeats, tmp, reply, target >>

Label1(self) == /\ pc[self] = "Label1"
                /\ IF k[self] = 0
                      THEN /\ CState' = [CState EXCEPT ![self] = "idle"]
                           /\ pc' = [pc EXCEPT ![self] = "CheckDone"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Label2"]
                           /\ UNCHANGED CState
                /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, 
                                Tickets, internalReq, id, ip, wantSeat, 
                                wantSeats, k, tmp, reply, target, availSeats >>

Label2(self) == /\ pc[self] = "Label2"
                /\ wantSeats' = [wantSeats EXCEPT ![self] = {}]
                /\ tmp' = [tmp EXCEPT ![self] = availSeats[self]]
                /\ pc' = [pc EXCEPT ![self] = "PickLoop"]
                /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, 
                                Tickets, CState, internalReq, id, ip, wantSeat, 
                                k, reply, target, availSeats >>

PickLoop(self) == /\ pc[self] = "PickLoop"
                  /\ IF Cardinality(wantSeats[self]) < k[self]
                        THEN /\ wantSeat' = [wantSeat EXCEPT ![self] = CHOOSE s \in tmp[self] : TRUE]
                             /\ wantSeats' = [wantSeats EXCEPT ![self] = wantSeats[self] \union {wantSeat'[self]}]
                             /\ tmp' = [tmp EXCEPT ![self] = tmp[self] \ {wantSeat'[self]}]
                             /\ pc' = [pc EXCEPT ![self] = "PickLoop"]
                             /\ UNCHANGED Channels
                        ELSE /\ Channels' = [Channels EXCEPT ![0] = Append(Channels[0],
                                                                          [type |-> "reserve",
                                                                           from |-> ip[self],
                                                                           seats |-> wantSeats[self],
                                                                           bankID |-> id[self]])]
                             /\ pc' = [pc EXCEPT ![self] = "WaitResReply"]
                             /\ UNCHANGED << wantSeat, wantSeats, tmp >>
                  /\ UNCHANGED << BankAccount, seatMap, ResOwner, Tickets, 
                                  CState, internalReq, id, ip, k, reply, 
                                  target, availSeats >>

WaitResReply(self) == /\ pc[self] = "WaitResReply"
                      /\ Len(Channels[ip[self]]) > 0
                      /\ reply' = [reply EXCEPT ![self] = Head(Channels[ip[self]])]
                      /\ Channels' = [Channels EXCEPT ![ip[self]] = Tail(Channels[ip[self]])]
                      /\ pc' = [pc EXCEPT ![self] = "Label3"]
                      /\ UNCHANGED << BankAccount, seatMap, ResOwner, Tickets, 
                                      CState, internalReq, id, ip, wantSeat, 
                                      wantSeats, k, tmp, target, availSeats >>

Label3(self) == /\ pc[self] = "Label3"
                /\ IF reply[self].type = "confirm"
                      THEN /\ Channels' = [Channels EXCEPT ![0] = Append(Channels[0],
                                                                        [type |-> "buy",
                                                                         from |-> ip[self],
                                                                         seats |-> wantSeats[self],
                                                                         bankID |-> id[self]])]
                           /\ pc' = [pc EXCEPT ![self] = "WaitBuyReply"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Label4"]
                           /\ UNCHANGED Channels
                /\ UNCHANGED << BankAccount, seatMap, ResOwner, Tickets, 
                                CState, internalReq, id, ip, wantSeat, 
                                wantSeats, k, tmp, reply, target, availSeats >>

WaitBuyReply(self) == /\ pc[self] = "WaitBuyReply"
                      /\ Len(Channels[ip[self]]) > 0
                      /\ reply' = [reply EXCEPT ![self] = Head(Channels[ip[self]])]
                      /\ Channels' = [Channels EXCEPT ![ip[self]] = Tail(Channels[ip[self]])]
                      /\ pc' = [pc EXCEPT ![self] = "Label4"]
                      /\ UNCHANGED << BankAccount, seatMap, ResOwner, Tickets, 
                                      CState, internalReq, id, ip, wantSeat, 
                                      wantSeats, k, tmp, target, availSeats >>

Label4(self) == /\ pc[self] = "Label4"
                /\ CState' = [CState EXCEPT ![self] = "idle"]
                /\ pc' = [pc EXCEPT ![self] = "CheckDone"]
                /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, 
                                Tickets, internalReq, id, ip, wantSeat, 
                                wantSeats, k, tmp, reply, target, availSeats >>

BCancelPaid(self) == /\ pc[self] = "BCancelPaid"
                     /\ IF Tickets[self] = {}
                           THEN /\ CState' = [CState EXCEPT ![self] = "idle"]
                                /\ pc' = [pc EXCEPT ![self] = "CheckDone"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Label5"]
                                /\ UNCHANGED CState
                     /\ UNCHANGED << BankAccount, Channels, seatMap, ResOwner, 
                                     Tickets, internalReq, id, ip, wantSeat, 
                                     wantSeats, k, tmp, reply, target, 
                                     availSeats >>

Label5(self) == /\ pc[self] = "Label5"
                /\ CState' = [CState EXCEPT ![self] = "waiting"]
                /\ wantSeat' = [wantSeat EXCEPT ![self] = CHOOSE s \in Tickets[self] : TRUE]
                /\ wantSeats' = [wantSeats EXCEPT ![self] = {wantSeat'[self]}]
                /\ Channels' = [Channels EXCEPT ![0] = Append(Channels[0],
                                                             [type |-> "cancelPaid",
                                                              from |-> ip[self],
                                                              seats |-> wantSeats'[self],
                                                              bankID |-> id[self]])]
                /\ pc' = [pc EXCEPT ![self] = "WaitCancelReply"]
                /\ UNCHANGED << BankAccount, seatMap, ResOwner, Tickets, 
                                internalReq, id, ip, k, tmp, reply, target, 
                                availSeats >>

WaitCancelReply(self) == /\ pc[self] = "WaitCancelReply"
                         /\ Len(Channels[ip[self]]) > 0
                         /\ reply' = [reply EXCEPT ![self] = Head(Channels[ip[self]])]
                         /\ Channels' = [Channels EXCEPT ![ip[self]] = Tail(Channels[ip[self]])]
                         /\ CState' = [CState EXCEPT ![self] = "idle"]
                         /\ pc' = [pc EXCEPT ![self] = "CheckDone"]
                         /\ UNCHANGED << BankAccount, seatMap, ResOwner, 
                                         Tickets, internalReq, id, ip, 
                                         wantSeat, wantSeats, k, tmp, target, 
                                         availSeats >>

HClient(self) == InitTarget(self) \/ s1(self) \/ CheckDone(self)
                    \/ BWaitIdle(self) \/ ActionChoice(self)
                    \/ BReserveBuy(self) \/ Label1(self) \/ Label2(self)
                    \/ PickLoop(self) \/ WaitResReply(self) \/ Label3(self)
                    \/ WaitBuyReply(self) \/ Label4(self)
                    \/ BCancelPaid(self) \/ Label5(self)
                    \/ WaitCancelReply(self)

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
=============================================================================
