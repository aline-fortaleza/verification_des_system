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
                                      
                BWaitReply:
                \* Wait for server response
                await (Len(Channels[ip]) > 0);
                reply := Head(Channels[ip]);
                Channels[ip] := Tail(Channels[ip]);

                BUpdate:
                if (reply.type = "confirm") {
                    tickets := tickets \union {reply.seat};
                };
                state := "idle";
            } or {
                \* Cancel branch
                CWaitIdle:
                await (state = "idle" /\ tickets # {});
                
                CSend:
                state := "waiting";
                wantSeat := CHOOSE s \in tickets : TRUE;
                lastReqType := "cancel";

                Channels[0] := Append(Channels[0], 
                                     [type |-> "cancel", 
                                      from |-> ip, 
                                      seat |-> wantSeat, 
                                      bankID |-> id]);
                                      
                CWaitReply:
                await (Len(Channels[ip]) > 0);
                reply := Head(Channels[ip]);
                Channels[ip] := Tail(Channels[ip]);

                CUpdate
                if (reply.type = "confirm") {
                    tickets := tickets \ {wantSeat};
                };
                state := "idle";
            }
        }
    }
} *)

\* END TRANSLATION 

=============================================================================


