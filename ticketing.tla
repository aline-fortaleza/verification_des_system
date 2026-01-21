----------------------------- MODULE ticketing -----------------------------
\* Change for later: CHOOSE m \in 1..INITMONEY : TRUE

EXTENDS Integers, TLC, Sequences, FiniteSets, helpers

CONSTANTS NUMCLIENTS, MALICIOUS, NUMSEATS, INITMONEY

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
        s1: while (TRUE) {
            \* Wait for a message to process
            WW: 
            await (Len(Channels[ip]) > 0);
            \* Read the first inline
            GET:
            internalReq := Head(Channels[ip]); \* Dequeue the message
            Channels[ip] := Tail(Channels[ip]); \* Remove the processed message from the queue
            
            TREAT:
            if (internalReq.type = "buy"){
                if (seatMap[internalReq.seat] = "available" 
                    /\ BankAccount[internalReq.bankID] > 0) {
                    seatMap[internalReq.seat] := "paid";
                    BankAccount := [BankAccount EXCEPT ![internalReq.bankID] = BankAccount[internalReq.bankID] - 1,
                                                       ![0] = BankAccount[0] + 1];
                    Channels[internalReq.from] := Append(Channels[internalReq.from], 
                                                [type |-> "confirm", 
                                                 from |-> 0, 
                                                 seat |-> internalReq.seat, 
                                                 bankID |-> -2]);
                }
                else {
                    Channels[internalReq.from] := Append(Channels[internalReq.from], 
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
                    Channels[internalReq.from] := Append(Channels[internalReq.from], 
                                                 [type |-> "confirm", 
                                                  from |-> 0, 
                                                  seat |-> internalReq.seat, 
                                                  bankID |-> id]);
                } else {
                    Channels[internalReq.from] := Append(Channels[internalReq.from], 
                                                 [type |-> "deny", 
                                                  from |-> 0, 
                                                  seat |-> internalReq.seat, 
                                                  bankID |-> id]);
                } \* didn't check the id -> someone who isn't the buyer can cancel the ticket
            }
            \* Ignore other message types
        }
    }

    fair process (HClient \in AllHonest) 
        variables tickets = {};
        id = self; \* Client's BankID
        ip = self; \* Client's IP address
        state = "idle"; \* Client's state
        wantSeat = 1; \* Seat the client wants to buy/cancel
        reply = M0; \* Dummy var
        lastReqType = "buy"; 
    {
        s1: while (TRUE) {
            
            either{
                \* Buy branch
                await (state = "idle");
                state := "waiting";
                \* Choose a seat to buy
                wantSeat := CHOOSE s \in Seats : TRUE;
                lastReqType := "buy";
                \* Send buy request to server
                Channels[0] := Append(Channels[0], 
                                     [type |-> "buy", 
                                      from |-> ip, 
                                      seat |-> wantSeat, 
                                      bankID |-> id]);
                \* Wait for server response
                await (Len(Channels[ip]) > 0);
                reply := Head(Channels[ip]);
                Channels[ip] := Tail(Channels[ip]);

                \* Updatre local state
                if (reply.type = "confirm") {
                    tickets := tickets \union {reply.seat};
                };
                state := "idle";
            } or {
                \* Cancel branch
                await (state = "idle" /\ tickets # {});
                state := "waiting";

                wantSeat := CHOOSE s \in tickets : TRUE;
                lastReqType := "cancel";

                Channels[0] := Append(Channels[0], 
                                     [type |-> "cancel", 
                                      from |-> ip, 
                                      seat |-> wantSeat, 
                                      bankID |-> id]);

                await (Len(Channels[ip]) > 0);
                reply := Head(Channels[ip]);
                Channels[ip] := Tail(Channels[ip]);

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
