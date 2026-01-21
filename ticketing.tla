----------------------------- MODULE ticketing -----------------------------
\* Change for later: CHOOSE m \in 1..INITMONEY : TRUE

EXTENDS Integers, TLC, Sequences, FiniteSets

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
                BWaitIdle:
                \* Buy branch
                await (state = "idle");
                
                BSend:
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
                                      
                BWaitRead:
                \* Wait for server response
                await (Len(Channels[ip]) > 0);
                reply := Head(Channels[ip]);
                
                BPop:
                Channels[ip] := Tail(Channels[ip]);
                
                
                BUpdate:
                \* Updatre local state
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

                CUpdate:
                if (reply.type = "confirm") {
                    tickets := tickets \ {wantSeat};
                };
                state := "idle";
            }
        }
    }
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "471539c" /\ chksum(tla) = "4bb3c908")
\* Label s1 of process Server at line 50 col 13 changed to s1_
\* Process variable id of process Server at line 46 col 9 changed to id_
\* Process variable ip of process Server at line 47 col 9 changed to ip_
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

VARIABLES seatMap, id_, ip_, internalReq, tickets, id, ip, state, wantSeat, 
          reply, lastReqType

vars == << BankAccount, Channels, pc, seatMap, id_, ip_, internalReq, tickets, 
           id, ip, state, wantSeat, reply, lastReqType >>

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
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "s1_"
                                        [] self \in AllHonest -> "s1"]

s1_ == /\ pc[0] = "s1_"
       /\ pc' = [pc EXCEPT ![0] = "WW"]
       /\ UNCHANGED << BankAccount, Channels, seatMap, id_, ip_, internalReq, 
                       tickets, id, ip, state, wantSeat, reply, lastReqType >>

WW == /\ pc[0] = "WW"
      /\ (Len(Channels[ip_]) > 0)
      /\ pc' = [pc EXCEPT ![0] = "GET"]
      /\ UNCHANGED << BankAccount, Channels, seatMap, id_, ip_, internalReq, 
                      tickets, id, ip, state, wantSeat, reply, lastReqType >>

GET == /\ pc[0] = "GET"
       /\ internalReq' = Head(Channels[ip_])
       /\ Channels' = [Channels EXCEPT ![ip_] = Tail(Channels[ip_])]
       /\ pc' = [pc EXCEPT ![0] = "TREAT"]
       /\ UNCHANGED << BankAccount, seatMap, id_, ip_, tickets, id, ip, state, 
                       wantSeat, reply, lastReqType >>

TREAT == /\ pc[0] = "TREAT"
         /\ IF internalReq.type = "buy"
               THEN /\ IF seatMap[internalReq.seat] = "available"
                          /\ BankAccount[internalReq.bankID] > 0
                          THEN /\ seatMap' = [seatMap EXCEPT ![internalReq.seat] = "paid"]
                               /\ BankAccount' = [BankAccount EXCEPT ![internalReq.bankID] = BankAccount[internalReq.bankID] - 1,
                                                                     ![0] = BankAccount[0] + 1]
                               /\ Channels' = [Channels EXCEPT ![internalReq.from] =   Append(Channels[internalReq.from],
                                                                                     [type |-> "confirm",
                                                                                      from |-> 0,
                                                                                      seat |-> internalReq.seat,
                                                                                      bankID |-> -2])]
                          ELSE /\ Channels' = [Channels EXCEPT ![internalReq.from] =   Append(Channels[internalReq.from],
                                                                                     [type |-> "deny",
                                                                                      from |-> 0,
                                                                                      seat |-> internalReq.seat,
                                                                                      bankID |-> -2])]
                               /\ UNCHANGED << BankAccount, seatMap >>
               ELSE /\ IF internalReq.type = "cancel"
                          THEN /\ IF seatMap[internalReq.seat] = "paid"
                                     THEN /\ seatMap' = [seatMap EXCEPT ![internalReq.seat] = "available"]
                                          /\ BankAccount' = [BankAccount EXCEPT ![internalReq.bankID] = BankAccount[internalReq.bankID] + 1,
                                                                                ![0] = BankAccount[0] - 1]
                                          /\ Channels' = [Channels EXCEPT ![internalReq.from] =  Append(Channels[internalReq.from],
                                                                                                [type |-> "confirm",
                                                                                                 from |-> 0,
                                                                                                 seat |-> internalReq.seat,
                                                                                                 bankID |-> id_])]
                                     ELSE /\ Channels' = [Channels EXCEPT ![internalReq.from] =  Append(Channels[internalReq.from],
                                                                                                [type |-> "deny",
                                                                                                 from |-> 0,
                                                                                                 seat |-> internalReq.seat,
                                                                                                 bankID |-> id_])]
                                          /\ UNCHANGED << BankAccount, seatMap >>
                          ELSE /\ TRUE
                               /\ UNCHANGED << BankAccount, Channels, seatMap >>
         /\ pc' = [pc EXCEPT ![0] = "s1_"]
         /\ UNCHANGED << id_, ip_, internalReq, tickets, id, ip, state, 
                         wantSeat, reply, lastReqType >>

Server == s1_ \/ WW \/ GET \/ TREAT

s1(self) == /\ pc[self] = "s1"
            /\ \/ /\ pc' = [pc EXCEPT ![self] = "BWaitIdle"]
               \/ /\ pc' = [pc EXCEPT ![self] = "CWaitIdle"]
            /\ UNCHANGED << BankAccount, Channels, seatMap, id_, ip_, 
                            internalReq, tickets, id, ip, state, wantSeat, 
                            reply, lastReqType >>

BWaitIdle(self) == /\ pc[self] = "BWaitIdle"
                   /\ (state[self] = "idle")
                   /\ pc' = [pc EXCEPT ![self] = "BSend"]
                   /\ UNCHANGED << BankAccount, Channels, seatMap, id_, ip_, 
                                   internalReq, tickets, id, ip, state, 
                                   wantSeat, reply, lastReqType >>

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
                               tickets, id, ip, reply >>

BWaitRead(self) == /\ pc[self] = "BWaitRead"
                   /\ (Len(Channels[ip[self]]) > 0)
                   /\ reply' = [reply EXCEPT ![self] = Head(Channels[ip[self]])]
                   /\ pc' = [pc EXCEPT ![self] = "BPop"]
                   /\ UNCHANGED << BankAccount, Channels, seatMap, id_, ip_, 
                                   internalReq, tickets, id, ip, state, 
                                   wantSeat, lastReqType >>

BPop(self) == /\ pc[self] = "BPop"
              /\ Channels' = [Channels EXCEPT ![ip[self]] = Tail(Channels[ip[self]])]
              /\ pc' = [pc EXCEPT ![self] = "BUpdate"]
              /\ UNCHANGED << BankAccount, seatMap, id_, ip_, internalReq, 
                              tickets, id, ip, state, wantSeat, reply, 
                              lastReqType >>

BUpdate(self) == /\ pc[self] = "BUpdate"
                 /\ IF reply[self].type = "confirm"
                       THEN /\ tickets' = [tickets EXCEPT ![self] = tickets[self] \union {reply[self].seat}]
                       ELSE /\ TRUE
                            /\ UNCHANGED tickets
                 /\ state' = [state EXCEPT ![self] = "idle"]
                 /\ pc' = [pc EXCEPT ![self] = "s1"]
                 /\ UNCHANGED << BankAccount, Channels, seatMap, id_, ip_, 
                                 internalReq, id, ip, wantSeat, reply, 
                                 lastReqType >>

CWaitIdle(self) == /\ pc[self] = "CWaitIdle"
                   /\ (state[self] = "idle" /\ tickets[self] # {})
                   /\ pc' = [pc EXCEPT ![self] = "CSend"]
                   /\ UNCHANGED << BankAccount, Channels, seatMap, id_, ip_, 
                                   internalReq, tickets, id, ip, state, 
                                   wantSeat, reply, lastReqType >>

CSend(self) == /\ pc[self] = "CSend"
               /\ state' = [state EXCEPT ![self] = "waiting"]
               /\ wantSeat' = [wantSeat EXCEPT ![self] = CHOOSE s \in tickets[self] : TRUE]
               /\ lastReqType' = [lastReqType EXCEPT ![self] = "cancel"]
               /\ Channels' = [Channels EXCEPT ![0] = Append(Channels[0],
                                                            [type |-> "cancel",
                                                             from |-> ip[self],
                                                             seat |-> wantSeat'[self],
                                                             bankID |-> id[self]])]
               /\ pc' = [pc EXCEPT ![self] = "CWaitReply"]
               /\ UNCHANGED << BankAccount, seatMap, id_, ip_, internalReq, 
                               tickets, id, ip, reply >>

CWaitReply(self) == /\ pc[self] = "CWaitReply"
                    /\ (Len(Channels[ip[self]]) > 0)
                    /\ reply' = [reply EXCEPT ![self] = Head(Channels[ip[self]])]
                    /\ Channels' = [Channels EXCEPT ![ip[self]] = Tail(Channels[ip[self]])]
                    /\ pc' = [pc EXCEPT ![self] = "CUpdate"]
                    /\ UNCHANGED << BankAccount, seatMap, id_, ip_, 
                                    internalReq, tickets, id, ip, state, 
                                    wantSeat, lastReqType >>

CUpdate(self) == /\ pc[self] = "CUpdate"
                 /\ IF reply[self].type = "confirm"
                       THEN /\ tickets' = [tickets EXCEPT ![self] = tickets[self] \ {wantSeat[self]}]
                       ELSE /\ TRUE
                            /\ UNCHANGED tickets
                 /\ state' = [state EXCEPT ![self] = "idle"]
                 /\ pc' = [pc EXCEPT ![self] = "s1"]
                 /\ UNCHANGED << BankAccount, Channels, seatMap, id_, ip_, 
                                 internalReq, id, ip, wantSeat, reply, 
                                 lastReqType >>

HClient(self) == s1(self) \/ BWaitIdle(self) \/ BSend(self)
                    \/ BWaitRead(self) \/ BPop(self) \/ BUpdate(self)
                    \/ CWaitIdle(self) \/ CSend(self) \/ CWaitReply(self)
                    \/ CUpdate(self)

Next == Server
           \/ (\E self \in AllHonest: HClient(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Server)
        /\ \A self \in AllHonest : WF_vars(HClient(self))

\* END TRANSLATION 

\* END TRANSLATION 

=============================================================================
