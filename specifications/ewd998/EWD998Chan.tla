----------------------------- MODULE EWD998Chan -----------------------------
(***************************************************************************)
(* TLA+ specification of an algorithm for distributed termination          *)
(* detection on a ring, due to Shmuel Safra, published as EWD 998:         *)
(* Shmuel Safra's version of termination detection.                        *)
(* Contrary to EWD998, this variant models message channels as sequences.  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

------------------------------------------------------------------------------

Contains(s, e) ==
  (**************************************************************************)
  (* TRUE iff the element e \in ToSet(s).                                   *)
  (**************************************************************************)
  \E i \in 1..Len(s) : s[i] = e
  
RemoveAt(s, i) == 
  (**************************************************************************)
  (* Replaces the element at position i shortening the length of s by one.  *)
  (**************************************************************************)
  SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))
  
Reduce(op(_,_), fun, from, to, base) == 
  (**************************************************************************)
  (* Reduce the elements in the range from..to of the function's co-domain. *)
  (**************************************************************************)
  LET reduced[i \in from..to] ==
          IF i = from THEN op(base, fun[i])
          ELSE op(reduced[i - 1], fun[i])
  IN reduced[to]

sum(a, b) ==
  a + b

------------------------------------------------------------------------------

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0} \* At least one node.

Nodes == 0 .. N-1
Color == {"white", "black"}

VARIABLES 
 active,
 color,
 counter,
 inbox
  
vars == <<active, color, counter, inbox>>

TokenMsg == [type : {"tok"}, q : Int, color : Color]
BasicMsg == [type : {"pl"}]
Message == TokenMsg \cup BasicMsg

TypeOK ==
  /\ counter \in [Nodes -> Int]
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ inbox \in [Nodes -> Seq(Message)]
  \* There is always exactly one token (singleton-type).
  /\ \E i \in Nodes : \E j \in 1..Len(inbox[i]): inbox[i][j].type = "tok"
  /\ \A i,j \in Nodes : \A k \in 1 .. Len(inbox[i]) : \A l \in 1 .. Len(inbox[j]) :
        inbox[i][k].type = "tok" /\ inbox[j][l].type = "tok"
        => i = j /\ k = l

------------------------------------------------------------------------------
 
Init ==
  (* Rule 0 *)
  /\ counter = [i \in Nodes |-> 0] \* c properly initialized
  /\ inbox = [i \in Nodes |-> IF i = 0 
                              THEN << [type |-> "tok", q |-> 0, color |-> "black" ] >> 
                              ELSE <<>>] \* with empty channels.
  (* EWD840 *) 
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]

InitiateProbe ==
  (* Rule 1 *)
  /\ \E j \in 1..Len(inbox[0]):
      \* Token is at node 0.
      /\ inbox[0][j].type = "tok"
      /\ \* Previous round inconsistent, if:
         \/ inbox[0][j].color = "black"
         \/ color[0] = "black"
         \* Implicit stated in EWD998 as c0 + q > 0 means that termination has not 
         \* been achieved: Initiate a probe if the token's color is white but the
         \* number of in-flight messages is not zero.
         \/ counter[0] + inbox[0][j].q # 0
      /\ inbox' = [inbox EXCEPT ![N-1] = Append(@, 
           [type |-> "tok", q |-> 0,
             (* Rule 6 *)
             color |-> "white"]), 
             ![0] = RemoveAt(@, j) ] \* consume token message from inbox[0]. 
  (* Rule 6 *)
  /\ color' = [ color EXCEPT ![0] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter>>                            
  
PassToken(i) ==
  (* Rule 2 *)
  /\ ~ active[i] \* If machine i is active, keep the token.
  /\ \E j \in 1..Len(inbox[i]) : 
          /\ inbox[i][j].type = "tok"
          \* the machine nr.i+1 transmits the token to machine nr.i under q := q + c[i+1]
          /\ LET tkn == inbox[i][j]
             IN  inbox' = [inbox EXCEPT ![i-1] = 
                                       Append(@, [tkn EXCEPT !.q = tkn.q + counter[i],
                                                             !.color = IF color[i] = "black"
                                                                       THEN "black"
                                                                       ELSE tkn.color]),
                                    ![i] = RemoveAt(@, j) ] \* pass on the token.
  (* Rule 7 *)
  /\ color' = [ color EXCEPT ![i] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter>>                            

System == \/ InitiateProbe
          \/ \E i \in Nodes \ {0} : PassToken(i)

-----------------------------------------------------------------------------

SendMsg(i) ==
  \* Only allowed to send msgs if node i is active.
  /\ active[i]
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  \* Non-deterministically choose a receiver node.
  /\ \E j \in Nodes \ {i} :
          \* Send a message (not the token) to j.
          /\ inbox' = [inbox EXCEPT ![j] = Append(@, [type |-> "pl" ] ) ]
          \* Note that we don't blacken node i as in EWD840 if node i
          \* sends a message to node j with j > i
  /\ UNCHANGED <<active, color>>                            

RecvMsg(i) ==
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![i] = @ - 1]
  (* Rule 3 *)
  /\ color' = [ color EXCEPT ![i] = "black" ]
  \* Receipt of a message activates i.
  /\ active' = [ active EXCEPT ![i] = TRUE ]
  \* Consume a message (not the token!).
  /\ \E j \in 1..Len(inbox[i]) : 
          /\ inbox[i][j].type = "pl"
          /\ inbox' = [inbox EXCEPT ![i] = RemoveAt(@, j) ]
  /\ UNCHANGED <<>>                           

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, inbox, counter>>

Environment == \E i \in Nodes : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

-----------------------------------------------------------------------------

Next ==
  System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

(***************************************************************************)
(* The number of incoming messages of a node's given inbox.                *)
(***************************************************************************)
NumberOfMsg(ibx) == 
  Len(SelectSeq(ibx, LAMBDA msg: msg.type = "pl"))

(***************************************************************************)
(* Bound the otherwise infinite state space that TLC has to check.         *)
(***************************************************************************)
StateConstraint ==
  /\ \A i \in DOMAIN inbox : NumberOfMsg(inbox[i]) < 3
\*  /\ \A i \in DOMAIN inbox : Len(inbox[i]) < 3
  \* Even with the number of in-flight messages restricted, we need a bound
  \* on the number of messages ever sent to exclude behaviors where two or
  \* more nodes forever alternate between send, receive, send, ...
  /\ \A i \in DOMAIN counter : counter[i] <= 3

-----------------------------------------------------------------------------

(***************************************************************************)
(* tpos \in Nodes s.t. the node's inbox contains the token.                *)
(***************************************************************************)
tpos ==
  CHOOSE i \in Nodes : \E j \in 1..Len(inbox[i]) : inbox[i][j].type = "tok"
 
(***************************************************************************)
(* The q value of the token.                                               *) 
(***************************************************************************)
tq ==
  LET box == CHOOSE i \in 1..Len(inbox[tpos]) : inbox[tpos][i].type = "tok"
  IN inbox[tpos][box].q
\* TLC doesn't evaluate n \in Int unless Int replaced with a def override.
\*  CHOOSE n \in Int : 
\*            \E i \in Nodes : 
\*             \E j \in 1..Len(inbox[i]) : 
\*              /\ inbox[i][j].type = "tok"
\*              /\ inbox[i][j].q = n                                          

(***************************************************************************)
(* Main safety property: if there is a white token at node 0 and there are *)
(* no in-flight messages then every node is inactive.                      *)
(***************************************************************************)
terminationDetected ==
  /\ tpos = 0 \* Redundant because of msg.type = "tok" below.
  /\ \E j \in 1..Len(inbox[0]) : /\ inbox[0][j].type = "tok"
                                 /\ inbox[0][j].color = "white"
                                 \* no messages in-flight.
                                 /\ inbox[0][j].q + counter[0] = 0
  /\ color[0] = "white"
  /\ ~ active[0]

(***************************************************************************)
(* The number of messages on their way. "in-flight"                        *)
(* Contrary to reasoning about the local counter below, this reasoning     *)
(* requires a global view of the world (all channels/inboxes.              *)
(***************************************************************************)
B == 
  Reduce(LAMBDA a, b: a + NumberOfMsg(b), inbox, 0, N-1, 0)

(***************************************************************************)
(***************************************************************************)
TerminationDetection ==
  terminationDetected => /\ \A i \in Nodes : ~ active[i]
                         /\ B = 0 \* No messages in-flight.

(***************************************************************************)
(* Safra's inductive invariant                                             *)
(***************************************************************************)
Inv == 
  /\ P0:: B = Reduce(sum, counter, 0, N-1, 0)
     (* (Ai: t < i < N: machine nr.i is passive) /\ *)
     (* (Si: t < i < N: ci.i) = q *)
  /\ \/ P1:: /\ \A i \in (tpos+1)..N-1: ~ active[i] \* machine nr.i is passive
             /\ IF tpos = N-1 THEN 0 = tq 
                ELSE Reduce(sum, counter, (tpos+1), N-1, 0) = tq
     (* (Si: 0 <= i <= t: c.i) + q > 0. *)
     \/ P2:: Reduce(sum, counter, 0, tpos, 0) + tq > 0
     (* Ei: 0 <= i <= t : machine nr.i is black. *)
     \/ P3:: \E i \in 0..tpos : color[i] = "black"
     (* The token is black. *)
     \/ P4:: \E i \in DOMAIN inbox:
              \E j \in 1..Len(inbox[i]): /\ inbox[i][j].type = "tok"
                                         /\ inbox[i][j].color = "black"

(***************************************************************************)
(* Liveness property: termination is eventually detected.                  *)
(***************************************************************************)
Liveness ==
  (\A i \in Nodes : ~ active[i] /\ B = 0) ~> terminationDetected

-----------------------------------------------------------------------------

(***************************************************************************)
(* EWD998 with channels refines EWD998 that models channels as sets.       *)
(***************************************************************************)
EWD998 == INSTANCE EWD998 WITH token <-
                                  LET tkn == CHOOSE i \in 1 .. Len(inbox[tpos]):
                                                     inbox[tpos][i].type = "tok"
                                  IN  [pos   |-> tpos, 
                                       q     |-> inbox[tpos][tkn].q,
                                       color |-> inbox[tpos][tkn].color],
                               pending <-
                                  [n \in Nodes |-> IF n = tpos 
                                                   THEN Len(inbox[n])-1 
                                                   ELSE Len(inbox[n])]

\* TLC config doesn't accept the expression EWD998!Spec for PROPERTY.
\* Model-checked for N=3 and StateConstraint above on a laptop in ~15min.
EWD998Spec == EWD998!Spec

THEOREM Spec => EWD998Spec

=============================================================================
