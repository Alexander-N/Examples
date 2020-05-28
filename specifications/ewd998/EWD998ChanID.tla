---------------------------- MODULE EWD998ChanID ----------------------------
(***************************************************************************)
(* TLA+ specification of an algorithm for distributed termination          *)
(* detection on a ring, due to Shmuel Safra, published as EWD 998:         *)
(* Shmuel Safra's version of termination detection.                        *)
(* Contrary to EWD998, this variant models message channels as sequences.  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, Naturals

------------------------------------------------------------------------------

RemoveAt(s, i) == 
  (**************************************************************************)
  (* Replaces the element at position i shortening the length of s by one.  *)
  (**************************************************************************)
  SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))

Range(f) ==
  { f[x] : x \in DOMAIN f }

\* No support for RECURSIVE in PlusPy.
IsSimpleCycle(S, r) ==
  (* View r as a graph s.t. S is the graph's set of vertices and there 
     exists an edge from s to t iff f[s] = t. IsFiniteSet(DOMAIN r). *)
  LET 
   F[ i \in 1..Cardinality(S) ] == 
         IF i = 1 THEN << CHOOSE s \in S : TRUE >>
         ELSE LET seq == F[i-1]
                  head == Head(seq)
              IN << r[head] >> \o F[i-1]
  IN Range(F[Cardinality(S)]) = S
         
------------------------------------------------------------------------------

CONSTANT Nodes
ASSUME IsFiniteSet(Nodes) /\ Nodes # {}

N == Cardinality(Nodes)
ASSUME NAssumption == N \in Nat \ {0} \* At least one node (a little bit of 
                                      \* redundancy can't hurt, a little bit 
                                      \* of redundancy can't hurt).

\* Choose a node to be the initiator of a fresh token. We don't care which one it
\* is as long as it is always the same.
Initiator == CHOOSE n \in Nodes : TRUE
                                         
\* Organize Nodes in a ring. 
RingOfNodes == 
  CHOOSE r \in [ Nodes -> Nodes ]: IsSimpleCycle(Nodes, r)

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
  /\ counter = [n \in Nodes |-> 0] \* c properly initialized
  /\ inbox = [n \in Nodes |-> IF n = Initiator 
                              THEN << [type |-> "tok", q |-> 0, color |-> "black" ] >> 
                              ELSE <<>>] \* with empty channels.
  (* EWD840 *) 
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]

InitiateProbe ==
  (* Rule 1 *)
  /\ \E j \in 1..Len(inbox[Initiator]):
      \* Token is at node the Initiator.
      /\ inbox[Initiator][j].type = "tok"
      /\ \* Previous round inconsistent, if:
         \/ inbox[Initiator][j].color = "black"
         \/ color[Initiator] = "black"
         \* Implicit stated in EWD998 as c0 + q > 0 means that termination has not 
         \* been achieved: Initiate a probe if the token's color is white but the
         \* number of in-flight messages is not zero.
         \/ counter[Initiator] + inbox[Initiator][j].q # 0
      /\ inbox' = [inbox EXCEPT ![RingOfNodes[Initiator]] = Append(@, 
           [type |-> "tok", q |-> 0,
             (* Rule 6 *)
             color |-> "white"]), 
             ![Initiator] = RemoveAt(@, j) ] \* consume token message from inbox[0]. 
  (* Rule 6 *)
  /\ color' = [ color EXCEPT ![Initiator] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter>>                            
  
PassToken(n) ==
  (* Rule 2 *)
  /\ ~ active[n] \* If machine i is active, keep the token.
  /\ \E j \in 1..Len(inbox[n]) : 
          /\ inbox[n][j].type = "tok"
          \* the machine nr.i+1 transmits the token to machine nr.i under q := q + c[i+1]
          /\ LET tkn == inbox[n][j]
             IN  inbox' = [inbox EXCEPT ![RingOfNodes[n]] = 
                                       Append(@, [tkn EXCEPT !.q = tkn.q + counter[n],
                                                             !.color = IF color[n] = "black"
                                                                       THEN "black"
                                                                       ELSE tkn.color]),
                                    ![n] = RemoveAt(@, j) ] \* pass on the token.
  (* Rule 7 *)
  /\ color' = [ color EXCEPT ![n] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter>>                            

System == \/ InitiateProbe
          \/ \E n \in Nodes \ {Initiator} : PassToken(n)

-----------------------------------------------------------------------------

SendMsg(n) ==
  \* Only allowed to send msgs if node i is active.
  /\ active[n]
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![n] = @ + 1]
  \* Non-deterministically choose a receiver node.
  /\ \E j \in Nodes \ {n} :
          \* Send a message (not the token) to j.
          /\ inbox' = [inbox EXCEPT ![j] = Append(@, [type |-> "pl" ] ) ]
          \* Note that we don't blacken node i as in EWD840 if node i
          \* sends a message to node j with j > i
  /\ UNCHANGED <<active, color>>                            

\* RecvMsg could write the incoming message to a (Java) buffer from which the (Java) implementation consumes it. 
RecvMsg(n) ==
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![n] = @ - 1]
  (* Rule 3 *)
  /\ color' = [ color EXCEPT ![n] = "black" ]
  \* Receipt of a message activates node n.
  /\ active' = [ active EXCEPT ![n] = TRUE ]
  \* Consume a message (not the token!).
  /\ \E j \in 1..Len(inbox[n]) : 
          /\ inbox[n][j].type = "pl"
          /\ inbox' = [inbox EXCEPT ![n] = RemoveAt(@, j) ]
  /\ UNCHANGED <<>>                           

Deactivate(n) ==
  /\ active[n]
  /\ active' = [active EXCEPT ![n] = FALSE]
  /\ UNCHANGED <<color, inbox, counter>>

Environment == \E n \in Nodes : SendMsg(n) \/ RecvMsg(n) \/ Deactivate(n)

-----------------------------------------------------------------------------

Next ==
  System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
\* The definitions of the refinement mapping below this line will be
\* ignored by PlusPy.  It can thus make use of RECURSIVE.
\*++:Spec
  
nat2node[i \in 0..N-1 ] == 
  LET RECURSIVE Op(_,_,_)
      Op(p, cnt, nd) ==
         IF p = cnt THEN nd
         ELSE Op(p, cnt - 1, RingOfNodes[nd])
  IN Op(i, N-1, RingOfNodes[Initiator])

Node2Nat(fcn) ==
  [ i \in 0..N-1 |->  fcn[nat2node[i]] ]

(***************************************************************************)
(* EWD998ChanID (identifier) refines EWD998Chan where nodes are modelled   *)
(* with naturals \in 0..N-1. To check that EWD998ChanID is a correct       *)
(* refinement _and_ to save us the troubles of rewriting the (inductive)   *)
(* Inv for identifiers, we have TLC check the two theorems below.          *)
(***************************************************************************)
EWD998 == INSTANCE EWD998Chan WITH active <- Node2Nat(active),
                                   color <- Node2Nat(color),
                                   counter <- Node2Nat(counter),
                                   inbox <- Node2Nat(inbox)

EWD998Spec == EWD998!Spec
THEOREM Spec => EWD998Spec

Inv == EWD998!Inv
THEOREM Spec => Inv

=============================================================================
