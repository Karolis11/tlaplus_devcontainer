---- MODULE metal_reports_refinement ----
EXTENDS Naturals, TLAPS

CONSTANTS Users, MaxQty, MaxTotalQty

VARIABLES reportStatus, reportQty

vars == <<reportStatus, reportQty>>

MR == INSTANCE metal_reports

Spec == MR!Spec

reportLifecycle == [u \in Users |->
    IF reportStatus[u] = "NONE" THEN "none"
    ELSE IF reportStatus[u] \in {"APPROVED", "REJECTED"} THEN "decided"
    ELSE "active"]

Abs == INSTANCE metal_reports_abstract WITH reportLifecycle <- reportLifecycle

THEOREM Refinement == MR!Spec => Abs!Spec
    OMITTED

Init ==
    /\ reportStatus = [u \in Users |-> "NONE"]
    /\ reportQty = [u \in Users |-> 0]

CreateDraft(u, q) ==
    /\ reportStatus[u] = "NONE"
    /\ q >= 1
    /\ q <= MaxTotalQty
    /\ reportStatus' = [reportStatus EXCEPT ![u] = "DRAFT"]
    /\ reportQty' = [reportQty EXCEPT ![u] = q]

AmendDraft(u, q) ==
    /\ reportStatus[u] = "DRAFT"
    /\ q >= 1
    /\ reportQty[u] + q <= MaxTotalQty
    /\ reportQty' = [reportQty EXCEPT ![u] = reportQty[u] + q]
    /\ UNCHANGED reportStatus

SubmitReport(u) ==
    /\ reportStatus[u] = "DRAFT"
    /\ reportStatus' = [reportStatus EXCEPT ![u] = "SUBMITTED"]
    /\ UNCHANGED reportQty

ApproveReport(u) ==
    /\ reportStatus[u] = "SUBMITTED"
    /\ reportStatus' = [reportStatus EXCEPT ![u] = "APPROVED"]
    /\ UNCHANGED reportQty

RejectReport(u) ==
    /\ reportStatus[u] = "SUBMITTED"
    /\ reportStatus' = [reportStatus EXCEPT ![u] = "REJECTED"]
    /\ UNCHANGED reportQty

Next ==
    \/ \E u \in Users, q \in 1..MaxQty : CreateDraft(u, q)
    \/ \E u \in Users, q \in 1..MaxQty : AmendDraft(u, q)
    \/ \E u \in Users : SubmitReport(u)
    \/ \E u \in Users : ApproveReport(u)
    \/ \E u \in Users : RejectReport(u)

TypeOK ==
    /\ reportStatus \in [Users -> {"NONE","DRAFT","SUBMITTED","APPROVED","REJECTED"}]
    /\ reportQty \in [Users -> 0..MaxTotalQty]

QtyPositive ==
    \A u \in Users : reportStatus[u] # "NONE" => reportQty[u] >= 1

LocalSpec == Init /\ [][Next]_vars

\* Proof: TypeOK is inductive 
THEOREM TypeInvariantLocal ==
    ASSUME MaxQty \in Nat /\ MaxTotalQty \in Nat /\ MaxQty >= 1
    PROVE LocalSpec => []TypeOK
    <1>1. Init => TypeOK
        BY DEF Init, TypeOK
    <1>2. TypeOK /\ [Next]_vars => TypeOK'
        <2>1. SUFFICES ASSUME TypeOK, [Next]_vars PROVE TypeOK'
            OBVIOUS
        <2>2. CASE \E u \in Users, q \in 1..MaxQty : CreateDraft(u, q)
            BY <2>1, <2>2, SMT DEF TypeOK, CreateDraft
        <2>3. CASE \E u \in Users, q \in 1..MaxQty : AmendDraft(u, q)
            BY <2>1, <2>3, SMT DEF TypeOK, AmendDraft
        <2>4. CASE \E u \in Users : SubmitReport(u)
            BY <2>1, <2>4, SMT DEF TypeOK, SubmitReport
        <2>5. CASE \E u \in Users : ApproveReport(u)
            BY <2>1, <2>5, SMT DEF TypeOK, ApproveReport
        <2>6. CASE \E u \in Users : RejectReport(u)
            BY <2>1, <2>6, SMT DEF TypeOK, RejectReport
        <2>7. CASE UNCHANGED vars
            BY <2>1, <2>7, SMT DEF TypeOK, vars
        <2>q. QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
    <1>q. QED BY <1>1, <1>2, PTL DEF LocalSpec

====
