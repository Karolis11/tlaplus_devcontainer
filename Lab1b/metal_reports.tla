---- MODULE metal_reports ----
\* Simplified metal reports workflow.
\* Each user may create, amend, submit, and have approved/rejected a single report.
\* Simplification of Lab1a: dropped per-metal dimension and record-valued reports
\* in favour of separate variables for status and quantity.
EXTENDS Naturals

CONSTANTS Users, MaxQty, MaxTotalQty

VARIABLES reportStatus, reportQty

vars == <<reportStatus, reportQty>>

Init ==
    /\ reportStatus = [u \in Users |-> "NONE"]
    /\ reportQty = [u \in Users |-> 0]

\* Create a new draft report with initial quantity q >= 1
CreateDraft(u, q) ==
    /\ reportStatus[u] = "NONE"
    /\ q >= 1
    /\ reportStatus' = [reportStatus EXCEPT ![u] = "DRAFT"]
    /\ reportQty' = [reportQty EXCEPT ![u] = q]

\* Amend a draft: add extra quantity (report stays in DRAFT)
AmendDraft(u, q) ==
    /\ reportStatus[u] = "DRAFT"
    /\ q >= 1
    /\ reportQty[u] + q <= MaxTotalQty
    /\ reportQty' = [reportQty EXCEPT ![u] = reportQty[u] + q]
    /\ UNCHANGED reportStatus

\* Submit the draft for approval
SubmitReport(u) ==
    /\ reportStatus[u] = "DRAFT"
    /\ reportStatus' = [reportStatus EXCEPT ![u] = "SUBMITTED"]
    /\ UNCHANGED reportQty

\* Approve a submitted report
ApproveReport(u) ==
    /\ reportStatus[u] = "SUBMITTED"
    /\ reportStatus' = [reportStatus EXCEPT ![u] = "APPROVED"]
    /\ UNCHANGED reportQty

\* Reject a submitted report
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

Spec == Init /\ [][Next]_vars

\* ----- Invariants -----
TypeOK ==
    /\ reportStatus \in [Users -> {"NONE","DRAFT","SUBMITTED","APPROVED","REJECTED"}]
    /\ reportQty \in [Users -> 0..MaxTotalQty]

QtyPositive ==
    \A u \in Users : reportStatus[u] # "NONE" => reportQty[u] >= 1

====
