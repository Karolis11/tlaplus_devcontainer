---- MODULE metal_reports_abstract ----
\* Abstract lifecycle model of the metal reports workflow.
\* Each user's report lifecycle: none -> active -> decided.
\* Abstracts away quantity, draft/submit distinction, and approve vs reject.
CONSTANTS Users

VARIABLES reportLifecycle

vars == <<reportLifecycle>>

TypeOK ==
    reportLifecycle \in [Users -> {"none", "active", "decided"}]

Init ==
    reportLifecycle = [u \in Users |-> "none"]

\* A report is created (abstracts CreateDraft)
CreateReport(u) ==
    /\ reportLifecycle[u] = "none"
    /\ reportLifecycle' = [reportLifecycle EXCEPT ![u] = "active"]

\* A report is decided (abstracts Approve/Reject)
DecideReport(u) ==
    /\ reportLifecycle[u] = "active"
    /\ reportLifecycle' = [reportLifecycle EXCEPT ![u] = "decided"]

Next ==
    \E u \in Users :
        \/ CreateReport(u)
        \/ DecideReport(u)

Spec == Init /\ [][Next]_vars

\* Safety: once decided, a report stays decided
DecidedIsFinal ==
    \A u \in Users :
        reportLifecycle[u] = "decided" => reportLifecycle'[u] = "decided"

P_DecidedIsFinal == [][DecidedIsFinal]_vars

====
