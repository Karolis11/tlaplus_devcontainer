---- MODULE metal_reports ----
EXTENDS Naturals, FiniteSets

CONSTANTS Users, Supervisor, MaxQty, MaxTotalQty, MaxPrice, Metals, WorkflowStates

Report == [qty: 0..MaxTotalQty, price: 0..MaxPrice, status: WorkflowStates]
EmptyReport == [qty |-> 0, price |-> 0, status |-> "DRAFT"]
MaxUserTotal == MaxTotalQty * Cardinality(Metals)

VARIABLES reports, totalQty

Vars == <<reports, totalQty>>

RECURSIVE SumQty(_, _, _)
SumQty(rs, u, ms) ==
    IF ms = {} THEN 0
    ELSE
        LET m == CHOOSE x \in ms: TRUE
        IN rs[u][m].qty + SumQty(rs, u, ms \ {m})

TotalsFromReports(rs) == [u \in Users |-> SumQty(rs, u, Metals)]

Init ==
    /\ reports = [u \in Users |-> [m \in Metals |-> EmptyReport]]
    /\ totalQty = [u \in Users |-> 0]

CreateDraft(u, m, q, p) ==
    /\ u \in Users
    /\ m \in Metals
    /\ q \in 1..MaxQty
    /\ p \in 0..MaxPrice
    /\ reports[u][m] = EmptyReport
    /\ reports' = [reports EXCEPT ![u][m] = [qty |-> q, price |-> p, status |-> "DRAFT"]]
    /\ totalQty' = TotalsFromReports(reports')

AmendDraft(u, m, q, p) ==
    /\ u \in Users
    /\ m \in Metals
    /\ q \in 1..MaxQty
    /\ p \in 0..MaxPrice
    /\ reports[u][m] # EmptyReport
    /\ reports[u][m].status = "DRAFT"
    /\ LET old == reports[u][m]
           newQty == old.qty + q
           newPrice == (old.price * old.qty + p * q) \div newQty
       IN /\ newQty <= MaxTotalQty
          /\ reports' = [reports EXCEPT ![u][m] = [qty |-> newQty, price |-> newPrice, status |-> "DRAFT"]]
          /\ totalQty' = TotalsFromReports(reports')

SubmitReport(u, m) ==
    /\ u \in Users
    /\ m \in Metals
    /\ reports[u][m] # EmptyReport
    /\ reports[u][m].status = "DRAFT"
    /\ reports' = [reports EXCEPT ![u][m].status = "SUBMITTED"]
    /\ UNCHANGED totalQty

ApproveReport(a, u, m) ==
    /\ a = Supervisor
    /\ u \in Users
    /\ m \in Metals
    /\ reports[u][m] # EmptyReport
    /\ reports[u][m].status = "SUBMITTED"
    /\ reports' = [reports EXCEPT ![u][m].status = "APPROVED"]
    /\ UNCHANGED totalQty

RejectReport(a, u, m) ==
    /\ a = Supervisor
    /\ u \in Users
    /\ m \in Metals
    /\ reports[u][m] # EmptyReport
    /\ reports[u][m].status = "SUBMITTED"
    /\ reports' = [reports EXCEPT ![u][m].status = "REJECTED"]
    /\ UNCHANGED totalQty

Next ==
    \/ \E u \in Users, m \in Metals, q \in 1..MaxQty, p \in 0..MaxPrice:
        CreateDraft(u, m, q, p)
    \/ \E u \in Users, m \in Metals, q \in 1..MaxQty, p \in 0..MaxPrice:
        AmendDraft(u, m, q, p)
    \/ \E u \in Users, m \in Metals:
        SubmitReport(u, m)
    \/ \E u \in Users, m \in Metals:
        ApproveReport(Supervisor, u, m)
    \/ \E u \in Users, m \in Metals:
        RejectReport(Supervisor, u, m)
    \/ UNCHANGED Vars

Spec == Init /\ [][Next]_Vars

\* All the reports exists and totalQty for every user is whithin a range
TypeOK ==
    /\ reports \in [Users -> [Metals -> Report]]
    /\ totalQty \in [Users -> 0..MaxUserTotal]

AggregateConsistent == totalQty = TotalsFromReports(reports)

HasReport(u, m) == reports[u][m] # EmptyReport

QtyPositive ==
    \A u \in Users, m \in Metals :
        HasReport(u, m) => reports[u][m].qty >= 1

QtyNotNegative ==
    \A u \in Users, m \in Metals :
        ~HasReport(u, m) => reports[u][m].qty = 0

QtyWithinLimit ==
    \A u \in Users, m \in Metals :
        HasReport(u, m) => reports[u][m].qty <= MaxTotalQty

PriceWithinLimit ==
    \A u \in Users, m \in Metals :
        HasReport(u, m) => reports[u][m].price \in 0..MaxPrice

IfSubmittedThenApproved == 
    [] (\A u \in Users, m \in Metals :
        reports[u][m].status = "SUBMITTED" => <> (reports[u][m].status = "APPROVED"))

EveryReportForOneMetal ==
    \E m \in Metals, \A u \in user : reports

StatusValid ==
    \A u \in Users, m \in Metals :
        HasReport(u, m) => reports[u][m].status \in WorkflowStates

StatusValidExists ==
    \A u \in Users, m \in Metals :
        \E s \in WorkflowStates : reports[u][m].status = s

NoReportDisappears ==
    \A u \in Users, m \in Metals :
        HasReport(u, m) => reports'[u][m] # EmptyReport

QtyNeverDecreases ==
    \A u \in Users, m \in Metals :
        HasReport(u, m) => reports'[u][m].qty >= reports[u][m].qty

ApprovedOnlyFromSubmitted ==
    \A u \in Users, m \in Metals :
        /\ reports'[u][m].status = "APPROVED"
        /\ reports[u][m].status # "APPROVED"
        => reports[u][m].status = "SUBMITTED"

RejectedOnlyFromSubmitted ==
    \A u \in Users, m \in Metals :
        /\ reports'[u][m].status = "REJECTED"
        /\ reports[u][m].status # "REJECTED"
        => reports[u][m].status = "SUBMITTED"

SubmittedOnlyFromDraft ==
    \A u \in Users, m \in Metals :
        /\ reports'[u][m].status = "SUBMITTED"
        /\ reports[u][m].status # "SUBMITTED"
        => reports[u][m].status = "DRAFT"

ApprovedRejectedNoChange ==
    \A u \in Users, m \in Metals :
        reports[u][m].status \in {"APPROVED", "REJECTED"} => reports'[u][m] = reports[u][m]

SubmittedNoChange ==
    \A u \in Users, m \in Metals :
        reports[u][m].status = "SUBMITTED" => 
        /\ reports'[u][m].qty = reports[u][m].qty
        /\ reports'[u][m].price = reports[u][m].price

P_NoReportDisappears == [][NoReportDisappears]_Vars
P_QtyNeverDecreases == [][QtyNeverDecreases]_Vars
P_ApprovedOnlyFromSubmitted == [][ApprovedOnlyFromSubmitted]_Vars
P_RejectedOnlyFromSubmitted == [][RejectedOnlyFromSubmitted]_Vars
P_SubmittedOnlyFromDraft == [][SubmittedOnlyFromDraft]_Vars
P_ApprovedRejectedNoChange == [][ApprovedRejectedNoChange]_Vars
P_SubmittedNoChange == [][SubmittedNoChange]_Vars

====
