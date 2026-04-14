# Lab1b — Metal Reports: Abstraction, Refinement & Proof

This folder contains a **simplified** version of the Lab1a metal reports
algorithm together with an abstract specification, a refinement mapping,
and TLAPS-verified invariant proofs.

## Simplifications relative to Lab1a

| Aspect | Lab1a | Lab1b (this folder) |
|---|---|---|
| Per-metal tracking | `[Users -> [Metals -> Report]]` (nested) | Dropped — one report per user |
| State representation | Single record-valued function | Two separate variables: `reportStatus`, `reportQty` |
| Quantity aggregation | `RECURSIVE SumQty`, `totalQty` variable | Removed |
| Price tracking | Weighted-average price calculation | Removed |

These simplifications were necessary to stay within the capabilities of
TLAPS/Z3: the SMT backend cannot handle tuple-indexed function `EXCEPT`
or record-valued functions within the default timeout.

## Files

| File | Purpose |
|---|---|
| `metal_reports.tla` | Simplified concrete spec (5 actions, 2 variables) |
| `metal_reports.cfg` | TLC config for the concrete spec |
| `metal_reports_abstract.tla` | Abstract lifecycle spec (`none -> active -> decided`) |
| `metal_reports_abstract.cfg` | TLC config for the abstract spec |
| `metal_reports_refinement.tla` | Refinement mapping **and** TLAPS proofs |
| `metal_reports_refinement.cfg` | TLC config for refinement checking |

## Abstraction levels

### Concrete (`metal_reports.tla`)

Two state variables per user:

* `reportStatus[u]` in `{NONE, DRAFT, SUBMITTED, APPROVED, REJECTED}`
* `reportQty[u]` in `Nat`

Actions: `CreateDraft`, `AmendDraft`, `SubmitReport`, `ApproveReport`,
`RejectReport`.

### Abstract (`metal_reports_abstract.tla`)

One state variable per user:

* `reportLifecycle[u]` in `{none, active, decided}`

Actions: `CreateReport` (none -> active), `DecideReport` (active -> decided).

### Refinement mapping

Defined in `metal_reports_refinement.tla`:

```
reportLifecycle[u] ==
    IF reportStatus[u] = "NONE"                          THEN "none"
    ELSE IF reportStatus[u] \in {"APPROVED", "REJECTED"} THEN "decided"
    ELSE "active"
```

## Proved invariants

Both proofs are in `metal_reports_refinement.tla` and verified by TLAPS
(81/81 obligations, Z3 backend).

1. **TypeOK** (inductive) — `reportStatus` maps users to valid status
   strings; `reportQty` maps users to natural numbers.

2. **QtyPositive** — every user with a non-NONE report has `reportQty >= 1`.
   Uses TypeOK as a supporting invariant (provides domain information
   required by the Z3 EXCEPT axiom).

## Running

```bash
# TLAPS proofs
tlapm metal_reports_refinement.tla
```
