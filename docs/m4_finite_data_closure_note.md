# M4 Finite-Data Closure Note

Status: finite-data closure / docs-only
Depends on: Certificate 1, Mask-Shape Collapse Law audit, Certificate 2 checker
Current authorization: closure note only
Not authorized: checker implementation, solver rerun, Lean theorem, 3-voter run, warrant-contract implementation, paper-claim promotion

## 1. Closure Decision

Decision:
The M4 finite-data side is CLOSED / PASS.

Under the declared selector-free semantic encoding, the project has a complete
finite-data certificate for the Sen24 bundled-mask x obstruction-shape phase
diagram.

The closure is finite-data closure only.
It is not Lean closure, paper closure, semantic encoding correctness closure,
or family-scale closure.

The next phase should not reopen the finite-data pipeline unless a new scope
decision changes the domain.

## 2. Exact Achievement

Under the declared selector-free semantic encoding, M4 completely
machine-audits the Sen24 bundled-mask x obstruction-shape phase diagram: all
48 minlib-active cells are covered; all 18 UNSAT cells satisfy repair-orbit
exactness and shape-blind support truncation; all 30 SAT cells satisfy active
RepairEmpty; no MIXED_WITHIN_SHAPE or UNKNOWN cells remain; and the analysis
remains non-circular because T is a bundled mask/schema while Shape(W) is an
internal analysis coordinate.

Audited counts:

```text
total cells = 48
ALL_UNSAT cells = 18
ALL_SAT cells = 30
MIXED_WITHIN_SHAPE cells = 0
UNKNOWN cells = 0
repair objects = 816
repair orbits = 46
cell report fibers = 46
shape-blind fibers = 33
```

## 3. Certificate Chain

Final pipeline:

```text
Certificate 1:
  bundled-mask coverage and cell-status phase diagram.

Certificate 1b:
  exploratory Mask-Shape Collapse Law audit.

Certificate 2:
  complete finite-data phase-diagram certificate:
    - SAT-cell active RepairEmpty;
    - UNSAT-cell orbit-fiber exactness;
    - orbit-stabilizer;
    - shape-blind support truncation;
    - Certificate 3/4 obligations absorbed as subchecks;
    - non-circularity.
```

There is no independent Certificate 3 or Certificate 4 stage after
consolidation.
Their obligations are internal Certificate 2 subchecks.

## 4. Final Finite-Data Claim

Final finite-data claim:

Under the declared selector-free semantic encoding, for the Sen24 bundled-mask
x obstruction-shape phase diagram:

1. If `CellStatus(T,s)=ALL_UNSAT`, then every cell-indexed grouped-report
   fiber is exactly one complete repair orbit, and every shape-blind grouped
   report satisfies support truncation over UNSAT support.

2. If `CellStatus(T,s)=ALL_SAT`, then `RepairEmpty(T,s)` holds.

3. No cell is `UNKNOWN` or `MIXED_WITHIN_SHAPE` in the certified domain.

4. The finite certificate preserves the non-circular discipline:
   `T` is mask/schema identity;
   `Shape(W)` is computed from `W`;
   `Cell(T,s)` is an analysis stratum;
   `ResidualClass` is not defined by collapse behavior.

This is not a Lean theorem.

## 5. What the Certificate Proves

The finite-data certificate proves, in the sense of complete machine-checked
finite enumeration over the declared artifacts, that the M4 phase diagram is
closed:

- SAT side: active repair-empty verification.
- UNSAT side: repair-orbit exactness.
- Shape-blind side: support truncation.
- Metadata side: non-circularity guard.

This is stronger than the earlier ALL_W_UNSAT-only reading.
ALL_W_UNSAT masks are now a special case of the 48-cell phase diagram.
MIXED masks are not discarded; they are support-truncated regimes.

## 6. What the Certificate Does Not Prove

The certificate does not prove:

- structural necessity of the Mask-Shape Collapse Law;
- that the collapse law follows abstractly from Sen24 without enumeration;
- semantic encoding correctness beyond the declared audit assumptions;
- semantic-to-CNF correctness;
- Lean theorem status;
- general Sen theorem status;
- Arrow or Gibbard-Satterthwaite transfer;
- 3-voter or family-scale generalization.

## 7. Eliminated Objections and Audit Evidence

| objection | resolution | evidence |
| --- | --- | --- |
| This is only two cases. | Replaced ALL_W_UNSAT-only scope with the 48-cell mask x shape phase diagram; MIXED regimes are integrated as support truncation. | Certificate 1b and Certificate 2 counts: 48 cells, 18 UNSAT, 30 SAT. |
| MIXED means repair geometry breaks. | MIXED means support truncation; UNSAT cells inside MIXED masks satisfy the same exactness/support law. | Mask-Shape Collapse Law audit; Certificate 2 support truncation `PASS`. |
| The result is circular because shape defines the theory. | `T` remains bundled mask/schema; `Shape(W)` is computed from `W`; `Cell(T,s)` is an analysis stratum; `ResidualClass` is not defined by collapse law. | Certificate 2 non-circularity `PASS`. |
| SAT cells were ignored. | SAT cells are first-class `RepairEmpty` cells and are actively verified. | Certificate 2 RepairEmpty `PASS` over 30 SAT cells. |
| Collapse is caused by partial orbit fragments or fiber artifacts. | Every cell-indexed grouped-report fiber is exactly one complete repair orbit; no partial orbit fragments. | Certificate 2 orbit-fiber exactness `PASS`. |
| Old Certificate 3/4 obligations remain unverified. | They are absorbed into Certificate 2 as shape-blind support and support-truncation subchecks. | Certificate 2 absorption `PASS`. |

## 8. Why This Is Not Merely Sen Confirmation

Sen's liberal paradox establishes an impossibility boundary.
This M4 finite-data closure does not merely reconfirm that boundary.
It resolves the internal structure of the Sen24 declared encoding: which
bundled residual masks and witness shapes are inconsistent, which are
satisfiable, and how grouped repair reports collapse repair orbits in every
inconsistent cell.

This is not a new general Sen theorem.
It is a complete computational internal resolution of the declared Sen24 phase
diagram.

## 9. Remaining Later Phases

Remaining work is split into two tracks.

## 10. Mainline Track X: Audit Completion

Track X is the recommended mainline.

Goal:
close M4 as a methodology-completion result: a complete machine-audited
internal resolution of the Sen24 phase diagram under declared encoding
assumptions.

Remaining work:

1. State the semantic encoding boundary at the front of the paper.
2. Optionally formalize or package the finite-data certificate in Lean /
   proof-carrying form.
3. Write the paper around the audited phase diagram.
4. Keep structural necessity and family-scale generalization as future work.

## 11. Optional Track Y: Structural Theorem

Track Y is optional future work.

Goal:
explain why the Mask-Shape Collapse Law holds structurally, beyond finite
enumeration.

Possible obligations:

- derive collapse count from group action and support pattern;
- explain why blind_orbit_count equals shape_support_count;
- generalize beyond Sen24 if possible;
- formalize the structural theorem in Lean.

Track Y is not required for finite-data closure.

## 12. Non-Claims

This closure note does not claim:

- Lean theorem;
- paper-ready theorem;
- general Sen theorem;
- Arrow theorem;
- Gibbard-Satterthwaite theorem;
- 3-voter theorem;
- family-scale theorem;
- warrant-contract semantics;
- semantic-to-CNF correctness theorem;
- semantic encoding correctness beyond declared audit assumptions;
- structural necessity of the Mask-Shape Collapse Law;
- that finite-data closure is the same as structural theorem closure.

## 13. Next Authorized Action

The next authorized action is review of this finite-data closure note.

After review, Track X should proceed as the audit-completion mainline unless a
new scope decision changes the M4 finite-data domain. Track Y remains optional
future work and is not required to preserve finite-data closure.

## 14. Semantic Encoding Boundary

The finite-data closure is under the declared selector-free semantic encoding.
The correspondence between M4 `right(voter,pair)` atoms and Lean `Decisive` is
auditable and structurally aligned, but not yet a Lean-proved bridge theorem.

See `docs/m4_semantic_encoding_boundary.md`.

## 15. Right-Atom Bridge Feasibility

The finite-data closure remains valid under the declared selector-free
semantic encoding. A follow-up feasibility note identifies a possible minimal
Lean semantic bridge for the central `right_atom` / `Decisive` alignment,
while keeping full semantic-to-CNF correctness as future work.

See `docs/m4_right_atom_decisive_bridge_feasibility.md`.

## Paper Claim Scaffold Follow-up

A paper-facing claim scaffold has been added to fix M4's presentation as an
auditable formal-methods methodology contribution.

See `docs/m4_paper_claim_scaffold.md`.
