# No-Cycle Interpretation Note
## Step 0.5 audit trail

This note records the interpretive resolution adopted after Step 0.

---

## What Step 0 established

Step 0 established the engineering facts:

- the repository now has a parametric finite schema,
- the five levers can be generated for `(2,4)`, `(2,5)`, and `(3,4)`,
- the generalized auditor validates those generated CNFs,
- `no_cycle3` and `no_cycle4` are schema-uniform local clause families across the tested cases.

In other words, the remaining issue after Step 0 was **not** schema identity.

---

## What remained interpretive at Step 0.5

At `m=5`, the conjunction `no_cycle3 ∧ no_cycle4` still permits length-5 cycles.
So even though the local clause families are uniform, their effective strength differs from the `m=4` case.

The open question was therefore:

> Should Step 0.5 resolve this by changing the encoding now, or by restricting claim scope?

---

## Chosen resolution

Step 0.5 resolves the issue by **explicit scope restriction**.

The adopted policy is:

> Any Candidate A evidence obtained using `no_cycle3` and `no_cycle4` is interpreted only within the local-rationality family defined by those clause families. It is not, at Step 0.5, evidence about full `SocialAcyclic` or about stronger rationality encodings.

This keeps the experiment usable without pretending that the current encoding captures full acyclicity at `m=5`.

---

## Why scope restriction is the right choice here

- Step 0 already delivered the schema and audit work needed for trustworthy comparison.
- The remaining issue is interpretive, not mechanical.
- Replacing the encoding in Step 0.5 would change the experiment definition rather than merely clarifying its meaning.
- The restricted-scope reading is precise, auditable, and sufficient for running the current protocol without overclaim.

---

## Future work

Future work may introduce a **stronger rationality encoding** if the project later wants claims about full acyclicity families rather than the current local-rationality family.

If that happens:

- the generator and auditor would need a new rationality lever family,
- the semantics memo would need a new sign-off pass,
- Candidate A results would need to be reinterpreted relative to that stronger family.
