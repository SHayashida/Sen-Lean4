# Candidate B Claim Boundary

## Allowed statement

> Candidate B is an artifact-defined M3-B instantiation under the declared bundled contract.

The frozen tables support the following finite, contract-relative statements:

- the fully active bundled and split cases are recorded UNSAT;
- all 15 proper block-aligned residuals are recorded SAT/SAT;
- the raw minimal repairs are the five singleton implementation deletions;
- raw repair transport is non-canonical because the two-lever `minlib` block
  does not remain a raw minimal repair while either decisive-voter singleton
  does;
- touch-any grouping yields the four singleton contract repairs;
- direct GroupSoundness, deletion monotonicity, and pointwise grouped
  correctness pass exhaustively over the declared finite sets.

## Guarantee ceiling

This package does not claim that:

- Candidate B is Lean-verified;
- Candidate B establishes semantic validity of any contract atom;
- M3 proves correctness of the CNF generator, solver, or evidence tables;
- M3 proves end-to-end repair correctness;
- `no_cycle4` is full `SocialAcyclic`, or `no_cycle3` is active here;
- the bundled grouping is normatively canonical;
- the finite result establishes family-scale validity, practical prevalence,
  or generality;
- the CPP manuscript is accepted or submission-ready.

The Lean binding checks the abstract theorem core and its allowed axioms. It
does not import, define, or prove Candidate B.
