-- SocialChoiceAtlas: A Lean 4 library for computational social choice theory
-- Focus: Sen's "Impossibility of a Paretian Liberal"

import SocialChoiceAtlas.Core.Basics
import SocialChoiceAtlas.Core.Ranking
import SocialChoiceAtlas.Core.Profile
import SocialChoiceAtlas.Axioms.Pareto
import SocialChoiceAtlas.Axioms.Liberalism
import SocialChoiceAtlas.Axioms.Rationality
import SocialChoiceAtlas.Sen.BaseCase24.Spec
import SocialChoiceAtlas.Sen.BaseCase24.Theorem
-- M2 Transfer Contract: pure-Lean lift of Sen's impossibility from the
-- `(Fin 2, Fin 4)` base case to `(Fin n, Fin m)` with `2 ≤ n`, `4 ≤ m`.
-- This module has NO solver backend and is included in the default build
-- on every PR (see docs/gates/m2/aim_signoff.md, Decision 3).
import SocialChoiceAtlas.Sen.Lifting.ImpossibilityLift
-- Optional (SAT/BVDecide/LRAT): this is large and solver-backed, so keep it out of default imports.
-- import SocialChoiceAtlas.Sen.BaseCase24.SATSen
