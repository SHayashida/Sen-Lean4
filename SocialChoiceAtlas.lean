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
-- M2 finite semantic obstruction bridge: generic UN + MINLIB instances yield
-- one of O2/O3/O4, and the legacy `(Fin n, Fin m)` theorem is retained as a
-- compatibility corollary. This has NO solver backend and is included in the
-- default build on every PR (see docs/gates/m2/aim_signoff.md, Decision 3).
import SocialChoiceAtlas.Sen.ObstructionBridge
-- M4 Level B right-atom semantic bridge: a semantic-only wrapper and
-- orientation lemma connecting the M4 right atom target to Decisive.
import SocialChoiceAtlas.Sen.RightAtomBridge
import SocialChoiceAtlas.Sen.Lifting.ImpossibilityLift
-- M3 finite-set reportability core: abstract repair/report interfaces,
-- sufficient conditions, exactness under reference monotonicity, and checked
-- boundary examples. Candidate B artifacts are not formalized by these imports.
import SocialChoiceAtlas.Reportability.Defs
import SocialChoiceAtlas.Reportability.Atomic
import SocialChoiceAtlas.Reportability.GroupSound
import SocialChoiceAtlas.Reportability.Monotone
import SocialChoiceAtlas.Reportability.Examples
-- Optional (SAT/BVDecide/LRAT): this is large and solver-backed, so keep it out of default imports.
-- import SocialChoiceAtlas.Sen.BaseCase24.SATSen
