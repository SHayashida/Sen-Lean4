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
-- Optional (SAT/BVDecide/LRAT): this is large and solver-backed, so keep it out of default imports.
-- import SocialChoiceAtlas.Sen.BaseCase24.SATSen
