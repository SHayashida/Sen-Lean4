/-
Copyright (c) 2026 SocialChoiceAtlas Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SocialChoiceAtlas Contributors
-/
import SocialChoiceAtlas.Sen.ObstructionSoundness

/-!
# Sen Obstruction Bridge, Stage 3

This module composes the Stage 1 witness/classification layer and the Stage 2
shape-soundness layer into the generic semantic obstruction bridge:

```text
UN + MINLIB
  -> ClassifiedSenRightsWitness
  -> SenOutcomeObstruction
  -> not SocialAcyclic
```

The phrase "finite semantic obstruction basis" denotes a complete finite
generating family of semantic obstruction shapes:

* O2: support cardinality 2, strict conflict.
* O3: support cardinality 3, 3-cycle.
* O4: support cardinality 4, 4-cycle.

No minimality or irredundancy theorem is claimed.

The obstruction is a semantic object. It is not a CNF clause family, not an
LRAT certificate, not a literal restricted SWF, and not a theorem obtained by
treating the Sen24 artifact itself as a formal input. The general theorem is
connected to the Sen24 proof pattern through the shared bounded semantic
obstruction shapes.
-/

namespace SocialChoiceAtlas.Sen

open SocialChoiceAtlas

universe u v

variable {Voter : Type u} {Alt : Type v} [DecidableEq Alt] [Fintype Alt]

/--
Stage-3 outcome bridge: `UN` and `MINLIB` produce a semantic Sen outcome
obstruction by extracting a classified rights witness and applying the
O2/O3/O4 soundness theorem.
-/
theorem sen_outcome_obstruction_of_UN_MINLIB
    (F : SWF Voter Alt)
    (hUN : UN F)
    (hMINLIB : MINLIB F) :
    SenOutcomeObstruction F := by
  rcases exists_classified_senRightsWitness F hMINLIB with ⟨cw⟩
  exact outcome_of_classifiedWitness F hUN cw

/--
Generic Sen impossibility from the finite semantic obstruction basis.

The theorem assumes an arbitrary voter type and a finite alternative type. It
does not require `Voter` to be finite, and it has no explicit lower-bound
hypotheses such as `2 ≤ n` or `4 ≤ m`.
-/
theorem sen_impossibility_from_obstruction_basis
    (F : SWF Voter Alt)
    (hUN : UN F)
    (hMINLIB : MINLIB F) :
    ¬ SocialAcyclic F :=
  (sen_outcome_obstruction_of_UN_MINLIB F hUN hMINLIB).refutes_socialAcyclic

end SocialChoiceAtlas.Sen
