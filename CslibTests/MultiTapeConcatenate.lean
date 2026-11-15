/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Concatenate
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id

namespace CslibTests.MultiTapeConcatenate

open Turing.MultiTapeTM

-- Concatenating two identity computations duplicates a word with zero work space.
example : ComputableInTimeAndSpace (fun w : List Bool => w ++ w)
    (Function.Embedding.refl _) (Function.Embedding.refl _)
    (fun w => 3 * w.length + 5) (fun _ => 0) := by
  refine ((computableInTimeAndSpace_id (enc := Function.Embedding.refl (List Bool))).concatenate
    (computableInTimeAndSpace_id (enc := Function.Embedding.refl (List Bool)))
    (fun _ => rfl)).mono ?_ (fun _ => le_rfl)
  intro w
  simp
  lia

end CslibTests.MultiTapeConcatenate
