/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Languages.OmegaLanguage
public import Mathlib.Topology.Closure

/-!
# Safety and Liveness properties of ω-sequences

This file formalizes the main results of [AlpernSchneider1985].  Namely, given
an appropriate topology on ω-sequences:
* Safety properties can be identified with closed sets.
* Liveness properties can be identified with dense sets.
* Every property is the intersection of a safety property and a liveness property.

## References
* [Alpern, Bowen; Schneider, Fred B. (1985). "Defining liveness".
Information Processing Letters. 21 (4): 181–185.][AlpernSchneider1985]
-/

@[expose] public section

namespace Cslib.ωLanguage

open Set ωSequence TopologicalSpace

variable {α : Type*}

/-- Safety properties are identified with closed sets. -/
abbrev IsSafety (p : ωLanguage α) : Prop := IsClosed p.toSet

/-- An alternative characterization of `IsSafety` that justifies its definition:
if an ω-sequence violates a safety property, then it has a finite prefix all of whose
infinite extensions also violate the property. -/
theorem isSafety_iff (p : ωLanguage α) :
    p.IsSafety ↔ ∀ xs, xs ∉ p → ∃ n, ∀ ys, (xs.take n) ++ω ys ∉ p := by
  simp [← isOpen_compl_iff, isOpen_iff, mem_def]

/-- Liveness properties are identified with dense sets. -/
abbrev IsLiveness (p : ωLanguage α) : Prop := Dense p.toSet

/-- An alternative characterization of `IsLiveness` that justifies its definition:
any finite sequence can be extended to an infinite sequence satisfying a liveness property. -/
theorem isLiveness_iff (p : ωLanguage α) :
    p.IsLiveness ↔ ∀ (xs : ωSequence α) (n : ℕ), ∃ ys, (xs.take n) ++ω ys ∈ p := by
  exact dense_iff p.toSet

/-- `p.closure` is always a safety property for any ω-language `p`. -/
theorem isSafety_closure (p : ωLanguage α) :
    p.closure.IsSafety := by
  exact isClosed_closure

/-- `p ⊔ p.closureᶜ` is always a liveness property for any ω-language `p`. -/
theorem isLiveness_sup_compl_closure (p : ωLanguage α) :
    (p ⊔ p.closureᶜ).IsLiveness := by
  simp only [sup_def, closure, compl_def, dense_iff_closure_eq, closure_union,
    ← compl_subset_iff_union, subset_closure]

/-- Every property `p` is the intersection of a safety property (namely, `p.closure`) and
a liveness property (namely, `p ⊔ p.closureᶜ`). -/
theorem exists_safetyLivenessDecomposition (p : ωLanguage α) :
    ∃ q r : ωLanguage α, q.IsSafety ∧ r.IsLiveness ∧ p = q ⊓ r := by
  use p.closure, p ⊔ p.closureᶜ
  split_ands
  · exact isSafety_closure p
  · exact isLiveness_sup_compl_closure p
  · simp [sup_def, closure, compl_def, inf_def, inter_union_distrib_left, subset_closure]

end Cslib.ωLanguage
