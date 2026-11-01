/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Languages.Congruences.MyhillCongruence

/-! # Syntactic monoid

This file has two main results:
(1) We define the syntactic monoid of a language `l` and show that `l` is regular
if and only if its syntactic monoid is finite.
(2) Using (1), we show that a language is regular if and only if it is the preimage of a subset
of a finite monoid `M` under a monoid homomorphism from the free monoid on its alphabet to `M`

## References

[Holcombe1982] Holcombe, W.M.L. (1982). Algebraic automata theory. Section 5.3
-/

@[expose] public section

variable {α : Type}

namespace Language

open Cslib.Language FreeMonoid

/-- Converting a (two-sided) congruence `c` on finite words to a congruence relation
on the (multiplicative) free monoid. -/
def Congruence.toCon [c : Congruence α] : Con (FreeMonoid α) where
  r x y := c.r x.toList y.toList
  iseqv.refl _ := c.iseqv.refl _
  iseqv.symm := c.iseqv.symm
  iseqv.trans := c.iseqv.trans
  mul' {w x y z} h_wx h_yz := by
    have h_wyxy : c.r (w * y).toList (x * y).toList := c.right_cov.elim y.toList h_wx
    have h_xyxz : c.r (x * y).toList (x * z).toList := c.left_cov.elim x.toList h_yz
    exact c.iseqv.trans h_wyxy h_xyxz

/-- The syntactic monoid of a language `l` is the quotient of the free monoid
by the Myhill congruence of `l`. -/
abbrev SyntacticMonoid (l : Language α) := l.MyhillCongruence.toCon.Quotient

/-- The natural homomorphism from `FreeMonoid α` to `l.SyntacticMonoid` induced
by the Myhill congruence of `l`. -/
abbrev homSyntacticMonoid (l : Language α) := l.MyhillCongruence.toCon.mk'

/-- The syntactic monoid of a language `l` and its Myhill quotient are the quotients of
`FreeMonoid α` and of `List α` by the same relation, hence in bijection. -/
def syntacticMonoidEquivMyhillQuotient (l : Language α) :
    l.SyntacticMonoid ≃ l.MyhillQuotient :=
  Quotient.congr FreeMonoid.toListEquiv fun _ _ ↦ Iff.rfl

/-- A language `l` is regular if and only if its syntactic monoid is finite. -/
theorem IsRegular.iff_finite_syntacticMonoid (l : Language α) :
    l.IsRegular ↔ Finite (l.SyntacticMonoid) :=
  (IsRegular.iff_finite_myhillQuotient l).trans
    (l.syntacticMonoidEquivMyhillQuotient.finite_iff).symm

/-- The congruence induced by `homSyntacticMonoid` is exactly the Myhill congruence. -/
theorem homSyntacticMonoid_iff_myhillCongruence {l : Language α} {x y : List α} :
    l.homSyntacticMonoid (ofList x) = l.homSyntacticMonoid (ofList y) ↔
    l.MyhillCongruence.eq x y := by
  simp only [Con.coe_mk', Con.eq]
  rfl

/-- Any regular language is the preimage of a subset of a finite monoid `M`
under a monoid homomorphism from the free monoid on its alphabet to `M`. -/
theorem IsRegular.exists_finite_monoid {l : Language α} (h : l.IsRegular) :
    ∃ M : Type, ∃ _ : Monoid M, ∃ _ : Finite M, ∃ f : FreeMonoid α →* M, ∃ s : Set M,
    (f ∘ ofList) ⁻¹' s = l := by
  use l.SyntacticMonoid, Con.monoid _, (iff_finite_syntacticMonoid l).mp h,
    l.homSyntacticMonoid, (l.homSyntacticMonoid ∘ ofList) '' l
  apply le_antisymm
  · rintro x ⟨y, hy, heq⟩
    have heq := homSyntacticMonoid_iff_myhillCongruence.mp heq
    specialize heq [] []
    simp only [List.nil_append, List.append_nil] at heq
    exact heq.mp hy
  · exact Set.subset_preimage_image _ _

section FiniteMonoid

variable {M : Type*} [Monoid M] (f : FreeMonoid α →* M)

/-- Given a monoid homomorphism `f` from `FreeMonoid α` to another monoid `M`,
`inducedCongr f` is the language congruence induced by `f`. -/
-- NOTE: This is in fact a two-sided congruence, but we need only the `RightCongruence` part here.
@[implicit_reducible]
def inducedCongr : RightCongruence α where
  eq := Setoid.ker (f ∘ ofList)
  right_cov.elim := by
    intro x y z
    simp only [Setoid.ker_def, Function.comp_apply, ofList_append, map_mul]
    grind

instance [Finite M] : Finite (Quotient (inducedCongr f).eq) :=
  Finite.of_equiv _ (Setoid.quotientKerEquivRange (f ∘ ofList)).symm

theorem inducedCongr_ofList (x : List α) :
    (f ∘ ofList) ⁻¹' {(f ∘ ofList) x} = (inducedCongr f).eqvCls ⟦ x ⟧ := by
  ext y
  simp [Quotient.eq]

/-- The preimage of a singleton in a finite monoid `M` under a monoid homomorphism
from the free monoid to `M` is regular. -/
theorem IsRegular.of_finite_monoid_singleton [Finite M]
    (m : M) : IsRegular ((f ∘ ofList) ⁻¹' {m}) := by
  by_cases h : (f ∘ ofList) ⁻¹' {m} = ∅
  · rw [h]
    exact IsRegular.zero
  · obtain ⟨x, rfl⟩ := Set.nonempty_iff_ne_empty.mpr h
    rw [inducedCongr_ofList]
    exact IsRegular.congr_fin_index (c := inducedCongr f) _

/-- The preimage of a subset of a finite monoid `M` under a monoid homomorphism
from the free monoid to `M` is regular. -/
theorem IsRegular.of_finite_monoid [Finite M]
    (s : Set M) : IsRegular ((f ∘ ofList) ⁻¹' s) := by
  have h : (f ∘ ofList) ⁻¹' s = ⨆ m ∈ s, (f ∘ ofList) ⁻¹' {m} := by
    simp only [Set.iSup_eq_iUnion, Set.biUnion_preimage_singleton]
  rw [h]
  apply IsRegular.iSup
  simp [IsRegular.of_finite_monoid_singleton]

end FiniteMonoid

/-- A language is regular if and only if it is the preimage of a subset of a finite monoid `M`
under a monoid homomorphism from the free monoid on its alphabet to `M`. -/
theorem IsRegular.iff_finite_monoid {l : Language α} :
    l.IsRegular ↔
    ∃ M : Type, ∃ _ : Monoid M, ∃ _ : Finite M, ∃ f : FreeMonoid α →* M, ∃ s : Set M,
    (f ∘ ofList) ⁻¹' s = l := by
  apply Iff.intro
  case mp =>
    intro h
    exact IsRegular.exists_finite_monoid h
  case mpr =>
    rintro ⟨M, _, _, f, s, rfl⟩
    exact IsRegular.of_finite_monoid f s

end Language
