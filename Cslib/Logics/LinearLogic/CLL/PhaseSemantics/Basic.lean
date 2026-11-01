/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Bhavik Mehta
-/

module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Order.Closure
public import Cslib.Logics.LinearLogic.CLL.Basic

/-!
# Phase semantics for Classical Linear Logic

This file develops the phase semantics for Classical Linear Logic (CLL), providing an
algebraic interpretation of linear logic propositions in terms of phase spaces.

Phase semantics is a denotational semantics for linear logic where
propositions are interpreted as subsets of a commutative monoid, and logical operations
correspond to specific set-theoretic operations.

## Main definitions

* `PhaseSpace`: A commutative monoid equipped with a distinguished subset ⊥
* `PhaseSpace.imp`: Linear implication `X ⊸ Y` between sets in a phase space
* `PhaseSpace.orthogonal`: The orthogonal `X⫠` of a set X
* `PhaseSpace.isFact`: A fact is a set that equals its biorthogonal closure
* `Fact`: The type of facts in a phase space
* `PhaseSpace.FactExpr`: Inductive type for representing operations on facts
* `PhaseSpace.interpret`: Interpretation of the connectives on facts
* `PhaseSpace.interpProp`: Interpretation of CLL propositions as facts in a phase space

## Main results

* `PhaseSpace.biorthogonalClosure`: The biorthogonal operation forms a closure operator
* `PhaseSpace.orth_iUnion`: Orthogonal of union equals intersection of orthogonals
* `PhaseSpace.sInf_isFact` and `PhaseSpace.inter_isFact_of_isFact`: Facts are closed under
  intersections
* `PhaseSpace.biorth_least_fact`: The biorthogonal closure gives the smallest fact containing a set

Several lemmas about facts and orthogonality useful in the proof of soundness are proven here.

## TODO
- Soundness theorem
- Completeness theorem

## References

* [J.-Y. Girard, *Linear logic*][Girard1987]
* [J.-Y. Girard, *Linear Logic: its syntax and semantics*][Girard1995]
-/

@[expose] public section

namespace Cslib.Logic.CLL

universe u v

open scoped Pointwise
open Set

attribute [scoped grind _=_] Set.le_iff_subset

/--
A phase space is a commutative monoid M equipped with a distinguished subset ⊥.
This forms the algebraic foundation for interpreting linear logic propositions.
-/
class PhaseSpace (M : Type u) extends CommMonoid M where
  /-- The distinguished subset ⊥ used to define orthogonality -/
  bot : Set M

namespace PhaseSpace

variable {P : Type*} [PhaseSpace P] {p q : P}

/-! ## Basic operations -/

/--
Implication between two sets in a phase space: the set of elements `m` such that
for all `x ∈ X`, we have `m * x ∈ Y`.
-/
def imp [PhaseSpace M] (X Y : Set M) : Set M := {m | ∀ x ∈ X, m * x ∈ Y}

/-- The orthogonal `X⫠` of a set X: the set of elements that map X into ⊥ under multiplication. -/
def orthogonal (G : Set P) : Set P :=
  imp G PhaseSpace.bot

@[inherit_doc] scoped postfix:max "⫠" => orthogonal

/-! ## Properties of orthogonality -/

@[scoped grind =, simp] lemma orthogonal_def (X : Set P) : X⫠ = {m | ∀ x ∈ X, m * x ∈ bot} := rfl

/-- The orthogonal operation is antitone: if X ⊆ Y then Y⫠ ⊆ X⫠. -/
lemma orth_antitone {X Y : Set P} (hXY : X ⊆ Y) : Y⫠ ⊆ X⫠ := by grind

/-- The biorthogonal operation is extensive: X ⊆ X⫠⫠ for any set X. -/
lemma orth_extensive (X : Set P) : X ⊆ X⫠⫠ := by grind

/-- The triple orthogonal equals the orthogonal: X⫠⫠⫠ = X⫠. -/
lemma triple_orth (X : Set P) : X⫠⫠⫠ = X⫠ := by
  apply le_antisymm <;> grind [orth_extensive]

lemma triple_dual {G : Set P} : G⫠⫠⫠⫠⫠ = G⫠⫠⫠ := by grind [triple_orth]

/-- The biorthogonal closure operator on sets in a phase space. -/
def biorthogonalClosure : ClosureOperator (Set P) where
  toFun X := X⫠⫠
  monotone' := by grind [Monotone]
  le_closure' := by grind
  idempotent' X := triple_orth X⫠

/-! # Basic theory of phase spaces -/

/--
Given a phase space (P, ⊥) and a family of subsets (Gᵢ) of P indexed by i ∈ I, we have that
(⋃ᵢ Gᵢ)⫠ = ⋂ᵢ Gᵢ⫠.
-/
lemma orth_iUnion {ι : Sort*} (G : ι → Set P) :
    (⋃ i, G i)⫠ = ⋂ i, (G i)⫠ := by
  ext m
  simp only [orthogonal_def, mem_iInter, mem_iUnion, forall_exists_index]
  exact forall_comm

/--
Given a phase space (P, ⊥) and a family of subsets (Gᵢ) of P indexed by i ∈ I, we have that
∩ᵢ Gᵢ⫠⫠ = (∪ᵢ Gᵢ⫠)⫠.
-/
lemma iInter_biorth_eq_orth_iUnion_orth {ι : Sort*} (G : ι → Set P) :
    (⋂ i, (G i)⫠⫠ : Set P) = (⋃ i, (G i)⫠)⫠ := by
  simpa using (orth_iUnion (G := fun i => (G i)⫠)).symm

/-! ## Facts -/

/-- A fact is a subset of a phase space that equals its biorthogonal closure. -/
def isFact (X : Set P) : Prop := X = X⫠⫠

/-- The type of facts in a phase space. -/
structure Fact (P : Type*) [PhaseSpace P] where
  /-- The underlying set that is a fact -/
  (carrier : Set P)
  (property : isFact carrier)

set_option linter.tacticAnalysis.verifyGrindOnly false in
instance : SetLike (Fact P) P where
  coe := Fact.carrier
  coe_injective _ _ _ := by grind only [cases Fact]

instance : PartialOrder (Fact P) := PartialOrder.ofSetLike (Fact P)

instance : HasSubset (Fact P) :=
  ⟨fun A B => (A : Set P) ⊆ (B : Set P)⟩

instance [PhaseSpace M] : Coe (Fact M) (Set M) := ⟨Fact.carrier⟩

initialize_simps_projections Fact (carrier → coe)

lemma Fact.eq (G : Fact P) : G = (G : Set P)⫠⫠ := G.property

lemma subset_dual_dual {G : Set P} :
  G ⊆ G⫠⫠ := fun p hp q hq => mul_comm p q ▸ hq _ hp

@[scoped grind =] lemma mem_dual {G : Fact P} : p ∈ G⫠ ↔ ∀ q ∈ G, p * q ∈ PhaseSpace.bot :=
  Iff.rfl

@[scoped grind =>]
lemma of_Fact {G : Fact P} {p : P}
    (hp : ∀ q, (∀ r ∈ G, q * r ∈ PhaseSpace.bot) → p * q ∈ PhaseSpace.bot) : p ∈ G := by
  rw [← SetLike.mem_coe, G.eq]
  simpa

@[scoped grind =, simp] lemma mem_carrier (G : Fact P) : G.carrier = (G : Set P) := rfl

/-- Construct a fact from a set G and a proof that its biorthogonal closure is contained in G. -/
@[simps] def Fact.mkSubset (G : Set P) (h : G⫠⫠ ⊆ G) : Fact P where
  carrier := G
  property := by grind [isFact, orth_extensive]

lemma dual_subset_dual {G H : Set P} (h : G ⊆ H) :
    H⫠ ⊆ G⫠ := fun _ hp _ hq => hp _ (h hq)

/-- Construct a fact from a set G and a proof that G equals the orthogonal of some set H. -/
@[simps!] def Fact.mkDual (G H : Set P) (h : G = H⫠) : Fact P :=
  Fact.mkSubset G <| by rw [h, triple_orth]

lemma coe_mk {X : Set P} {h : isFact X} : ((⟨X, h⟩ : Fact P) : Set P) = X := rfl

@[simp] lemma closed (F : Fact P) : isFact (F : Set P) := F.property

/-- In any phase space, `{1}⫠ = ⊥`. -/
lemma orth_one_eq_bot : ({(1 : P)} : Set P)⫠ = (PhaseSpace.bot : Set P) := by
  simp_all

/-- The fact given by the dual of G. -/
@[simps!] def dualFact (G : Set P) : Fact P := Fact.mkDual (G⫠) G rfl

lemma dual_dual_subset_Fact_iff {G : Set P} {H : Fact P} : G⫠⫠ ⊆ H ↔ G ⊆ H := by
  constructor <;> rw [H.eq] <;> grind

lemma dual_dual_subset_dual_iff {G H : Set P} :
    G⫠⫠ ⊆ H⫠ ↔ G ⊆ H⫠ := by
  simpa using (dual_dual_subset_Fact_iff (H := dualFact H))

instance : One (Fact P) where one := dualFact (PhaseSpace.bot : Set P)

@[scoped grind =, simp] lemma coe_one : ((1 : Fact P) : Set P) = (PhaseSpace.bot : Set P)⫠ := rfl

@[scoped grind =, simp] lemma mem_one :
  p ∈ (1 : Fact P) ↔ (∀ q ∈ PhaseSpace.bot, p * q ∈ PhaseSpace.bot) := Iff.rfl

lemma one_mem_one : (1 : P) ∈ (1 : Fact P) := by simp [mem_one]

lemma mul_mem_one (hp : p ∈ (1 : Fact P)) (hq : q ∈ (1 : Fact P)) : p * q ∈ (1 : Fact P) := by
  grind

instance : Top (Fact P) where
  top := Fact.mkSubset Set.univ <| fun _ _ => Set.mem_univ _

@[scoped grind =, simp] lemma coe_top : ((⊤ : Fact P) : Set P) = Set.univ := rfl

@[simp] lemma mem_top : x ∈ (⊤ : Fact P) := Set.mem_univ _

@[scoped grind =] lemma dual_empty : (∅ : Set P)⫠ = Set.univ := by simp

@[scoped grind =, simp]
lemma dualFact_empty : dualFact (∅ : Set P) = ⊤ := SetLike.coe_injective (by simp)

instance : Zero (Fact P) where zero := dualFact ⊤

@[scoped grind =, simp] lemma coe_zero : ((0 : Fact P) : Set P) = (Set.univ : Set P)⫠ := rfl

lemma mem_zero : p ∈ (0 : Fact P) ↔ ∀ q, p * q ∈ PhaseSpace.bot := by
  simp [← SetLike.mem_coe]

instance : Bot (Fact P) where
  bot := Fact.mkDual (PhaseSpace.bot : Set P) {1} (orth_one_eq_bot).symm

/-- In a phase space, `G⫠⫠` is the smallest fact containing `G`. -/
lemma biorth_least_fact (G : Set P) :
      ∀ {F : Set P}, isFact F → G ⊆ F → G⫠⫠ ⊆ F := by
  intro F hF hGF
  exact biorthogonalClosure.closure_min hGF hF.symm

/-- `0` is the least fact (w.r.t. inclusion). -/
lemma zero_least_fact :
    ∀ {F : Set P}, isFact F → (0 : Fact P).carrier ⊆ F := by
  intro F hF
  have h := biorth_least_fact (G := (∅ : Set P)) hF (by simp)
  simpa using h

lemma isFact_iff_closed (X : Set P) :
  isFact X ↔ biorthogonalClosure.IsClosed X := eq_comm

/-- Arbitrary intersections of facts are facts. -/
lemma sInf_isFact {S : Set (Fact P)} :
  isFact (sInf ((fun F : Fact P => (F : Set P)) '' S)) := by
  rw [isFact_iff_closed]
  apply ClosureOperator.sInf_isClosed
  rintro _ ⟨F, _, rfl⟩
  exact (isFact_iff_closed _).1 F.property

/-- Intersection of the carriers of a set of facts. -/
def carriersInf (S : Set (Fact P)) : Set P :=
  sInf ((fun F : Fact P => (F : Set P)) '' S)

/-- Binary intersections of facts are facts. -/
lemma inter_isFact_of_isFact {A B : Set P} (hA : isFact A) (hB : isFact B) : isFact (A ∩ B) := by
  simpa using! sInf_isFact (S := {⟨A, hA⟩, ⟨B, hB⟩})

instance : InfSet (Fact P) where
  sInf S := ⟨carriersInf S, sInf_isFact (S := S)⟩

omit [PhaseSpace P] in
lemma iInter_eq_sInf_image {α} (S : Set α) (f : α → Set P) :
    (⋂ x ∈ S, f x) = sInf (f '' S) := by aesop

@[scoped grind =, simp]
lemma inter_eq_orth_union_orth (G H : Fact P) :
    ((G : Set P) ∩ (H : Set P) : Set P) =
      (((G : Set P)⫠) ∪ ((H : Set P)⫠) : Set P)⫠ := by
  ext m
  constructor
  · simp only [orthogonal_def, mem_union]
    grind
  · grind [Fact.eq]

instance : Min (Fact P) where
  min G H := Fact.mkDual (G ∩ H) (G⫠ ∪ H⫠) <| by simp

@[simp] lemma coe_min {G H : Fact P} : ((G ⊓ H : Fact P) : Set P) = (G : Set P) ∩ H := rfl

/-- The idempotent elements within a given set X. -/
def idempotentsIn [Monoid M] (X : Set M) : Set M := {m | IsIdempotentElem m ∧ m ∈ X}

/-- The set I of idempotents that "belong to 1" in the phase semantics. -/
def I : Set P := idempotentsIn (1 : Set P)

/-! ## Interpretation of the connectives -/

namespace Fact

/--
Linear negation of a fact, given by taking its orthogonal.
-/
def neg (G : Fact P) : Fact P := dualFact G

@[inherit_doc] postfix:max "ᗮ" => neg

@[simp] lemma coe_neg {G : Fact P} : (Gᗮ : Set P) = (G : Set P)⫠ := rfl

@[simp] lemma neg_neg {G : Fact P} : Gᗮᗮ = G := SetLike.coe_injective G.eq.symm

@[simp] lemma neg_bot : (⊥ : Fact P)ᗮ = 1 := rfl

@[simp] lemma neg_one : (1 : Fact P)ᗮ = ⊥ := by rw [← neg_bot, neg_neg]

@[simp] lemma neg_top : (⊤ : Fact P)ᗮ = 0 := rfl

@[simp] lemma neg_zero : (0 : Fact P)ᗮ = ⊤ := by rw [← neg_top, neg_neg]

lemma neg_eq_iff {G H : Fact P} : Gᗮ = H ↔ G = Hᗮ :=
  ⟨fun h => h ▸ neg_neg.symm, fun h => h ▸ neg_neg⟩

@[simp] theorem neg_involutive : Function.Involutive (neg : Fact P → Fact P) :=
  fun _ => neg_neg

@[simp] theorem neg_surjective : Function.Surjective (neg : Fact P → Fact P) :=
  neg_involutive.surjective

theorem neg_injective : Function.Injective (neg : Fact P → Fact P) :=
  neg_involutive.injective

@[simp] theorem neg_inj {G H : Fact P} : Gᗮ = Hᗮ ↔ G = H :=
  neg_injective.eq_iff

/--
The tensor product `X ⊗ Y` of two facts,
defined as the dual of the orthogonal of the pointwise product.
-/
def tensor (X Y : Fact P) : Fact P := dualFact (X * Y)⫠

@[inherit_doc] infixr:78 " ⊗ " => tensor

/--
The par (multiplicative disjunction) `X ⅋ Y` of two facts,
defined as the dual of the pointwise product of the orthogonals.
-/
def parr (X Y : Fact P) : Fact P := dualFact ((X⫠) * (Y⫠))

@[inherit_doc] infixr:78 " ⅋ " => parr

@[simp] lemma one_tensor {G : Fact P} : (1 ⊗ G) = G := by
  refine SetLike.coe_injective ?_
  rw [tensor]
  refine Set.Subset.antisymm ?_ ?_
  · simp only [dualFact, mkDual, mkSubset, coe_mk]
    rw [dual_dual_subset_Fact_iff]
    grind [SetLike.mem_coe, Set.mem_mul]
  · exact Set.Subset.trans (orth_extensive _) <| orth_antitone <| orth_antitone <|
      Set.subset_mul_right _ (by simp)

lemma tensor_comm {X Y : Fact P} : (X ⊗ Y) = (Y ⊗ X) := by rw [tensor, tensor, mul_comm]

@[simp] lemma tensor_one {G : Fact P} : (G ⊗ 1) = G := by rw [tensor_comm, one_tensor]

lemma tensor_assoc_aux {F G : Set P} :
    (F⫠⫠) * (G⫠⫠) ⊆ (F * G)⫠⫠ := by
  simp only [Set.subset_def, Set.mem_mul, forall_exists_index, and_imp]
  rintro _ p hp q hq rfl v hv
  rw [mul_assoc]
  refine hp _ fun f hf => ?_
  have : v * f ∈ G⫠ := fun g hg => mul_assoc v f g ▸ hv _ (Set.mul_mem_mul hf hg)
  grind

lemma coe_tensor_assoc {G H K : Fact P} :
    ((G ⊗ H) ⊗ K : Set P) = ((G : Set P) * ((H : Set P) * (K : Set P)))⫠⫠ := by
  simp only [tensor]
  refine Set.Subset.antisymm ?_ ?_
  · simp only [dualFact, mkDual, mkSubset, coe_mk, dual_dual_subset_dual_iff]
    rw [K.eq]
    refine tensor_assoc_aux.trans ?_
    rw [← K.eq]
    grind
  repeat apply orth_antitone
  intro x hx
  rcases Set.mem_mul.mp hx with ⟨g, hg, y, hy, rfl⟩
  rcases Set.mem_mul.mp hy with ⟨h, hh, k, hk, rfl⟩
  have gh_mem : g * h ∈ ((G : Set P) * (H : Set P)) := Set.mul_mem_mul hg hh
  have gh_mem' : g * h ∈ ((G : Set P) * (H : Set P))⫠⫠ := (orth_extensive _) gh_mem
  exact Set.mem_mul.mpr ⟨g * h, gh_mem', k, hk, by simp [mul_assoc]⟩

@[simp] lemma tensor_assoc {G H K : Fact P} : ((G ⊗ H) ⊗ K) = (G ⊗ H ⊗ K) :=
  SetLike.coe_injective <| by
    grind [SetLike.coe_injective, coe_tensor_assoc, tensor_comm, coe_tensor_assoc]

lemma tensor_rotate {G H K : Fact P} : (G ⊗ H ⊗ K) = H ⊗ K ⊗ G := by
  rw [tensor_comm, tensor_assoc]

lemma tensor_le_tensor {G K H} {L : Fact P} (hGK : G ≤ K) (hHL : H ≤ L) : (G ⊗ H) ≤ (K ⊗ L) :=
  orth_antitone <| orth_antitone <| Set.mul_subset_mul hGK hHL

lemma tensor_of_par {G H : Fact P} : (G ⊗ H) = (Gᗮ ⅋ Hᗮ)ᗮ :=
  SetLike.coe_injective <| by
    simp only [tensor, parr, dualFact, mkDual, mkSubset, coe_mk]
    rw [G.eq, H.eq]
    #adaptation_note
    /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
    rfl

lemma par_of_tensor {G H : Fact P} : (G ⅋ H) = (Gᗮ ⊗ Hᗮ)ᗮ := by
  simp [tensor_of_par]

lemma par_le_par {G H K L : Fact P} (hGK : G ≤ K) (hHL : H ≤ L) : (G ⅋ H) ≤ (K ⅋ L) :=
  orth_antitone <| Set.mul_subset_mul (orth_antitone hGK) (orth_antitone hHL)

@[simp] lemma bot_par {G : Fact P} : (⊥ ⅋ G) = G := by simp [par_of_tensor]

@[simp] lemma par_bot {G : Fact P} : (G ⅋ ⊥) = G := by simp [par_of_tensor]

@[simp] lemma par_assoc {G H K : Fact P} : ((G ⅋ H) ⅋ K) = (G ⅋ H ⅋ K) := by simp [par_of_tensor]

lemma par_comm (G H : Fact P) : (G ⅋ H) = (H ⅋ G) := by simp [par_of_tensor, tensor_comm]

/--
Linear implication between facts,
defined as the dual of the orthogonal of the pointwise product.
-/
def linImpl (X Y : Fact P) : Fact P := dualFact ((X : Set P) * (Y : Set P)⫠)
@[inherit_doc] infix:73 " ⊸ " => linImpl

lemma linImpl_of_tensor {G H : Fact P} : (G ⊸ H) = (G ⊗ Hᗮ)ᗮ :=
  SetLike.coe_injective <| by
    simp only [linImpl, tensor, coe_neg, dualFact, mkDual, mkSubset, coe_mk]
    apply Set.Subset.antisymm <;> grind

lemma par_of_linImpl {G H : Fact P} : (G ⅋ H) = (Gᗮ ⊸ H) :=
  SetLike.coe_injective <| by simp [parr, linImpl]

lemma tensor_of_linImpl {G H : Fact P} : (G ⊗ H) = (G ⊸ Hᗮ)ᗮ := by simp [linImpl_of_tensor]

lemma linImpl_of_par {G H : Fact P} : (G ⊸ H) = (Gᗮ ⅋ H) := by simp [par_of_linImpl]

lemma neg_tensor {G H : Fact P} : (G ⊗ H)ᗮ = Gᗮ ⅋ Hᗮ := by rw [tensor_of_par, neg_neg]

lemma neg_par {G H : Fact P} : (G ⅋ H)ᗮ = Gᗮ ⊗ Hᗮ := by rw [par_of_tensor, neg_neg]

lemma mul_subset_tensor {G H : Fact P} : (G * H : Set P) ⊆ G ⊗ H := orth_extensive _

@[simp] lemma one_linImpl {G : Fact P} : (1 ⊸ G) = G := by simp [linImpl_of_tensor]

@[simp] lemma linImpl_bot {G : Fact P} : (G ⊸ ⊥) = Gᗮ := by simp [linImpl_of_tensor]

@[simp] lemma tensor_linImpl {G H K : Fact P} : ((G ⊗ H) ⊸ K) = (G ⊸ (H ⊸ K)) := by
  simp [linImpl_of_tensor]

lemma linImpl_par {G H K : Fact P} : (G ⊸ H ⅋ K) = ((G ⊸ H) ⅋ K) := by
  simp [linImpl_of_tensor, par_of_tensor]

lemma linImpl_par' {G H K : Fact P} : (G ⊸ H ⅋ K) = (H ⅋ (G ⊸ K)) := by
  rw [par_comm, linImpl_par, par_comm]

@[simp] lemma neg_linImpl_neg {G H : Fact P} : (Gᗮ ⊸ Hᗮ) = (H ⊸ G) := by
  simp [linImpl_of_tensor, tensor_comm]

lemma linImpl_iff_implies {G H : Fact P} : p ∈ G ⊸ H ↔ p ∈ imp G H := by
  rw [← SetLike.mem_coe, linImpl]
  simp only [dualFact_coe, mem_dual, Set.mem_mul, SetLike.mem_coe,
    forall_exists_index, and_imp]
  constructor
  · intro h q hq
    apply of_Fact _
    intro r hr
    rw [mul_assoc]
    exact h _ _ hq _ hr rfl
  · rintro h _ r hr s hs rfl
    rw [← mul_rotate']
    exact hs _ (h _ hr)

/--
The with (additive conjunction) `X & Y` of two facts,
defined as the intersection of the two facts.
-/
def withh (X Y : Fact P) : Fact P := X ⊓ Y
@[inherit_doc] infix:74 " & " => withh

/--
The oplus (additive disjunction) `X ⊕ Y` of two facts,
defined as the dual of the orthogonal of the union.
-/
def oplus (X Y : Fact P) : Fact P := dualFact (X ∪ Y)⫠
@[inherit_doc] infix:74 " ⊕ " => oplus

/--
The exponential `!X` (of course) of a fact,
defined as the dual of the orthogonal of the intersection with the idempotents.
-/
def bang (X : Fact P) : Fact P := dualFact (X ∩ I)⫠
@[inherit_doc] prefix:100 " ! " => bang

/--
The exponential `?X` (why not) of a fact,
defined as the dual of the intersection of the orthogonal with the idempotents.
-/
def quest (X : Fact P) : Fact P := dualFact (X⫠ ∩ I)
@[inherit_doc] prefix:100 " ʔ " => quest

/-! ### Properties of Additives -/

lemma plus_eq_with_dual : (G ⊕ H : Fact P) = (Gᗮ & Hᗮ)ᗮ := by
  apply SetLike.coe_injective
  rw [oplus, withh]
  aesop

lemma with_eq_plus_dual : (G & H : Fact P) = (Gᗮ ⊕ Hᗮ)ᗮ := by simp [plus_eq_with_dual]

lemma neg_plus {G H : Fact P} : (G ⊕ H)ᗮ = Gᗮ & Hᗮ := by rw [plus_eq_with_dual, neg_neg]

lemma neg_with {G H : Fact P} : (G & H)ᗮ = Gᗮ ⊕ Hᗮ := by rw [with_eq_plus_dual, neg_neg]

lemma with_comm : (G & H : Fact P) = H & G :=
  SetLike.coe_injective <| by simp [withh, Set.inter_comm]

@[simp] lemma with_assoc : ((G & H) & K : Fact P) = G & (H & K) := by
  apply SetLike.coe_injective
  rw [withh, coe_min]
  exact Set.inter_assoc ..

@[simp] lemma top_with : (⊤ & G : Fact P) = G := SetLike.coe_injective <| by simp [withh]

@[simp] lemma with_top : (G & ⊤ : Fact P) = G := SetLike.coe_injective <| by simp [withh]

lemma plus_comm : (G ⊕ H : Fact P) = H ⊕ G := by rw [oplus, Set.union_comm, ← oplus]

@[simp] lemma plus_assoc : ((G ⊕ H) ⊕ K : Fact P) = G ⊕ (H ⊕ K) := by
  simp [plus_eq_with_dual]

@[simp] lemma zero_plus : (0 ⊕ G : Fact P) = G := by simp [plus_eq_with_dual]

@[simp] lemma plus_zero : (G ⊕ 0 : Fact P) = G := by simp [plus_eq_with_dual]

/-! ### Distributivity Properties -/

lemma le_plus_left {G H : Fact P} : G ≤ G ⊕ H := fun _ hx ↦
  subset_dual_dual <| Or.inl hx

lemma le_plus_right {G H : Fact P} : H ≤ G ⊕ H := fun _ hx ↦
  subset_dual_dual <| Or.inr hx

lemma tensor_distrib_plus : (G ⊗ (H ⊕ K) : Fact P) = (G ⊗ H) ⊕ (G ⊗ K) := by
  refine SetLike.coe_injective <| Set.Subset.antisymm ?_ ?_
  · rw [tensor, dualFact, mkDual_coe, oplus, dualFact, mkDual_coe]
    rw [dual_dual_subset_Fact_iff, G.eq]
    refine tensor_assoc_aux.trans ?_
    rw [Set.mul_union, oplus, dualFact, mkDual_coe, tensor, dualFact, mkDual_coe]
    exact dual_subset_dual <| dual_subset_dual <|
      Set.union_subset_union subset_dual_dual subset_dual_dual
  · rw [oplus, dualFact, mkDual_coe, dual_dual_subset_Fact_iff, tensor, dualFact, mkDual_coe,
      tensor, dualFact, mkDual_coe, Set.union_subset_iff]
    simp only [dual_dual_subset_Fact_iff]
    exact ⟨(Set.mul_subset_mul_left le_plus_left).trans mul_subset_tensor,
           (Set.mul_subset_mul_left le_plus_right).trans mul_subset_tensor⟩

lemma plus_tensor_distrib : ((H ⊕ K) ⊗ G  : Fact P) = (H ⊗ G) ⊕ (K ⊗ G) := by
  rw [tensor_comm, tensor_distrib_plus]; simp [tensor_comm]

lemma par_distrib_with : (G ⅋ (H & K) : Fact P) = (G ⅋ H) & (G ⅋ K) := by
  simp [par_of_tensor, with_eq_plus_dual, tensor_distrib_plus]

lemma with_par_distrib : ((H & K) ⅋ G : Fact P) = (H ⅋ G) & (K ⅋ G) := by
  rw [par_comm, par_distrib_with]; simp [par_comm]

lemma tensor_semi_distrib_with : (G ⊗ (H & K) : Fact P) ≤ (G ⊗ H) & (G ⊗ K) := by
  rw [← SetLike.coe_subset_coe]
  simp only [tensor, withh, coe_min, dualFact_coe, Set.subset_inter_iff]
  exact ⟨dual_subset_dual (dual_subset_dual (Set.mul_subset_mul_left Set.inter_subset_left)),
         dual_subset_dual (dual_subset_dual (Set.mul_subset_mul_left Set.inter_subset_right))⟩

lemma with_tensor_semi_distrib : ((G & H) ⊗ K : Fact P) ≤ (G ⊗ K) & (H ⊗ K) :=
  calc ((G & H) ⊗ K : Fact P) = K ⊗ (G & H) := by rw [tensor_comm]
    _ ≤ K ⊗ G & K ⊗ H := tensor_semi_distrib_with
    _ = _ := by simp only [tensor_comm]

lemma neg_le_neg_iff {G H : Fact P} : Gᗮ ≤ Hᗮ ↔ H ≤ G := by
  constructor
  · intro h
    rw [← neg_neg (G := H), ← neg_neg (G := G)]
    exact PhaseSpace.orth_antitone h
  · exact PhaseSpace.orth_antitone

lemma par_semi_distrib_plus : ((G ⅋ H) ⊕ (G ⅋ K) : Fact P) ≤ G ⅋ (H ⊕ K) := by
  rw [← neg_le_neg_iff]
  simp only [neg_par, neg_plus]
  exact tensor_semi_distrib_with

/-! ### Absorption Properties -/

@[simp] lemma top_par : (⊤ ⅋ G : Fact P) = ⊤ := by
  refine SetLike.coe_injective ?_
  rw [coe_top, Set.eq_univ_iff_forall]
  intro x w hw
  rcases Set.mem_mul.mp hw with ⟨y, hy, z, hz, rfl⟩
  rw [mul_left_comm]
  exact hy (x * z) (Set.mem_univ _)

@[simp] lemma par_top : (G ⅋ ⊤ : Fact P) = ⊤ := by
  rw [par_comm, top_par]

@[simp] lemma zero_tensor : (0 ⊗ G : Fact P) = 0 := by
  simp [tensor_of_par]

@[simp] lemma tensor_zero : (G ⊗ 0 : Fact P) = 0 := by
  rw [tensor_comm, zero_tensor]

/-! ### Entailment Distributivity -/

@[simp] lemma plus_entails : ((G ⊕ H) ⊸ K : Fact P) = (G ⊸ K) & (H ⊸ K) := by
  simp only [linImpl_of_tensor, with_eq_plus_dual, plus_tensor_distrib, neg_neg]

@[simp] lemma entails_with : (G ⊸ (H & K) : Fact P) = (G ⊸ H) & (G ⊸ K) := by
  simp only [linImpl_of_par, par_distrib_with]

@[simp] lemma zero_entails : (0 ⊸ G : Fact P) = ⊤ := by simp [linImpl_of_par]

@[simp] lemma entails_top : (G ⊸ ⊤ : Fact P) = ⊤ := by simp [linImpl_of_par]

/--
A fact `G` is valid if the unit `1` belongs to `G`.
-/
abbrev IsValid (G : Fact P) : Prop := 1 ∈ G

lemma valid_with {G H : Fact P} : (G & H).IsValid ↔ G.IsValid ∧ H.IsValid := Iff.rfl

end Fact

open PhaseSpace.Fact

/-! ## Interpretation of propositions -/

/--
The interpretation of a CLL proposition in a phase space, given a valuation of atoms to facts.
-/
def interpProp [PhaseSpace M] (v : Atom → Fact M) : Proposition Atom → Fact M
  | .atom a       => v a
  | .atomDual a   => (v a)ᗮ
  | .one          => 1
  | .zero         => 0
  | .top          => ⊤
  | .bot          => ⊥
  | .tensor A B   => (interpProp v A) ⊗ (interpProp v B)
  | .parr   A B   => (interpProp v A) ⅋ (interpProp v B)
  | .with   A B   => (interpProp v A) & (interpProp v B)
  | .oplus  A B   => (interpProp v A) ⊕ (interpProp v B)
  | .bang   A     => !(interpProp v A)
  | .quest  A     => ʔ(interpProp v A)

@[inherit_doc] scoped notation:max "⟦" P "⟧" v:90 => interpProp v P

end PhaseSpace

end Cslib.Logic.CLL
