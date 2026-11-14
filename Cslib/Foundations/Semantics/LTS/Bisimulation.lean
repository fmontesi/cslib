/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring
-/

module

public import Cslib.Foundations.Order.FixedPoints
public import Cslib.Foundations.Relation.Domain
public import Cslib.Foundations.Semantics.LTS.TraceEq
public import Mathlib.SetTheory.Ordinal.FixedPointApproximants
public import Mathlib.Tactic.TFAE

import Mathlib.Data.Fintype.Order

/-! # Bisimulation and Bisimilarity

A bisimulation is a binary relation on the states of two `LTS`s, which establishes a tight semantic
correspondence. More specifically, if two states `s₁` and `s₂` are related by a bisimulation, then
`s₁` can mimic all transitions of `s₂` and vice versa. Furthermore, the derivatives reached through
these transitions remain related by the bisimulation.

Bisimilarity is the largest bisimulation between two LTSs: it relates any two states that are
related by some bisimulation between those LTSs.

Weak bisimulation (resp. bisimilarity) is the relaxed version of bisimulation (resp. bisimilarity)
whereby internal actions performed by processes can be ignored.

For an introduction to theory of bisimulation, we refer to [Sangiorgi2011].

## Main definitions

- `IsBisimulation lts₁ lts₂ r`: the relation `r` is a bisimulation between `lts₁` and `lts₂`.
- `Bisimilarity lts₁ lts₂`: states related by some bisimulation between `lts₁` and `lts₂`.
- `bisimulationStep lts₁ lts₂`: the monotone one-step bisimulation operator.
- `BisimilarityApprox lts₁ lts₂ o`: the stratum of bisimilarity at an index in `WithTop Ordinal`.
- `UpToHomBisimilarity lts₁ lts₂ r`: the closure of `r` under bisimilarity in each LTS.
- `IsBisimulationUpTo lts₁ lts₂ r`: transitions from states related by `r` can be matched with
  derivatives in `UpToHomBisimilarity lts₁ lts₂ r`.
- `IsWeakBisimulation lts₁ lts₂ r`: the relation `r` is a weak bisimulation.
- `WeakBisimilarity lts₁ lts₂`: states related by some weak bisimulation.
- `IsSWBisimulation lts₁ lts₂ r`: a characterization of weak bisimulation using single-transition
  challenges, which we prove to be sound and complete.

The `Hom` variants specialize these definitions to comparing states in the same LTS.

## Notations

- `s₁ ~[lts₁,lts₂] s₂`: the states `s₁` and `s₂` are bisimilar under `lts₁` and `lts₂`.
- `s₁ ≈[lts₁,lts₂] s₂`: the states `s₁` and `s₂` are weakly bisimilar under `lts₁` and `lts₂`.
- `s₁ ~[lts] s₂` and `s₁ ≈[lts] s₂`: the corresponding homogeneous relations.
- `s₁ ~[lts₁,lts₂;o] s₂` and `s₁ ~[lts;o] s₂`: approximations of bisimilarity.
  Ordinals and natural numbers coerce to `WithTop Ordinal`; `open scoped Ordinal` enables `ω`.
  The index `⊤` denotes the intersection of all ordinal strata.

## Main statements

- `LTS.IsBisimulation.inv`: the inverse of a bisimulation is a bisimulation.
- `HomBisimilarity.eqv`: homogeneous bisimilarity is an equivalence relation (see `Equivalence`).
- `Bisimilarity.isBisimulation`: bisimilarity is itself a bisimulation.
- `BisimilarityApprox.top_eq_bisimilarity`: the top endpoint is bisimilarity for all LTSs.
- `BisimilarityApprox.omega_eq_bisimilarity`: on image-finite LTSs, the omega approximation is
  bisimilarity.
- `BisimilarityApprox.stabilizes`: the ordinal strata eventually stabilize at bisimilarity.
- `IsBisimulation.le_bisimilarity`: bisimilarity is the largest bisimulation.
- `Bisimilarity.gfp`: the union of bisimilarity and any bisimulation is equal to bisimilarity.
- `LTS.IsBisimulationUpTo.isBisimulation`: if `r` is a bisimulation up to bisimilarity,
  `UpToHomBisimilarity lts₁ lts₂ r` is a bisimulation.
- `LTS.IsBisimulationUpTo.le_bisimilarity`: a bisimulation up to bisimilarity relates only
  bisimilar states.
- `LTS.IsBisimulation.traceEq`: any bisimulation that relates two states implies that they are
trace equivalent (see `TraceEq`).
- `Bisimilarity.deterministic_bisim_eq_traceEq`: in a deterministic LTS, bisimilarity and trace
equivalence coincide.
- `HomBisimilarity.symm_simulation`: homogeneous bisimilarity can be characterized through
  symmetric simulations.
- `WeakBisimilarity.weakBisim_eq_swBisim`: weak bisimulation and sw-bisimulation coincide.
- `HomWeakBisimilarity.eqv`: homogeneous weak bisimilarity is an equivalence relation.

-/

@[expose] public section

namespace Cslib.LTS

universe u

variable {State₁ State₂ Label : Type*} {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}

section Bisimulation

/-- A relation is a bisimulation if, whenever it relates two states,
the transitions originating from these states mimic each other and the reached
derivatives are themselves related. -/
def IsBisimulation (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (r : State₁ → State₂ → Prop) : Prop :=
  ∀ ⦃s₁ s₂⦄, r s₁ s₂ → ∀ μ, (
    (∀ s₁', lts₁.Tr s₁ μ s₁' → ∃ s₂', lts₂.Tr s₂ μ s₂' ∧ r s₁' s₂')
    ∧
    (∀ s₂', lts₂.Tr s₂ μ s₂' → ∃ s₁', lts₁.Tr s₁ μ s₁' ∧ r s₁' s₂')
  )

/-! ## Relation to simulation -/

/-- Any bisimulation is also a simulation. -/
theorem IsBisimulation.isSimulation : IsBisimulation lts₁ lts₂ r → IsSimulation lts₁ lts₂ r := by
  grind [IsBisimulation, IsSimulation]

/-- The inverse of a bisimulation is a simulation. -/
theorem IsBisimulation.flip_isSimulation :
    IsBisimulation lts₁ lts₂ r → IsSimulation lts₂ lts₁ (flip r) := by
  grind [IsBisimulation, IsSimulation, flip]

/-- A relation is a bisimulation iff both it and its inverse are simulations. -/
theorem IsBisimulation.isSimulation_iff :
    IsBisimulation lts₁ lts₂ r ↔ (IsSimulation lts₁ lts₂ r ∧ IsSimulation lts₂ lts₁ (flip r)) := by
  have _ (s₁ s₂) : r s₁ s₂ → flip r s₂ s₁ := id
  grind [IsBisimulation, IsSimulation, flip]

/-- Helper for following a transition by the first state in a pair of a `Bisimulation`. -/
theorem IsBisimulation.follow_fst
    (hb : IsBisimulation lts₁ lts₂ r) (hr : r s₁ s₂) (htr : lts₁.Tr s₁ μ s₁') :
    ∃ s₂', lts₂.Tr s₂ μ s₂' ∧ r s₁' s₂' :=
  IsSimulation.follow hb.isSimulation hr htr

/-- Helper for following a transition by the second state in a pair of a `Bisimulation`. -/
theorem IsBisimulation.follow_snd
    (hb : IsBisimulation lts₁ lts₂ r) (hr : r s₁ s₂) (htr : lts₂.Tr s₂ μ s₂') :
    ∃ s₁', lts₁.Tr s₁ μ s₁' ∧ r s₁' s₂' :=
  IsSimulation.follow hb.flip_isSimulation hr htr

/-- If the unique transition of a state is matched by a related state in a bisimulation,
then the derivatives are still in the bisimulation. -/
theorem IsBisimulation.match_deterministic
    (hb : IsBisimulation lts₁ lts₂ r)
    (hr : r s₁ s₂)
    (hdet : lts₁.DeterministicStateLabel s₁ μ)
    (htr₁ : lts₁.Tr s₁ μ s₁')
    (htr₂ : lts₂.Tr s₂ μ s₂') : r s₁' s₂' := by
  have hr' : (flip r) s₂ s₁ := by grind [flip]
  apply IsSimulation.match_deterministic hb.flip_isSimulation hr' hdet htr₂ htr₁

/-- If the unique transition of a state is matched by a related state in the inverse of a
bisimulation, then the derivatives are still in the bisimulation. -/
theorem IsBisimulation.match_deterministic₂
    (hb : IsBisimulation lts₁ lts₂ r)
    (hr : r s₁ s₂)
    (hdet : lts₂.DeterministicStateLabel s₂ μ)
    (htr₁ : lts₁.Tr s₁ μ s₁')
    (htr₂ : lts₂.Tr s₂ μ s₂') : r s₁' s₂' := by
  apply IsSimulation.match_deterministic hb.isSimulation hr hdet htr₁ htr₂

/-- If a state is deterministic for `μ`, then any transition made by a related state in a
bisimulation is matched by a unique transition (left variant). -/
theorem IsBisimulation.follow_fst_deterministic (hb : IsBisimulation lts₁ lts₂ r) (hr : r s₁ s₂)
    (hdet : lts₂.DeterministicStateLabel s₂ μ) (htr : lts₁.Tr s₁ μ s₁') :
    ∃! s₂', lts₂.Tr s₂ μ s₂' ∧ r s₁' s₂' :=
  IsSimulation.follow_deterministic hb.isSimulation hr hdet htr

/-- If a state is deterministic for `μ`, then any transition made by a related state in a
bisimulation is matched by a unique transition (right variant). -/
theorem IsBisimulation.follow_snd_deterministic
    (hb : IsBisimulation lts₁ lts₂ r)
    (hr : r s₁ s₂)
    (hdet : lts₁.DeterministicStateLabel s₁ μ)
    (htr : lts₂.Tr s₂ μ s₂') : ∃! s₁', lts₁.Tr s₁ μ s₁' ∧ r s₁' s₂' :=
  IsSimulation.follow_deterministic hb.flip_isSimulation hr hdet htr

/-- A homogeneous bisimulation is a bisimulation where the underlying LTSs are the same. -/
abbrev IsHomBisimulation (lts : LTS State Label) := IsBisimulation lts lts

/-- Two states are bisimilar if they are related by some bisimulation. -/
@[scoped grind =]
def Bisimilarity (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) : State₁ → State₂ → Prop :=
  fun s₁ s₂ => ∃ r : State₁ → State₂ → Prop, r s₁ s₂ ∧ IsBisimulation lts₁ lts₂ r

/--
Notation for bisimilarity.

Differently from standard pen-and-paper presentations, we require the LTSs to be mentioned
explicitly.
-/
scoped notation s:max " ~[" lts₁ "," lts₂ "] " s':max => Bisimilarity lts₁ lts₂ s s'

/-- Homogeneous bisimilarity is bisimilarity where the underlying LTSs are the same. -/
abbrev HomBisimilarity (lts : LTS State Label) := Bisimilarity lts lts

/-- Notation for homogeneous bisimilarity. -/
scoped notation s:max " ~[" lts "] " s':max => HomBisimilarity lts s s'

/-- Helper for following a transition by the first state in a pair of a `Bisimilarity`. -/
theorem Bisimilarity.follow_fst (hr : s₁ ~[lts₁,lts₂] s₂) (htr : lts₁.Tr s₁ μ s₁') :
    ∃ s₂', lts₂.Tr s₂ μ s₂' ∧ s₁' ~[lts₁,lts₂ ] s₂' := by grind [IsBisimulation]

/-- Helper for following a transition by the first state in a pair of a `Bisimilarity`. -/
theorem Bisimilarity.follow_snd (hr : s₁ ~[lts₁,lts₂] s₂) (htr : lts₂.Tr s₂ μ s₂') :
    ∃ s₁', lts₁.Tr s₁ μ s₁' ∧ s₁' ~[lts₁,lts₂] s₂' := by grind [IsBisimulation]

/-- Homogeneous bisimilarity is reflexive. -/
@[scoped grind ., refl]
theorem HomBisimilarity.refl (s : State) : s ~[lts] s := by
  exists Eq
  grind [IsBisimulation]

/-- States with the same image function are bisimilar. -/
theorem HomBisimilarity.of_image_eq {lts : LTS State Label} {s₁ s₂ : State}
    (h : lts.image s₁ = lts.image s₂) : s₁ ~[lts] s₂ := by
  refine ⟨fun s t => lts.image s = lts.image t, h, ?_⟩
  intro s t h μ
  have htr (s' : State) : lts.Tr s μ s' ↔ lts.Tr t μ s' :=
    Set.ext_iff.mp (congrFun h μ) s'
  exact ⟨fun s' hs' => ⟨s', (htr s').mp hs', rfl⟩,
    fun t' ht' => ⟨t', (htr t').mpr ht', rfl⟩⟩

/-- The inverse of a bisimulation is a bisimulation. -/
@[scoped grind →]
theorem IsBisimulation.inv (h : IsBisimulation lts₁ lts₂ r) :
  IsBisimulation lts₂ lts₁ (flip r) := by grind [IsBisimulation, flip]

open scoped IsBisimulation in
/-- Bisimilarity is symmetric. -/
@[scoped grind →, symm]
theorem Bisimilarity.symm {State₁ State₂ : Type*}
    {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {s₁ : State₁} {s₂ : State₂}
    (h : s₁ ~[lts₁,lts₂] s₂) : s₂ ~[lts₂,lts₁] s₁ := by
  grind [flip]

/-- The composition of two bisimulations is a bisimulation. -/
@[scoped grind .]
theorem IsBisimulation.comp
    (h1 : IsBisimulation lts₁ lts₂ r1) (h2 : IsBisimulation lts₂ lts₃ r2) :
  IsBisimulation lts₁ lts₃ (Relation.Comp r1 r2) := by grind [IsBisimulation, Relation.Comp]

/-- Bisimilarity is transitive. -/
@[scoped grind →]
theorem Bisimilarity.trans
    (h1 : s₁ ~[lts₁,lts₂] s₂) (h2 : s₂ ~[lts₂,lts₃] s₃) :
  s₁ ~[lts₁,lts₃] s₃ := by
  obtain ⟨r1, _, _⟩ := h1
  obtain ⟨r2, _, _⟩ := h2
  exists Relation.Comp r1 r2
  grind [IsBisimulation, Relation.Comp]

/-- Homogeneous bisimilarity is an equivalence relation. -/
theorem HomBisimilarity.eqv :
  Equivalence (· ~[lts] ·) := {
    refl := HomBisimilarity.refl
    symm := Bisimilarity.symm
    trans := Bisimilarity.trans
  }

instance : IsEquiv State (· ~[lts] ·) where
  refl := HomBisimilarity.refl
  symm _ _ := Bisimilarity.symm
  trans _ _ _ := Bisimilarity.trans

/-- Bisimulation implies simulation equivalence. -/
theorem IsBisimulation.simulationEquiv (h : IsBisimulation lts₁ lts₂ r) (hrel : r s₁ s₂) :
    s₁ ≤≥[lts₁,lts₂] s₂ := ⟨⟨r, hrel, h.isSimulation⟩, flip r, hrel, h.inv.isSimulation⟩

/-- The union of two bisimulations is a bisimulation. -/
@[scoped grind .]
theorem IsBisimulation.sup (hrb : IsBisimulation lts₁ lts₂ r) (hsb : IsBisimulation lts₁ lts₂ s) :
    IsBisimulation lts₁ lts₂ (r ⊔ s) := by
  rw [IsBisimulation.isSimulation_iff] at hrb hsb ⊢
  rw [show flip (r ⊔ s) = flip r ⊔ flip s by ext; rfl]
  exact ⟨hrb.1.sup hsb.1, hrb.2.sup hsb.2⟩

/-- Bisimilarity is a bisimulation. -/
@[scoped grind .]
theorem Bisimilarity.isBisimulation (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) :
  IsBisimulation lts₁ lts₂ (· ~[lts₁,lts₂] ·) := by grind [IsBisimulation]

/-- Bisimilarity is the largest bisimulation. -/
@[scoped grind →]
theorem IsBisimulation.le_bisimilarity (h : IsBisimulation lts₁ lts₂ r) :
    r ≤ (· ~[lts₁,lts₂] ·) := by
  intro s₁ s₂ hr
  exists r

/-- The union of bisimilarity with any bisimulation is bisimilarity. -/
@[scoped grind =, simp]
theorem Bisimilarity.gfp (r : State₁ → State₂ → Prop) (h : IsBisimulation lts₁ lts₂ r) :
    (· ~[lts₁,lts₂] ·) ⊔ r = (· ~[lts₁,lts₂] ·) := sup_eq_left.mpr h.le_bisimilarity

/-- `calc` support for bisimilarity. -/
instance : Trans (· ~[lts₁,lts₂] ·) (· ~[lts₂,lts₃] ·) (· ~[lts₁,lts₃] ·) where
  trans := Bisimilarity.trans

/-! ## Stratification of bisimilarity

Following [Sangiorgi2011], the strata start with the universal relation and require matching
transitions into the preceding stratum at successors. Limit ordinals intersect earlier strata;
the added top ordinal `⊤` intersects all ordinal strata and equals bisimilarity.
-/

/-- The one-step bisimulation operator. -/
def bisimulationStep (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) :
    (State₁ → State₂ → Prop) →o (State₁ → State₂ → Prop) where
  toFun r s₁ s₂ := ∀ μ,
    (∀ s₁', lts₁.Tr s₁ μ s₁' → ∃ s₂', lts₂.Tr s₂ μ s₂' ∧ r s₁' s₂') ∧
    (∀ s₂', lts₂.Tr s₂ μ s₂' → ∃ s₁', lts₁.Tr s₁ μ s₁' ∧ r s₁' s₂')
  monotone' := by
    intro r s (hrs : ∀ x y, r x y → s x y) s₁ s₂ h μ
    grind only

theorem isBisimulation_iff_le_bisimulationStep :
    IsBisimulation lts₁ lts₂ r ↔ r ≤ bisimulationStep lts₁ lts₂ r := Iff.rfl

/-- The greatest fixed point of the one-step operator is bisimilarity. -/
theorem bisimulationStep_gfp : (bisimulationStep lts₁ lts₂).gfp = (· ~[lts₁,lts₂] ·) :=
  le_antisymm
    ((isBisimulation_iff_le_bisimulationStep.mpr
      ((bisimulationStep lts₁ lts₂).gfp_le_map le_rfl)).le_bisimilarity)
    ((bisimulationStep lts₁ lts₂).le_gfp
      (isBisimulation_iff_le_bisimulationStep.mp (Bisimilarity.isBisimulation ..)))

/-- The approximation of bisimilarity indexed by ordinals with an added top endpoint.
Ordinal stages use `OrdinalApprox.gfpApprox`; at `⊤` we intersect all ordinal stages,
corresponding to the infinity approximation in [Sangiorgi2011]. -/
def BisimilarityApprox (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) :
    WithTop Ordinal → State₁ → State₂ → Prop :=
  WithTop.recTopCoe (⨅ o, OrdinalApprox.gfpApprox (bisimulationStep lts₁ lts₂) ⊤ o)
    (OrdinalApprox.gfpApprox (bisimulationStep lts₁ lts₂) ⊤)

/-- Infix notation for the ordinal-indexed approximation of bisimilarity of two states. -/
scoped notation s:max " ~[" lts₁ "," lts₂ ";" o "] " s':max =>
  BisimilarityApprox lts₁ lts₂ o s s'

/-- The ordinal-indexed approximation of bisimilarity within one LTS. -/
abbrev HomBisimilarityApprox (lts : LTS State Label) (o : WithTop Ordinal) :=
  BisimilarityApprox lts lts o

/-- Infix notation for the ordinal-indexed approximation of homogeneous bisimilarity. -/
scoped notation s:max " ~[" lts ";" o "] " s':max => HomBisimilarityApprox lts o s s'

/-- At an ordinal index, the approximation is mathlib's greatest-fixed-point approximant. -/
theorem BisimilarityApprox.coe_eq (o : Ordinal) :
    (· ~[lts₁,lts₂;o] ·) = OrdinalApprox.gfpApprox (bisimulationStep lts₁ lts₂) ⊤ o := rfl

/-- The top endpoint intersects all ordinal strata. -/
theorem BisimilarityApprox.top_eq_iInf :
    (· ~[lts₁,lts₂;⊤] ·) = ⨅ o : Ordinal, (· ~[lts₁,lts₂;o] ·) := rfl

/-- Membership at the top endpoint means membership at every ordinal stage. -/
theorem BisimilarityApprox.top_iff : s₁ ~[lts₁,lts₂;⊤] s₂ ↔
    ∀ o : Ordinal, s₁ ~[lts₁,lts₂;o] s₂ := by
  simp [BisimilarityApprox.top_eq_iInf]

/-- The intersection of all ordinal strata is bisimilarity, for arbitrary LTSs. -/
theorem BisimilarityApprox.top_eq_bisimilarity (lts₁ : LTS State₁ Label)
    (lts₂ : LTS State₂ Label) : (· ~[lts₁,lts₂;⊤] ·) = (· ~[lts₁,lts₂] ·) :=
  (OrdinalApprox.prevFixed_eq_iInf_gfpApprox _ le_top).symm.trans
    ((OrderHom.prevFixed_top_coe _).trans bisimulationStep_gfp)

/-- Membership at the top endpoint is bisimilarity, for arbitrary LTSs. -/
@[simp]
theorem BisimilarityApprox.top_iff_bisimilarity :
    s₁ ~[lts₁,lts₂;⊤] s₂ ↔ s₁ ~[lts₁,lts₂] s₂ :=
  congr($(BisimilarityApprox.top_eq_bisimilarity lts₁ lts₂) s₁ s₂)

/-- The zeroth stratum is the universal relation. -/
theorem BisimilarityApprox.zero_eq : (· ~[lts₁,lts₂;0] ·) = ⊤ :=
  OrdinalApprox.gfpApprox_zero _

/-- A successor stratum applies the one-step operator to the preceding stratum. -/
theorem BisimilarityApprox.succ {o : WithTop Ordinal} :
    (· ~[lts₁,lts₂;o + 1] ·) =
      bisimulationStep lts₁ lts₂ (· ~[lts₁,lts₂;o] ·) := by
  cases o with
  | top =>
    rw [WithTop.top_add, BisimilarityApprox.top_eq_bisimilarity, ← bisimulationStep_gfp]
    exact (bisimulationStep lts₁ lts₂).map_gfp.symm
  | coe o => exact OrdinalApprox.gfpApprox_add_one _ le_top o

/-- Every pair of states belongs to the zeroth stratum. -/
@[scoped grind ., simp]
theorem BisimilarityApprox.zero : s₁ ~[lts₁,lts₂;0] s₂ := by simp [BisimilarityApprox.zero_eq]

/-- Membership in a successor stratum is given by matching transitions into the previous one. -/
theorem BisimilarityApprox.succ_iff {o : WithTop Ordinal} : s₁ ~[lts₁,lts₂;o + 1] s₂ ↔
    ∀ μ,
      (∀ s₁', lts₁.Tr s₁ μ s₁' →
        ∃ s₂', lts₂.Tr s₂ μ s₂' ∧ s₁' ~[lts₁,lts₂;o] s₂') ∧
      (∀ s₂', lts₂.Tr s₂ μ s₂' →
        ∃ s₁', lts₁.Tr s₁ μ s₁' ∧ s₁' ~[lts₁,lts₂;o] s₂') :=
  congr($BisimilarityApprox.succ s₁ s₂)

/-- Follow a transition by the first state, consuming one level of approximation. -/
theorem BisimilarityApprox.follow_fst {o : WithTop Ordinal} (h : s₁ ~[lts₁,lts₂;o + 1] s₂)
    (htr : lts₁.Tr s₁ μ s₁') :
    ∃ s₂', lts₂.Tr s₂ μ s₂' ∧ s₁' ~[lts₁,lts₂;o] s₂' :=
  (BisimilarityApprox.succ_iff.mp h μ).1 s₁' htr

/-- Follow a transition by the second state, consuming one level of approximation. -/
theorem BisimilarityApprox.follow_snd {o : WithTop Ordinal} (h : s₁ ~[lts₁,lts₂;o + 1] s₂)
    (htr : lts₂.Tr s₂ μ s₂') :
    ∃ s₁', lts₁.Tr s₁ μ s₁' ∧ s₁' ~[lts₁,lts₂;o] s₂' :=
  (BisimilarityApprox.succ_iff.mp h μ).2 s₂' htr

/-- The strata decrease with the ordinal index. -/
theorem BisimilarityApprox.antitone : Antitone (fun o => (· ~[lts₁,lts₂;o] ·)) := by
  intro o o' hoo'
  cases o with
  | top => rw [eq_top_iff.mpr hoo']
  | coe o =>
    cases o' with
    | top => exact iInf_le _ o
    | coe o' => exact OrdinalApprox.gfpApprox_anti_right _ (WithTop.coe_le_coe.mp hoo')

/-- The restriction to natural-number indices is decreasing. -/
theorem BisimilarityApprox.antitone_nat : Antitone (fun n : ℕ => (· ~[lts₁,lts₂;n] ·)) := by
  intro m n h
  exact BisimilarityApprox.antitone (by exact_mod_cast h)

/-- Membership in a stratum implies membership in every earlier stratum. -/
theorem BisimilarityApprox.of_ge {o o' : WithTop Ordinal}
    (h : s₁ ~[lts₁,lts₂;o'] s₂) (hoo' : o ≤ o') : s₁ ~[lts₁,lts₂;o] s₂ :=
  BisimilarityApprox.antitone hoo' _ _ h

/-- `BisimilarityApprox.of_ge` for natural number indices. -/
theorem BisimilarityApprox.of_ge_nat {m n : ℕ}
    (h : s₁ ~[lts₁,lts₂;n] s₂) (hmn : m ≤ n) : s₁ ~[lts₁,lts₂;m] s₂ :=
  BisimilarityApprox.antitone_nat hmn _ _ h

/-- Each successor stratum is contained in the preceding stratum. -/
theorem BisimilarityApprox.succ_le (o : Ordinal) :
    (· ~[lts₁,lts₂;o + 1] ·) ≤ (· ~[lts₁,lts₂;o] ·) :=
  BisimilarityApprox.antitone (WithTop.coe_le_coe.mpr (lt_add_one o).le)

theorem BisimilarityApprox.limit_iff {o : Ordinal} (ho : Order.IsSuccLimit o) :
    s₁ ~[lts₁,lts₂;o] s₂ ↔ ∀ o' < o, s₁ ~[lts₁,lts₂;o'] s₂ := by
  simp [OrdinalApprox.gfpApprox_of_isSuccLimit _ ho, BisimilarityApprox]

theorem BisimilarityApprox.natCast_eq_iterate (n : ℕ) :
    (· ~[lts₁,lts₂;n] ·) = (bisimulationStep lts₁ lts₂)^[n] ⊤ := by
  induction n with
  | zero => exact BisimilarityApprox.zero_eq
  | succ n ih => simp [BisimilarityApprox.succ, ih, Function.iterate_succ_apply']

open scoped Ordinal

/-- The omega stratum is the intersection of the finite strata. -/
theorem BisimilarityApprox.omega_iff : s₁ ~[lts₁,lts₂;ω] s₂ ↔
    ∀ n : ℕ, s₁ ~[lts₁,lts₂;n] s₂ := by
  simp [BisimilarityApprox.limit_iff Ordinal.isSuccLimit_omega0, Ordinal.lt_omega0]

/-- Bisimilar states belong to every ordinal stratum. -/
theorem Bisimilarity.approx (h : s₁ ~[lts₁,lts₂] s₂) (o : WithTop Ordinal) :
    s₁ ~[lts₁,lts₂;o] s₂ :=
  (BisimilarityApprox.top_iff_bisimilarity.mpr h).of_ge le_top

/-- For all LTSs, some ordinal stratum coincides with bisimilarity. -/
theorem BisimilarityApprox.exists_eq_bisimilarity (lts₁ : LTS State₁ Label)
    (lts₂ : LTS State₂ Label) :
    ∃ o : Ordinal, (· ~[lts₁,lts₂;o] ·) = (· ~[lts₁,lts₂] ·) := by
  obtain ⟨o, ho⟩ := OrdinalApprox.gfp_mem_range_gfpApprox (bisimulationStep lts₁ lts₂)
  exact ⟨o, ho.trans bisimulationStep_gfp⟩

/-- Once a stratum reaches bisimilarity, every later stratum equals bisimilarity. -/
theorem BisimilarityApprox.eq_bisimilarity_of_le {o o' : WithTop Ordinal} (hoo' : o ≤ o')
    (ho : (· ~[lts₁,lts₂;o] ·) = (· ~[lts₁,lts₂] ·)) :
    (· ~[lts₁,lts₂;o'] ·) = (· ~[lts₁,lts₂] ·) := by
  apply le_antisymm
  · rw [← ho]
    exact BisimilarityApprox.antitone hoo'
  · exact fun _ _ h => h.approx o'

/-- The ordinal stratification eventually stabilizes at bisimilarity. -/
theorem BisimilarityApprox.stabilizes (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) :
    ∃ o : Ordinal, ∀ o' : WithTop Ordinal, (o : WithTop Ordinal) ≤ o' →
      (· ~[lts₁,lts₂;o'] ·) = (· ~[lts₁,lts₂] ·) := by
  obtain ⟨o, ho⟩ := BisimilarityApprox.exists_eq_bisimilarity lts₁ lts₂
  exact ⟨o, fun _ hoo' => BisimilarityApprox.eq_bisimilarity_of_le hoo' ho⟩

/-- Each ordinal stratum is symmetric. -/
@[symm]
theorem BisimilarityApprox.symm {State₁ State₂ : Type*}
    {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {s₁ : State₁} {s₂ : State₂}
    (h : s₁ ~[lts₁,lts₂;o] s₂) :
    s₂ ~[lts₂,lts₁;o] s₁ := by
  cases o with
  | top =>
    rw [BisimilarityApprox.top_iff_bisimilarity] at h ⊢
    exact h.symm
  | coe o =>
    induction o using Ordinal.limitRecOn generalizing s₁ s₂ with
    | zero => exact BisimilarityApprox.zero
    | add_one o ih =>
      simp only [WithTop.coe_add, WithTop.coe_one] at h ⊢
      grind [BisimilarityApprox.succ_iff, h.follow_fst, h.follow_snd]
    | limit o ho ih =>
      grind [BisimilarityApprox.limit_iff]

/-- Ordinal strata compose across LTSs in a common state universe at the same ordinal index. -/
theorem BisimilarityApprox.trans {State₁ State₂ State₃ : Type u}
    {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {lts₃ : LTS State₃ Label}
    {s₁ : State₁} {s₂ : State₂} {s₃ : State₃} {o : WithTop Ordinal}
    (h₁ : s₁ ~[lts₁,lts₂;o] s₂)
    (h₂ : s₂ ~[lts₂,lts₃;o] s₃) :
    s₁ ~[lts₁,lts₃;o] s₃ := by
  cases o with
  | top =>
    rw [BisimilarityApprox.top_iff_bisimilarity] at h₁ h₂ ⊢
    exact h₁.trans h₂
  | coe o =>
    induction o using Ordinal.limitRecOn generalizing s₁ s₂ s₃ with
    | zero => exact BisimilarityApprox.zero
    | add_one o ih =>
      simp only [WithTop.coe_add, WithTop.coe_one] at h₁ h₂ ⊢
      grind only [BisimilarityApprox.succ_iff]
    | limit o ho ih =>
      grind only [BisimilarityApprox.limit_iff]

/-- Finite strata compose even when the state types inhabit different universes. -/
theorem BisimilarityApprox.trans_nat {n : ℕ}
    (h₁ : s₁ ~[lts₁,lts₂;(n : Ordinal)] s₂)
    (h₂ : s₂ ~[lts₂,lts₃;(n : Ordinal)] s₃) :
    s₁ ~[lts₁,lts₃;n] s₃ := by
  induction n generalizing s₁ s₂ s₃ with
  | zero => exact BisimilarityApprox.zero
  | succ n ih =>
    push_cast at h₁ h₂ ⊢
    refine succ_iff.mpr fun μ ↦ ⟨fun s₁' htr₁ ↦ ?_, fun s₃' htr₃ ↦ ?_⟩
    · have ⟨s₂', htr₂, hsim⟩ := h₁.follow_fst htr₁
      have ⟨s₃', htr₃, hsim'⟩ := h₂.follow_fst htr₂
      exact ⟨s₃', htr₃, ih hsim hsim'⟩
    · have ⟨s₂, htr₂, hsim⟩ := h₂.follow_snd htr₃
      have ⟨s₁', htr₁, hsim'⟩ := h₁.follow_snd htr₂
      exact ⟨s₁', htr₁, ih hsim' hsim⟩

/-- Homogeneous ordinal strata are reflexive. -/
@[refl]
theorem HomBisimilarityApprox.refl (o : WithTop Ordinal) (s : State) :
    s ~[lts;o] s := (HomBisimilarity.refl s).approx o

/-- Each homogeneous ordinal stratum is an equivalence relation. -/
theorem HomBisimilarityApprox.eqv (o : WithTop Ordinal) : Equivalence (· ~[lts;o] ·) where
  refl := HomBisimilarityApprox.refl o
  symm := BisimilarityApprox.symm
  trans := BisimilarityApprox.trans

theorem BisimilarityApprox.trans_omega (h₁ : s₁ ~[lts₁,lts₂;ω] s₂)
    (h₂ : s₂ ~[lts₂,lts₃;ω] s₃) : s₁ ~[lts₁,lts₃;ω] s₃ :=
  BisimilarityApprox.omega_iff.mpr fun n =>
    (BisimilarityApprox.omega_iff.mp h₁ n).trans_nat (BisimilarityApprox.omega_iff.mp h₂ n)

/-- If the second LTS is image-finite, the omega approximation is a simulation. -/
theorem BisimilarityApprox.isSimulation_omega [lts₂.ImageFinite] :
    IsSimulation lts₁ lts₂ (· ~[lts₁,lts₂;ω] ·) := by
  intro s₁ s₂ h μ s₁' htr
  classical
  by_contra! hnone
  -- If every derivative fails at some depth, finiteness gives a common depth of failure.
  have hbad : ∀ t : lts₂.image s₂ μ, ∃ n : ℕ, ¬(s₁' ~[lts₁,lts₂;(n : Ordinal)] t) := by
    simp [omega_iff] at hnone
    simpa
  choose depth hdepth using hbad
  obtain ⟨N, hN⟩ := Finite.exists_le depth
  have hs : s₁ ~[lts₁,lts₂;(N : Ordinal) + 1] s₂ := by
    simpa using BisimilarityApprox.omega_iff.mp h (N + 1)
  obtain ⟨t, ht, hr⟩ := hs.follow_fst htr
  exact hdepth ⟨t, ht⟩ (hr.of_ge_nat (hN ⟨t, ht⟩))

/-- If the first LTS is image-finite, the inverse of the omega approximation is a simulation. -/
theorem BisimilarityApprox.flip_isSimulation_omega [lts₁.ImageFinite] :
    IsSimulation lts₂ lts₁ (flip (· ~[lts₁,lts₂;ω] ·)) := fun _ _ h μ _ htr =>
  have ⟨s₁', ht, hr⟩ := isSimulation_omega h.symm μ _ htr
  ⟨s₁', ht, hr.symm⟩

/-- On image-finite LTSs, the omega approximation is a bisimulation.
This is the image-finite stratification result in [Sangiorgi2011]. -/
theorem BisimilarityApprox.isBisimulation_omega [lts₁.ImageFinite] [lts₂.ImageFinite] :
    IsBisimulation lts₁ lts₂ (· ~[lts₁,lts₂;ω] ·) :=
  IsBisimulation.isSimulation_iff.mpr ⟨isSimulation_omega, flip_isSimulation_omega⟩

/-- If the second LTS is image-finite, a transition by the first state has a matching
derivative related at every finite depth. -/
theorem BisimilarityApprox.follow_fst_omega [lts₂.ImageFinite]
    (h : s₁ ~[lts₁,lts₂;ω] s₂) (htr : lts₁.Tr s₁ μ s₁') :
    ∃ s₂', lts₂.Tr s₂ μ s₂' ∧ s₁' ~[lts₁,lts₂;ω] s₂' :=
  isSimulation_omega.follow h htr

/-- If the first LTS is image-finite, a transition by the second state has a matching
derivative related at every finite depth. -/
theorem BisimilarityApprox.follow_snd_omega [lts₁.ImageFinite]
    (h : s₁ ~[lts₁,lts₂;ω] s₂) (htr : lts₂.Tr s₂ μ s₂') :
    ∃ s₁', lts₁.Tr s₁ μ s₁' ∧ s₁' ~[lts₁,lts₂;ω] s₂' :=
  flip_isSimulation_omega.follow h htr

/-- On image-finite LTSs, membership in every finite stratum implies bisimilarity. -/
theorem BisimilarityApprox.bisimilarity_of_omega [lts₁.ImageFinite] [lts₂.ImageFinite]
    (h : s₁ ~[lts₁,lts₂;ω] s₂) : s₁ ~[lts₁,lts₂] s₂ :=
  BisimilarityApprox.isBisimulation_omega.le_bisimilarity _ _ h

/-- On image-finite LTSs, membership in the omega approximation is bisimilarity. -/
@[simp]
theorem BisimilarityApprox.omega_iff_bisimilarity [lts₁.ImageFinite] [lts₂.ImageFinite] :
    s₁ ~[lts₁,lts₂;ω] s₂ ↔ s₁ ~[lts₁,lts₂] s₂ :=
  ⟨BisimilarityApprox.bisimilarity_of_omega, (fun h => h.approx ω)⟩

/-- On image-finite LTSs, the omega approximation coincides with bisimilarity. -/
theorem BisimilarityApprox.omega_eq_bisimilarity (lts₁ : LTS State₁ Label)
    (lts₂ : LTS State₂ Label) [lts₁.ImageFinite] [lts₂.ImageFinite] :
    (· ~[lts₁,lts₂;ω] ·) = (· ~[lts₁,lts₂] ·) := by
  ext s₁ s₂
  exact BisimilarityApprox.omega_iff_bisimilarity

/-- On image-finite LTSs, every stratum at or beyond omega is bisimilarity. -/
theorem BisimilarityApprox.eq_bisimilarity [lts₁.ImageFinite] [lts₂.ImageFinite]
    {o : WithTop Ordinal} (ho : (ω : Ordinal) ≤ o) :
    (· ~[lts₁,lts₂;o] ·) = (· ~[lts₁,lts₂] ·) :=
  BisimilarityApprox.eq_bisimilarity_of_le ho (BisimilarityApprox.omega_eq_bisimilarity ..)

/-- On image-finite LTSs, membership in any stratum at or beyond omega is bisimilarity. -/
theorem BisimilarityApprox.iff_bisimilarity [lts₁.ImageFinite] [lts₂.ImageFinite]
    {o : WithTop Ordinal} (ho : (ω : Ordinal) ≤ o) :
    s₁ ~[lts₁,lts₂;o] s₂ ↔ s₁ ~[lts₁,lts₂] s₂ :=
  congr($(BisimilarityApprox.eq_bisimilarity ho) s₁ s₂)

section Order

/-! ## Order properties -/

instance : Max {r // IsBisimulation lts₁ lts₂ r} where
  max r s := ⟨r.1 ⊔ s.1, IsBisimulation.sup r.2 s.2⟩

@[simp] lemma coe_sup (r s : {r // IsBisimulation lts₁ lts₂ r}) :
    (↑(r ⊔ s) : State₁ → State₂ → Prop) = (r : State₁ → State₂ → Prop) ⊔ s := rfl

/-- Bisimulations equipped with union form a join-semilattice. -/
instance : SemilatticeSup {r // IsBisimulation lts₁ lts₂ r} where
  sup r s := r ⊔ s
  le_sup_left r s := by simp [←Subtype.coe_le_coe]
  le_sup_right r s := by simp [←Subtype.coe_le_coe]
  sup_le r s t := by simp [←Subtype.coe_le_coe]; tauto

/-- The empty (heterogeneous) relation is a bisimulation. -/
@[scoped grind .]
theorem IsBisimulation.bot : IsBisimulation lts₁ lts₂ Relation.emptyHRelation := by
  intro s₁ s₂ hr
  cases hr

instance : Bot {r // IsBisimulation lts₁ lts₂ r} :=
  ⟨Relation.emptyHRelation, IsBisimulation.bot⟩

instance : Top {r // IsBisimulation lts₁ lts₂ r} :=
  ⟨(· ~[lts₁,lts₂] ·), Bisimilarity.isBisimulation ..⟩

/-- In the inclusion order on bisimulations:

- The empty relation is the bottom element.
- Bisimilarity is the top element.
-/
instance : BoundedOrder {r // IsBisimulation lts₁ lts₂ r} where
  top := ⊤
  bot := ⊥
  le_top r := r.property.le_bisimilarity
  bot_le r := by simp [Bot.bot, LE.le]

end Order

/-! ## Bisimulation up-to -/

/-- The closure of `r` under bisimilarity in each LTS: `s₁` and `s₂` are related if there are
`t₁` and `t₂` with `s₁ ~[lts₁] t₁`, `r t₁ t₂`, and `t₂ ~[lts₂] s₂`. -/
def UpToHomBisimilarity (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (r : State₁ → State₂ → Prop) : State₁ → State₂ → Prop :=
  Relation.Comp (· ~[lts₁] ·) (Relation.Comp r (· ~[lts₂] ·))

/-- A relation `r` is a bisimulation up to homogeneous bisimilarity if, whenever it relates two
states, their transitions can be matched with derivatives related by
`UpToHomBisimilarity lts₁ lts₂ r`. -/
def IsBisimulationUpTo (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (r : State₁ → State₂ → Prop) : Prop :=
  ∀ ⦃s₁ s₂⦄, r s₁ s₂ → ∀ μ, (
    (∀ s₁', lts₁.Tr s₁ μ s₁' → ∃ s₂', lts₂.Tr s₂ μ s₂' ∧
      (UpToHomBisimilarity lts₁ lts₂ r) s₁' s₂')
    ∧
    (∀ s₂', lts₂.Tr s₂ μ s₂' → ∃ s₁', lts₁.Tr s₁ μ s₁' ∧
      (UpToHomBisimilarity lts₁ lts₂ r) s₁' s₂')
  )

/-- If `r` is a bisimulation up to bisimilarity, its closure
`UpToHomBisimilarity lts₁ lts₂ r` is a bisimulation. -/
@[scoped grind →]
theorem IsBisimulationUpTo.isBisimulation (h : IsBisimulationUpTo lts₁ lts₂ r) :
    IsBisimulation lts₁ lts₂ (UpToHomBisimilarity lts₁ lts₂ r) := by
  intro s₁ s₂ hr μ
  rcases hr with ⟨s₁b, hr1b, s₂b, hrb, hr2b⟩
  constructor
  case left =>
    intro s₁' htr1
    obtain ⟨s₁b', hs₁b'tr, hs₁b'r⟩ := hr1b.follow_fst htr1
    obtain ⟨s₂b', hs₂b'tr, hs₂b'r⟩ := (h hrb μ).1 s₁b' hs₁b'tr
    obtain ⟨s₂', hs₂btr, hs₂br⟩ := hr2b.follow_fst hs₂b'tr
    use s₂', hs₂btr
    obtain ⟨smid1, hsmidb, smid2, hsmidr, hsmidrb⟩ := hs₂b'r
    use smid1, hs₁b'r.trans hsmidb, smid2, hsmidr
    exact hsmidrb.trans hs₂br
  case right =>
    intro s₂' htr2
    obtain ⟨s₂b', hs₂b'tr, hs₂b'r⟩ := hr2b.follow_snd htr2
    obtain ⟨s₁b', hs₁b'tr, hs₁b'r⟩ := (h hrb μ).2 s₂b' hs₂b'tr
    obtain ⟨s₁', hs₁btr, hs₁br⟩ := hr1b.follow_snd hs₁b'tr
    use s₁', hs₁btr
    obtain ⟨smid1, hsmidb, smid2, hsmidr, hsmidrb⟩ := hs₁b'r
    use smid1, hs₁br.trans hsmidb, smid2, hsmidr
    exact hsmidrb.trans hs₂b'r

/-- A bisimulation up to bisimilarity relates only bisimilar states. -/
theorem IsBisimulationUpTo.le_bisimilarity (h : IsBisimulationUpTo lts₁ lts₂ r) :
    r ≤ (· ~[lts₁,lts₂] ·) := by
  intro s₁ s₂ hr
  exact h.isBisimulation.le_bisimilarity s₁ s₂
    ⟨s₁, HomBisimilarity.refl s₁, s₂, hr, HomBisimilarity.refl s₂⟩

/-- If two states are related by a bisimulation, they can mimic each other's multi-step
transitions. -/
theorem IsBisimulation.bisim_trace (hb : IsBisimulation lts₁ lts₂ r) (hr : r s₁ s₂) :
    ∀ μs s₁', lts₁.MTr s₁ μs s₁' → ∃ s₂', lts₂.MTr s₂ μs s₂' ∧ r s₁' s₂' :=
  hb.isSimulation.sim_trace hr

/-! ## Relation to trace equivalence -/

/-- Any bisimulation implies trace equivalence. -/
@[scoped grind =>]
theorem IsBisimulation.traceEq (hb : IsBisimulation lts₁ lts₂ r) (hr : r s₁ s₂) :
    s₁ ~tr[lts₁,lts₂] s₂ := (hb.simulationEquiv hr).traceEq

/-- Bisimilarity is included in trace equivalence. -/
@[scoped grind .]
theorem Bisimilarity.le_traceEq : (· ~[lts₁,lts₂] ·) ≤ TraceEq lts₁ lts₂ := by
  intro s₁ s₂ h
  obtain ⟨r, hr, hb⟩ := h
  apply hb.traceEq hr

/- One of the standard motivating examples for bisimulation: `1` and `5` are trace equivalent, but
not bisimilar. -/
private inductive BisimMotTr : ℕ → Char → ℕ → Prop where
-- First process, `1`
| one2two : BisimMotTr 1 'a' 2
| two2three : BisimMotTr 2 'b' 3
| two2four : BisimMotTr 2 'c' 4
-- Second process, `5`
| five2six : BisimMotTr 5 'a' 6
| six2seven : BisimMotTr 6 'b' 7
| five2eight : BisimMotTr 5 'a' 8
| eight2nine : BisimMotTr 8 'c' 9

/-- In general, trace equivalence is not a bisimulation (extra conditions are needed, see for
example `Bisimulation.deterministic_trace_eq_is_bisim`). -/
theorem IsBisimulation.traceEq_not_bisim :
    ∃ (State : Type) (Label : Type) (lts : LTS State Label),
      ¬(IsHomBisimulation lts (HomTraceEq lts)) := by
  let lts := LTS.mk BisimMotTr
  exists ℕ, Char, lts
  intro h
  have htreq : (1 ~tr[lts] 5) := by
    have htraces₁ : lts.traces 1 = {[], ['a'], ['a', 'b'], ['a', 'c']} := by
      ext μs
      constructor
      case mp =>
        rintro ⟨_, (_ | ⟨⟨_⟩, (_ | ⟨(_ | _), (_ | ⟨⟨_⟩, _⟩)⟩)⟩)⟩
        all_goals simp
      case mpr =>
        rintro (rfl | rfl | rfl | rfl)
        · exact ⟨1, .refl⟩
        · exact ⟨2, MTr.single lts .one2two⟩
        · exact ⟨3, MTr.stepL .one2two <| MTr.single lts .two2three⟩
        · exact ⟨4, MTr.stepL .one2two <| MTr.single lts .two2four⟩
    have htraces₅ : lts.traces 5 = {[], ['a'], ['a', 'b'], ['a', 'c']} := by
      ext μs
      constructor
      case mp =>
        rintro ⟨_, (_ | ⟨(_ | _), (_ | ⟨⟨_⟩, (_ | ⟨⟨_⟩, _⟩)⟩)⟩)⟩
        all_goals simp
      case mpr =>
        rintro (rfl | rfl | rfl | rfl)
        · exact ⟨5, .refl⟩
        · exact ⟨6, MTr.single lts .five2six⟩
        · exact ⟨7, MTr.stepL .five2six <| MTr.single lts .six2seven⟩
        · exact ⟨9, MTr.stepL .five2eight <| MTr.single lts .eight2nine⟩
    exact htraces₁.trans htraces₅.symm
  obtain ⟨h1, h2⟩ := h htreq 'a'
  obtain ⟨s₂', htr5, cih⟩ := h1 2 (by constructor)
  have htraces₂ : {['b'], ['c']} ⊆ lts.traces 2 := by
    intro μs h
    rcases h with (rfl | rfl)
    · refine ⟨3, MTr.single lts .two2three⟩
    · refine ⟨4, MTr.single lts .two2four⟩
  cases htr5
  case five2six =>
    suffices ['c'] ∉ lts.traces 6 by grind [TraceEq]
    rintro ⟨_, (_ | h)⟩
    cases h
  case five2eight =>
    suffices ['b'] ∉ lts.traces 8 by grind [TraceEq]
    rintro ⟨_, (_ | h)⟩
    cases h

/-- In general, bisimilarity and trace equivalence are distinct. -/
theorem Bisimilarity.bisimilarity_neq_traceEq :
    ∃ (State : Type) (Label : Type) (lts : LTS State Label),
      (· ~[lts] ·) ≠ HomTraceEq lts := by
  obtain ⟨State, Label, lts, h⟩ := IsBisimulation.traceEq_not_bisim
  grind [Bisimilarity.isBisimulation lts lts]

/-- In any deterministic LTS, trace equivalence is a bisimulation. -/
theorem IsBisimulation.deterministic_traceEq_isBisimulation
    {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    [lts₁.Deterministic] [lts₂.Deterministic] :
    (IsBisimulation lts₁ lts₂ (TraceEq lts₁ lts₂)) := by
  rw [IsBisimulation.isSimulation_iff, TraceEq.flip_eq]
  exact ⟨Deterministic.isSimulation_traceEq, Deterministic.isSimulation_traceEq⟩

/-- In deterministic LTSs, trace equivalence implies bisimilarity. -/
theorem Bisimilarity.deterministic_traceEq_bisim {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    [lts₁.Deterministic] [lts₂.Deterministic] (h : s₁ ~tr[lts₁,lts₂] s₂) :
    (s₁ ~[lts₁,lts₂] s₂) := by
  use TraceEq lts₁ lts₂, h, IsBisimulation.deterministic_traceEq_isBisimulation

/-- In a deterministic lts, bisimilarity, trace equivalence, and simulation equivalence are
equivalent to one-another. -/
theorem Deterministic.bisim_tfae {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    [lts₁.Deterministic] [lts₂.Deterministic] (s₁ : State₁) (s₂ : State₂) :
    [s₁ ~[lts₁,lts₂] s₂, s₁ ~tr[lts₁,lts₂] s₂, s₁ ≤≥[lts₁,lts₂] s₂].TFAE := by
  tfae_have 2 ↔ 3 := Deterministic.traceEq_iff_simulationEquiv s₁ s₂
  tfae_have 1 → 2 := Bisimilarity.le_traceEq s₁ s₂
  tfae_have 2 → 1 := Bisimilarity.deterministic_traceEq_bisim
  tfae_finish

/-- In deterministic LTSs, bisimilarity and trace equivalence coincide. -/
theorem Bisimilarity.deterministic_bisim_eq_traceEq
    {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    [lts₁.Deterministic] [lts₂.Deterministic] : (· ~[lts₁,lts₂] ·) = TraceEq lts₁ lts₂ := by
  ext s₁ s₂
  exact (Deterministic.bisim_tfae s₁ s₂).out 1 2

/-- Homogeneous bisimilarity can also be characterized through symmetric simulations. -/
theorem HomBisimilarity.symm_simulation :
  (· ~[lts] ·) =
    fun s₁ s₂ => ∃ r, r s₁ s₂ ∧ Std.Symm r ∧ IsHomSimulation lts r := by
  ext s₁ s₂
  constructor
  · intro h
    use (· ~[lts] ·), h
    exact ⟨⟨fun _ _ => Bisimilarity.symm⟩, (Bisimilarity.isBisimulation lts lts).isSimulation⟩
  · intro ⟨r, hrel, ⟨hsymm⟩, hsim⟩
    use r, hrel
    have : r = flip r := by grind [flip]
    simpa [IsBisimulation.isSimulation_iff, ←this]

end Bisimulation

section WeakBisimulation

/-! ## Weak bisimulation and weak bisimilarity -/

/-- A weak bisimulation is similar to a `Bisimulation`, but allows for the related processes to do
internal work. Technically, this is defined as a `Bisimulation` on the saturation of the LTSs. -/
def IsWeakBisimulation [HasTau Label] (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (r : State₁ → State₂ → Prop) :=
  IsBisimulation (lts₁.saturate) (lts₂.saturate) r

/-- A homogeneous bisimulation is a bisimulation where the underlying LTSs are the same. -/
abbrev IsHomWeakBisimulation [HasTau Label] (lts : LTS State Label) := IsWeakBisimulation lts lts

/-- Two states are weakly bisimilar if they are related by some weak bisimulation. -/
def WeakBisimilarity [HasTau Label] (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) :
    State₁ → State₂ → Prop :=
  fun s₁ s₂ =>
    ∃ r : State₁ → State₂ → Prop, r s₁ s₂ ∧ IsWeakBisimulation lts₁ lts₂ r

/-- Notation for weak bisimilarity. -/
scoped notation s:max " ≈[" lts₁ "," lts₂ "] " s':max => WeakBisimilarity lts₁ lts₂ s s'

/-- Homogeneous bisimilarity is bisimilarity where the underlying LTSs are the same. -/
abbrev HomWeakBisimilarity [HasTau Label] (lts : LTS State Label) := WeakBisimilarity lts lts

/-- Notation for homogeneous bisimilarity. -/
scoped notation s:max " ≈[" lts "] " s':max => HomWeakBisimilarity lts s s'

/-- An `SWBisimulation` is a more convenient definition of weak bisimulation, because the challenge
is a single transition. We prove later that this technique is sound, following a strategy inspired
by [Sangiorgi2011]. -/
def IsSWBisimulation [HasTau Label] (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (r : State₁ → State₂ → Prop) : Prop :=
  ∀ ⦃s₁ s₂⦄, r s₁ s₂ → ∀ μ, (
    (∀ s₁', lts₁.Tr s₁ μ s₁' → ∃ s₂', lts₂.STr s₂ μ s₂' ∧ r s₁' s₂')
    ∧
    (∀ s₂', lts₂.Tr s₂ μ s₂' → ∃ s₁', lts₁.STr s₁ μ s₁' ∧ r s₁' s₂')
  )

lemma IsSWBisimulation.isSimulation [HasTau Label] (h : IsSWBisimulation lts₁ lts₂ r) :
    IsSimulation lts₁ lts₂.saturate r := by
  intro s₁ s₂ hr μ
  exact (h hr μ).1

lemma IsSWBisimulation.isSimulation_flip [HasTau Label] (h : IsSWBisimulation lts₁ lts₂ r) :
    IsSimulation lts₂ lts₁.saturate (flip r) := by
  intro s₂ s₁ hr μ
  exact (h hr μ).2

theorem IsSWBisimulation.iff_isSimulation [HasTau Label] :
    IsSWBisimulation lts₁ lts₂ r ↔
      IsSimulation lts₁ lts₂.saturate r ∧ IsSimulation lts₂ lts₁.saturate (flip r) := by
  refine ⟨fun h => ⟨h.isSimulation, h.isSimulation_flip⟩, ?_⟩
  intro ⟨h, hflip⟩ s₁ s₂ hr μ
  exact ⟨h hr μ, hflip hr μ⟩

/-- We can now prove that any relation is a `WeakBisimulation` iff it is an `SWBisimulation`.
This formalises lemma 4.2.10 in [Sangiorgi2011]. -/
theorem isWeakBisimulation_iff_isSWBisimulation
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} :
    IsWeakBisimulation lts₁ lts₂ r ↔ IsSWBisimulation lts₁ lts₂ r := by
  apply Iff.intro
  case mp =>
    intro h
    rw [IsSWBisimulation.iff_isSimulation]
    exact ⟨h.isSimulation.mono lts₁.tr_le_tr_saturate le_rfl,
      h.inv.isSimulation.mono lts₂.tr_le_tr_saturate le_rfl⟩
  case mpr =>
    intro h
    rw [IsWeakBisimulation, IsBisimulation.isSimulation_iff]
    exact ⟨h.isSimulation.isSimulation_saturate_left,
      h.isSimulation_flip.isSimulation_saturate_left⟩

theorem IsWeakBisimulation.isSwBisimulation
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {r : State₁ → State₂ → Prop}
    (h : IsWeakBisimulation lts₁ lts₂ r) :
  IsSWBisimulation lts₁ lts₂ r := isWeakBisimulation_iff_isSWBisimulation.1 h

theorem IsSWBisimulation.isWeakBisimulation
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {r : State₁ → State₂ → Prop}
    (h : IsSWBisimulation lts₁ lts₂ r) :
  IsWeakBisimulation lts₁ lts₂ r := isWeakBisimulation_iff_isSWBisimulation.2 h

/-- Weak bisimilarity can also be characterized through sw-bisimulations. -/
@[scoped grind =]
theorem WeakBisimilarity.weakBisim_eq_swBisim [HasTau Label]
    (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) :
    WeakBisimilarity lts₁ lts₂ =
      fun s₁ s₂ => ∃ r : State₁ → State₂ → Prop, r s₁ s₂ ∧ IsSWBisimulation lts₁ lts₂ r := by
  grind [WeakBisimilarity, isWeakBisimulation_iff_isSWBisimulation.1,
    isWeakBisimulation_iff_isSWBisimulation.2]

/- The weak laws below reuse the strong laws on the saturated LTSs. -/

/-- Homogeneous weak bisimilarity is reflexive. -/
theorem HomWeakBisimilarity.refl [HasTau Label] {lts : LTS State Label} (s : State) :
    s ≈[lts] s := HomBisimilarity.refl s

/-- The inverse of a weak bisimulation is a weak bisimulation. -/
theorem IsWeakBisimulation.inv [HasTau Label]
    {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    (r : State₁ → State₂ → Prop) (h : IsWeakBisimulation lts₁ lts₂ r) :
    IsWeakBisimulation lts₂ lts₁ (flip r) := IsBisimulation.inv h

/-- Weak bisimilarity is symmetric. -/
theorem WeakBisimilarity.symm [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    (h : s₁ ≈[lts₁,lts₂] s₂) : s₂ ≈[lts₂,lts₁] s₁ := Bisimilarity.symm h

/-- The composition of two weak bisimulations is a weak bisimulation. -/
theorem IsWeakBisimulation.comp
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {lts₃ : LTS State₃ Label}
    (h1 : IsWeakBisimulation lts₁ lts₂ r1) (h2 : IsWeakBisimulation lts₂ lts₃ r2) :
    IsWeakBisimulation lts₁ lts₃ (Relation.Comp r1 r2) := IsBisimulation.comp h1 h2

/-- The composition of two sw-bisimulations is an sw-bisimulation. -/
theorem IsSWBisimulation.comp
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {lts₃ : LTS State₃ Label}
    (h1 : IsSWBisimulation lts₁ lts₂ r1) (h2 : IsSWBisimulation lts₂ lts₃ r2) :
    IsSWBisimulation lts₁ lts₃ (Relation.Comp r1 r2) := by
  simp_all only [isWeakBisimulation_iff_isSWBisimulation.symm]
  apply IsWeakBisimulation.comp h1 h2

/-- Weak bisimilarity is transitive. -/
theorem WeakBisimilarity.trans [HasTau Label]
    {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {lts₃ : LTS State₃ Label}
    (h1 : s₁ ≈[lts₁,lts₂] s₂) (h2 : s₂ ≈[lts₂,lts₃] s₃) : s₁ ≈[lts₁,lts₃] s₃ :=
  Bisimilarity.trans h1 h2

/-- Homogeneous weak bisimilarity is an equivalence relation. -/
theorem HomWeakBisimilarity.eqv [HasTau Label] {lts : LTS State Label} :
    Equivalence (HomWeakBisimilarity lts) where
  refl := HomWeakBisimilarity.refl
  symm := WeakBisimilarity.symm
  trans := WeakBisimilarity.trans

end WeakBisimulation

section Reindex

/-! ## Reindex an LTS by an equivalence between two state types -/

/-- Reindex an LTS by an equivalence between two state types. -/
def reindex (lts₁ : LTS State₁ Label) (e : State₁ ≃ State₂) : LTS State₂ Label where
  Tr s₂ a t₂ := lts₁.Tr (e.symm s₂) a (e.symm t₂)

theorem reindex.tr (lts₁ : LTS State₁ Label) (e : State₁ ≃ State₂) (s₁ t₁ : State₁) (μ : Label) :
    (lts₁.reindex e).Tr (e s₁) μ (e t₁) ↔ lts₁.Tr s₁ μ t₁ := by
  simp [reindex]

theorem reindex.isBisimulation (lts₁ : LTS State₁ Label) (e : State₁ ≃ State₂) :
    IsBisimulation lts₁ (lts₁.reindex e) (fun s s' ↦ s' = e s) := by
  intro s s' hss' μ
  constructor
  · intro t htr
    use e t
    simp [hss', reindex.tr, htr]
  · intro t' htr'
    use e.symm t'
    simp [← hss', ← reindex.tr lts₁ e, htr']

theorem reindex.bisim_trace (lts₁ : LTS State₁ Label) (e : State₁ ≃ State₂)
    (s₁ t₁ : State₁) (μs : List Label) :
    lts₁.MTr s₁ μs t₁ → (lts₁.reindex e).MTr (e s₁) μs (e t₁) := by
  intro h
  obtain ⟨_, htr, rfl⟩ := (reindex.isBisimulation lts₁ e).bisim_trace rfl μs t₁ h
  exact htr

theorem reindex.bisim_trace_iff (lts₁ : LTS State₁ Label) (e : State₁ ≃ State₂)
    (s₁ t₁ : State₁) (μs : List Label) :
    lts₁.MTr s₁ μs t₁ ↔ (lts₁.reindex e).MTr (e s₁) μs (e t₁) := by
  constructor
  · exact reindex.bisim_trace lts₁ e s₁ t₁ μs
  · intro h
    obtain ⟨_, htr, heq⟩ := (reindex.isBisimulation lts₁ e).inv.bisim_trace rfl μs (e t₁) h
    rwa [e.injective heq]

end Reindex

end Cslib.LTS
