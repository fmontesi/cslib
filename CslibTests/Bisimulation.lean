/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Foundations.Semantics.LTS.Bisimulation

namespace CslibTests

open Cslib LTS
open scoped Ordinal

/- An LTS with two bisimilar states. -/
private inductive tr1 : ℕ → Char → ℕ → Prop where
-- First process, `1`
| one2two : tr1 1 'a' 2
| two2three : tr1 2 'b' 3
| two2four : tr1 2 'c' 4
-- Second process, `5`
| five2six : tr1 5 'a' 6
| six2seven : tr1 6 'b' 7
| six2eight : tr1 6 'c' 8

def lts1 := LTS.mk tr1

private inductive Bisim15 : ℕ → ℕ → Prop where
| oneFive : Bisim15 1 5
| twoSix : Bisim15 2 6
| threeSeven : Bisim15 3 7
| fourEight : Bisim15 4 8

example : 1 ~[lts1] 5 := by
  exists Bisim15
  apply And.intro
  · constructor
  intro s1 s2 hr μ
  constructor
  case left =>
    intro s1' htr
    cases htr <;> cases hr
    · exists 6
      repeat constructor
    · exists 7
      repeat constructor
    · exists 8
      repeat constructor
  case right =>
    intro s2' htr
    cases htr <;> cases hr
    · exists 2; repeat constructor
    · exists 3; repeat constructor
    · exists 4; repeat constructor

  -- aesop?
  --   (add simp Bisimulation)
  --   (add safe constructors Bisim15)
  --   (add safe cases Bisim15)
  --   (add safe cases [LTS.mtr])
  --   (add simp LTS.tr)
  --   (add safe constructors tr1)
  --   (add unsafe apply Bisimulation.follow_fst)
  --   (add unsafe apply Bisimulation.follow_snd)

section Heterogeneous

variable {State₁ State₂ Label : Type*} {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
variable {s₁ : State₁} {s₂ : State₂}

-- Bisimilarity as a relation can be written as a section of the infix notation.
example : IsBisimulation lts₁ lts₂ (· ~[lts₁,lts₂] ·) := Bisimilarity.isBisimulation ..

example : Equivalence (· ~[lts₁] ·) := HomBisimilarity.eqv

example : (· ~[lts₁,lts₂] ·) = Bisimilarity lts₁ lts₂ := rfl

-- Instances stated with sections are found for the unapplied relation.
example : IsEquiv State₁ (HomBisimilarity lts₁) := inferInstance

-- Approximations as relations are written as sections, like bisimilarity.
example : Equivalence (· ~[lts₁;o] ·) := HomBisimilarityApprox.eqv o

example : (· ~[lts₁,lts₂;o] ·) = BisimilarityApprox lts₁ lts₂ o := rfl

-- Symmetry must support different state types and universes, as the relations do.
example (h : s₁ ≤≥[lts₁,lts₂] s₂) : s₂ ≤≥[lts₂,lts₁] s₁ := h.symm

example (h : s₁ ~[lts₁,lts₂] s₂) : s₂ ~[lts₂,lts₁] s₁ := h.symm

example (h : s₁ ~[lts₁,lts₂] s₂) : s₂ ~[lts₂,lts₁] s₁ := by
  symm
  exact h

open scoped Bisimilarity in
example (h : s₁ ~[lts₁,lts₂] s₂) : s₂ ~[lts₂,lts₁] s₁ := by grind

-- The named state-type arguments match the heterogeneous symmetry statements.
example (h : s₁ ≤≥[lts₁,lts₂] s₂) : s₂ ≤≥[lts₂,lts₁] s₁ :=
  SimulationEquiv.symm (State₁ := State₁) (s2 := s₂) h

example (h : s₁ ~[lts₁,lts₂] s₂) : s₂ ~[lts₂,lts₁] s₁ :=
  Bisimilarity.symm (State₁ := State₁) h

example (h : s₁ ~[lts₁,lts₂;o] s₂) : s₂ ~[lts₂,lts₁;o] s₁ := by
  symm
  exact h

example (h : s₁ ~[lts₁,lts₂;ω] s₂) : s₂ ~[lts₂,lts₁;ω] s₁ := by
  symm
  exact h

example (h : s₁ ~[lts₁,lts₂] s₂) : s₁ ~[lts₁,lts₂;ω] s₂ := h.approx ω

example (m n : ℕ) (hmn : m ≤ n) (h : s₁ ~[lts₁,lts₂;(n : Ordinal)] s₂) :
    s₁ ~[lts₁,lts₂;(m : Ordinal)] s₂ := h.of_ge_nat hmn

-- Finite composition remains available across independent state universes.
example {State₃ : Type*} {lts₃ : LTS State₃ Label} {s₃ : State₃} (n : ℕ)
    (h₁ : s₁ ~[lts₁,lts₂;(n : Ordinal)] s₂) (h₂ : s₂ ~[lts₂,lts₃;(n : Ordinal)] s₃) :
    s₁ ~[lts₁,lts₃;(n : Ordinal)] s₃ := h₁.trans_nat h₂

example [lts₁.ImageFinite] [lts₂.ImageFinite] (h : s₁ ~[lts₁,lts₂;ω] s₂) :
    s₁ ~[lts₁,lts₂] s₂ := h.bisimilarity_of_omega

example [lts₁.ImageFinite] [lts₂.ImageFinite] :
    s₁ ~[lts₁,lts₂;ω] s₂ ↔ s₁ ~[lts₁,lts₂] s₂ := by simp

-- Ordinal indices use the same notation, including limits and successors of limits.
example (h : s₁ ~[lts₁,lts₂;ω] s₂) (n : ℕ) : s₁ ~[lts₁,lts₂;(n : Ordinal)] s₂ :=
  BisimilarityApprox.omega_iff.mp h n

example [lts₁.ImageFinite] [lts₂.ImageFinite] : (· ~[lts₁,lts₂;ω] ·) = (· ~[lts₁,lts₂] ·) := by
  simp

example [lts₁.ImageFinite] [lts₂.ImageFinite] : (· ~[lts₁,lts₂;ω + 1] ·) = (· ~[lts₁,lts₂] ·) :=
  BisimilarityApprox.eq_bisimilarity (by exact_mod_cast (lt_add_one ω).le)

-- The added top endpoint is bisimilarity without any image-finiteness assumption.
example : (· ~[lts₁,lts₂;⊤] ·) = (· ~[lts₁,lts₂] ·) := by simp

example : (· ~[lts₁;⊤] ·) = (· ~[lts₁] ·) := by simp

example (h : s₁ ~[lts₁,lts₂;⊤] s₂) : s₁ ~[lts₁,lts₂] s₂ := by simpa using h

example (h : s₁ ~[lts₁,lts₂;⊤] s₂) (o : Ordinal) : s₁ ~[lts₁,lts₂;o] s₂ :=
  BisimilarityApprox.top_iff.mp h o

-- The applied characterisations rewrite goals stated with the infix notation.
example (h : s₁ ~[lts₁,lts₂] s₂) : s₁ ~[lts₁,lts₂;⊤] s₂ := by
  rw [BisimilarityApprox.top_iff_bisimilarity]
  exact h

example [lts₁.ImageFinite] [lts₂.ImageFinite] (h : s₁ ~[lts₁,lts₂;ω + 1] s₂) :
    s₁ ~[lts₁,lts₂] s₂ := by
  rwa [BisimilarityApprox.iff_bisimilarity (by exact_mod_cast (lt_add_one ω).le)] at h

open scoped BisimilarityApprox in
example : s₁ ~[lts₁,lts₂;0] s₂ := by grind

end Heterogeneous

example (lts : LTS State Label) (n : ℕ) (s : State) : s ~[lts;n] s := by rfl

-- A single transition and an infinite loop agree for one round but differ in the second.
private def countdownLTS : LTS ℕ Unit := ⟨fun s _ t => s = t + 1⟩

private def loopLTS : LTS Unit Unit := ⟨fun _ _ _ => True⟩

example : 0 ~[countdownLTS,loopLTS;0] () := by simp

example : 1 ~[countdownLTS,loopLTS;1] () := by
  rw [← zero_add (1 : WithTop Ordinal), BisimilarityApprox.succ_iff]
  intro μ
  exact ⟨fun _ _ => ⟨(), trivial, BisimilarityApprox.zero⟩,
    fun _ _ => ⟨0, rfl, BisimilarityApprox.zero⟩⟩

private theorem countdown_not_approx_two : ¬(1 ~[countdownLTS,loopLTS;2] ()) := by
  intro h
  rw [← one_add_one_eq_two] at h
  obtain ⟨s, (hs : 1 = s + 1), hr⟩ := h.follow_snd (show loopLTS.Tr () () () from trivial)
  rw [← zero_add (1 : WithTop Ordinal)] at hr
  obtain ⟨t, (ht : s = t + 1), _⟩ := hr.follow_snd (show loopLTS.Tr () () () from trivial)
  lia

-- Both directions of matching matter, including across different state types.
example : ¬(() ~[loopLTS,countdownLTS;2] 1) :=
  fun h => countdown_not_approx_two h.symm

example : ¬ (1 ~[countdownLTS,loopLTS;ω] ()) :=
  fun h => countdown_not_approx_two (BisimilarityApprox.omega_iff.mp h 2)

-- A relation can be a bisimulation up to bisimilarity without itself being a bisimulation.
-- Soundness gives a bisimulation on its closure and bisimilarity of its related states.
private def completeLTS : LTS Bool Unit := ⟨fun _ _ _ => True⟩

private def onlyFalse (s t : Bool) : Prop := s = false ∧ t = false

private theorem completeLTS_bisimilar (s t : Bool) : s ~[completeLTS] t := by
  refine ⟨fun _ _ => True, trivial, ?_⟩
  intro _ _ _ _
  exact ⟨fun _ _ => ⟨false, trivial, trivial⟩, fun _ _ => ⟨false, trivial, trivial⟩⟩

private theorem onlyFalse_closure (s t : Bool) :
    UpToHomBisimilarity completeLTS completeLTS onlyFalse s t :=
  ⟨false, completeLTS_bisimilar s false, false, ⟨rfl, rfl⟩, completeLTS_bisimilar false t⟩

private theorem onlyFalse_upTo : IsBisimulationUpTo completeLTS completeLTS onlyFalse := by
  intro _ _ _ _
  exact ⟨fun s _ => ⟨false, trivial, onlyFalse_closure s false⟩,
    fun t _ => ⟨false, trivial, onlyFalse_closure false t⟩⟩

example : onlyFalse ≤ (· ~[completeLTS] ·) := onlyFalse_upTo.le_bisimilarity

example : ¬ IsHomBisimulation completeLTS onlyFalse := by
  intro h
  obtain ⟨_, _, hr⟩ := (h (show onlyFalse false false from ⟨rfl, rfl⟩) ()).1 true trivial
  exact Bool.noConfusion hr.1

end CslibTests
