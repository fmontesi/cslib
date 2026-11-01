/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Logics.BTL.Basic

namespace CslibTests.BTL

open Cslib Logic Modal BTL
open scoped InferenceSystem Satisfies

-- The timeline is 0 → 1 → 2, with the atom true only at 1.
private def timeline : BTL.Model Nat Unit where
  r w w' := w + 1 = w' ∧ w' < 3
  v w _ := w = 1

example : ⇓BTL[timeline,0 ⊨ d⟨F⟩(() : Unit)] := by
  rw [Satisfies.btl_future_sometime_iff]
  exact ⟨1, by simp [timeline], rfl⟩

example : ⇓BTL[timeline,2 ⊨ d⟨P⟩(() : Unit)] := by
  rw [Satisfies.btl_past_sometime_iff]
  exact ⟨1, by simp [timeline], rfl⟩

example : ⇓BTL[timeline,0 ⊨ d[F](() : Unit)] := by
  rw [Satisfies.btl_future_always_iff]
  intro w hw
  exact hw.1.symm

example : ⇓BTL[timeline,2 ⊨ d[P](() : Unit)] := by
  rw [Satisfies.btl_past_always_iff]
  intro w hw
  change w = 1
  have := hw.1
  grind

-- Endpoint boxes are vacuous, and endpoint diamonds are false.
example : ⇓BTL[timeline,0 ⊨ d[P]⊥] := by
  rw [Satisfies.btl_past_always_iff]
  intro w hw
  have := hw.1
  grind

example : ⇓BTL[timeline,2 ⊨ ¬d⟨F⟩⊤] := by
  rw [Satisfies.not_iff_not, Satisfies.btl_future_sometime_iff]
  rintro ⟨w, hw, _⟩
  obtain ⟨h₁, h₂⟩ := hw
  grind

-- The present is not implicitly included.
example : ⇓BTL[timeline,1 ⊨ ¬d⟨F⟩(() : Unit) ∧ ¬d⟨P⟩(() : Unit)] := by
  simp only [Satisfies.and_iff_and, Satisfies.not_iff_not,
    Satisfies.btl_future_sometime_iff, Satisfies.btl_past_sometime_iff, Satisfies.btl_atom_iff]
  change (¬∃ w, (1 + 1 = w ∧ w < 3) ∧ w = 1) ∧
    (¬∃ w, (w + 1 = 1 ∧ 1 < 3) ∧ w = 1)
  grind

-- The relation is not implicitly closed under transitivity.
example : ⇓BTL[timeline,0 ⊨ d⟨F⟩(d⟨F⟩⊤) ∧ ¬d⟨F⟩¬(() : Unit)] := by
  rw [Satisfies.and_iff_and]
  constructor
  · apply Satisfies.btl_future_sometime_intro (w' := 1) (by simp [timeline])
    apply Satisfies.btl_future_sometime_intro (w' := 2) (by simp [timeline])
    exact Satisfies.true
  · rw [Satisfies.not_iff_not, Satisfies.btl_future_sometime_iff]
    rintro ⟨w, hw, h⟩
    exact h hw.1.symm

-- Temporal propositions support the existing modal automation and equivalence API.
example (m : BTL.Model World Atom) (hr : m.r w w') (φ : BTL.Proposition Atom)
    (h : ⇓BTL[m,w' ⊨ φ]) : ⇓BTL[m,w ⊨ d⟨F⟩φ] := by
  rw [Satisfies.btl_future_sometime_iff]
  exact ⟨w', hr, h⟩

example (m : BTL.Model World Atom) (φ : BTL.Proposition Atom) :
    d[F]φ ≡[Modal.Proposition.Equiv m.toModal] ¬d⟨F⟩¬φ := by
  rw [Modal.Proposition.equiv_iff_forall_iff, BTL.Proposition.always_eq_not_future_not]
  intro w
  rfl

end CslibTests.BTL
