/-
Copyright (c) 2026 Luc Edixhoven. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luc Edixhoven
-/

module

public import Cslib.Init
public import Mathlib.Computability.Language

/-!
# Basic closure properties of languages

Prefix closure and its order-theoretic properties, plus the subset instance on `Language α`.
-/

@[expose] public section

namespace Language

/-- Subset of languages, which is not defined in Mathlib. -/
instance instHasSubset (α : Type*) : HasSubset (Language α) :=
  ⟨(· ⊆ · : Set (List α) → Set (List α) → Prop)⟩

/-- The prefix closure of a language: the words having a prefix in the language. -/
def prefixClosure (l : Language α) : Language α :=
  { w | ∃ v, w ++ v ∈ l}

variable {α : Type*}

-- monotonicity
theorem prefixClosure.monotone : Monotone (prefixClosure : Language α → Language α) := by
  intro _ _ h _ ⟨v, hv⟩
  exact ⟨v, h hv⟩

-- extensivity
theorem prefixClosure.le_closure (l : Language α) : l ≤ l.prefixClosure := by
  intro _ _
  exists []
  simpa

-- idempotency
theorem prefixClosure.idempotent (l : Language α) :
  l.prefixClosure.prefixClosure = l.prefixClosure := by
  ext w
  constructor
  · rintro ⟨v, u, hu⟩
    exists v ++ u
    rwa [List.append_assoc] at hu
  · intro h
    exact ⟨[], by simpa⟩

end Language
