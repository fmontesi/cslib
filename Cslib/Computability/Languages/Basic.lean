import Mathlib.Computability.Language
-- import Mathlib.Order.Closure
-- import Mathlib.Order.Monotone

-- All of this should probably go in Language.lean.

namespace Language

-- apparently not defined in mathlib, seems very basic
instance : HasSubset (Language α) :=
  ⟨(· ⊆ · : Set (List α) → Set (List α) → Prop)⟩

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
