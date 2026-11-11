import Cslib.Computability.Languages.Basic
-- import Mathlib.Computability.Language

/-! Luc's playground
  With initial help from ChatGPT and later DeepSeek-V4.1-Flash-1017.
-/

namespace List

/-- `PermUpTo r u v` means that `u` can be obtained from `v` by swapping adjacent elements
related by `r`, in either direction. -/
inductive PermUpTo {α : Type*} (r : α → α → Prop) : List α → List α → Prop where
  | nil : PermUpTo r [] []
  | cons (a : α) {u v : List α} : PermUpTo r u v → PermUpTo r (a :: u) (a :: v)
  | swap (a b : α) (w : List α) (h : r a b ∨ r b a) :
      PermUpTo r (a :: b :: w) (b :: a :: w)
  | trans {u v w : List α} : PermUpTo r u v → PermUpTo r v w → PermUpTo r u w

namespace PermUpTo

variable {α : Type*} {r : α → α → Prop}

/-- Every list is a permitted permutation of itself. -/
theorem refl (w : List α) : PermUpTo r w w := by
  induction w with
  | nil => exact .nil
  | cons a w ih => exact .cons a ih

/-- Permitted permutations are symmetric, including for asymmetric relations. -/
theorem symm {u v : List α} (h : PermUpTo r u v) : PermUpTo r v u := by
  induction h with
  | nil => exact .nil
  | cons a _ ih => exact .cons a ih
  | swap a b w h => exact .swap b a w h.symm
  | trans _ _ ih₁ ih₂ => exact .trans ih₂ ih₁

/-- Prepending the same list preserves permitted permutations. -/
theorem append_left (u v w : List α) (h : PermUpTo r v w) :
    PermUpTo r (u ++ v) (u ++ w) := by
  induction u with
  | nil => exact h
  | cons a u ih => exact .cons a ih

/-- Appending the same list preserves permitted permutations. -/
theorem append_right (u v w : List α) (h : PermUpTo r v w) :
    PermUpTo r (v ++ u) (w ++ u) := by
  induction h with
  | nil => exact refl u
  | cons a _ ih => exact .cons a ih
  | swap a b w h => exact .swap a b (w ++ u) h
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

end PermUpTo

end List

namespace Cslib.Concurrency

/-- An independence relation is symmetric and irreflexive. -/
class abbrev Independence {α : Type*} (I : α → α → Prop) := Std.Symm I, Std.Irrefl I

def traceSetoid {α : Type*} (I : α → α → Prop) [Independence I] : Setoid (List α) where
  r := List.PermUpTo I
  iseqv := {
    refl := by exact List.PermUpTo.refl
    symm := by exact List.PermUpTo.symm
    trans := by exact List.PermUpTo.trans
  }

def Trace (I : α → α → Prop) [Independence I] : Type* :=
  Quotient (traceSetoid I)

namespace Trace

variable {α : Type*} {I : α → α → Prop} [Independence I]

def mk (I : α → α → Prop) [Independence I] (w : List α) : Trace I :=
  Quotient.mk (traceSetoid I) w

def one : Trace I :=
  mk I []

def mul (u v : Trace I) : Trace I :=
  Quotient.lift₂
    (fun a b => mk I (a ++ b))
    (by
      intro n k n' k' heq heq'
      apply Quotient.sound
      exact List.PermUpTo.trans
        (List.PermUpTo.append_right k n n' heq)
        (List.PermUpTo.append_left n' k k' heq')
    )
    u
    v

def toLanguage (u : Trace I) : Set (List α) :=
  Quotient.lift
    (fun a => { w : List α | List.PermUpTo I w a})
    (by
      intro n k h
      ext v
      exact ⟨fun hv => hv.trans h, fun hv => hv.trans h.symm⟩
    )
    u

end Trace

abbrev TraceLanguage (I : α → α → Prop) [Independence I] := Set (Trace I)

namespace TraceLanguage

variable {α : Type*} {I : α → α → Prop} [Independence I]

def mk (I : α → α → Prop) [Independence I] (l : Set (List α)) : TraceLanguage I :=
  { t | ∃ w ∈ l, t = Trace.mk I w}

def toLanguage (T : TraceLanguage I) : Set (List α) :=
  { w | ∃ t ∈ T, w ∈ Trace.toLanguage t }

end TraceLanguage

-- A representative of B if B is a subset of the prefix trace closure of A
def IsRepresentative {α : Type*} (I : α → α → Prop) [Independence I] (A B : Set (List α)) :=
  ∀ w ∈ B, ∃ v, ∃ u ∈ A, List.PermUpTo I (w ++ v) u

end Cslib.Concurrency
