import Cslib.Computability.Languages.Basic
import Mathlib.Computability.Language

/-! Luc's playground
  With initial help from ChatGPT and later DeepSeek-V4.1-Flash-1017.
-/

namespace Cslib.Concurrency

/-- Independence relation on an alphabet α.

`independent a b` means that the actions `a` and `b` are independent. -/
structure Independence (α : Type*) where
  independent : α → α → Prop
  symm : ∀ {a b : α}, independent a b → independent b a
  irrefl : ∀ a : α, ¬ independent a a

/-- Definition for trace equivalence. `TraceEq I u v` means that the words `u` and `v` are equivalent under the independence relation `I`.
In other words: `u` can be obtained from `v` by swapping adjacent independent characters, and vice-versa. -/
inductive TraceEq {α : Type*} (I : Independence α) : List α → List α → Prop where
  | refl (w : List α) : TraceEq I w w
  | symm {u v : List α} : TraceEq I u v → TraceEq I v u
  | trans {u v w : List α} : TraceEq I u v → TraceEq I v w → TraceEq I u w
  | swap (a b : α) (w : List α) (h : I.independent a b) : TraceEq I (a :: b :: w) (b :: a :: w)
  | append_left (u v w: List α) : TraceEq I v w → TraceEq I (u ++ v) (u ++ w)
  | append_right (u v w : List α) : TraceEq I v w → TraceEq I (v ++ u) (w ++ u)

def traceSetoid {α : Type*} (I : Independence α) : Setoid (List α) where
  r := TraceEq I
  iseqv := {
    refl := by exact TraceEq.refl
    symm := by exact TraceEq.symm
    trans := by exact TraceEq.trans
  }

def Trace (I : Independence α) : Type* :=
  Quotient (traceSetoid I)

namespace Trace

variable {α : Type*} {I : Independence α}

def mk (I : Independence α) (w : List α) : Trace I :=
  Quotient.mk (traceSetoid I) w

def one : Trace I :=
  mk I []

def mul (u v : Trace I) : Trace I :=
  Quotient.lift₂
    (fun a b => mk I (a ++ b))
    (by
      intro n k n' k' heq heq'
      apply Quotient.sound
      exact TraceEq.trans
        (TraceEq.append_right k n n' heq)
        (TraceEq.append_left n' k k' heq')
    )
    u
    v

def toLanguage (u : Trace I) : Language α :=
  Quotient.lift
    (fun a => { w : List α | TraceEq I w a})
    (by
      intro n k h
      ext v
      exact ⟨fun hv => hv.trans h, fun hv => hv.trans h.symm⟩
    )
    u

end Trace

abbrev TraceLanguage (I : Independence α) := Set (Trace I)

namespace TraceLanguage

variable {α : Type*} {I : Independence α}

def mk (I : Independence α) (l : Language α) : TraceLanguage I :=
  { t | ∃ w ∈ l, t = Trace.mk I w}

def toLanguage (T : TraceLanguage I) : Language α :=
  { w | ∃ t ∈ T, w ∈ Trace.toLanguage t }

end TraceLanguage

-- A representative of B if B is a subset of the prefix trace closure of A
def Representative {α : Type*} (I : Independence α) (A B : Language α) :=
  ∀ w ∈ B, ∃ v, ∃ u ∈ A, TraceEq I (w ++ v) u

end Cslib.Concurrency
