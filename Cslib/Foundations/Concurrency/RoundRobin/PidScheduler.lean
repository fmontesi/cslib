/-
Copyright (c) 2026 Luc Edixhoven. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luc Edixhoven
-/

module

public import Cslib.Foundations.Concurrency.Linearisation
public import Cslib.Foundations.Concurrency.RoundRobin.Queue

/-!
# Round-robin scheduling by participant

Select the first process involved in an enabled transition. All transitions involving the
selected process use the same queue rotation, including both branches of a conditional.

Luc Edixhoven, with help from OpenAI Codex.
-/

@[expose] public section

namespace Cslib.Concurrency.RoundRobin

variable {State Label Pid : Type*} {A : LTS State Label} {ids : List Pid}
  {B : Branching Label} {I : Label → Label → Prop} [Independence I]

open Classical in
/-- A process is ready if it participates in some enabled transition. -/
noncomputable def pidReady (A : LTS State Label) (uses : Pid → Label → Prop)
    (s : State) (p : Pid) : Bool := decide (∃ a t, A.Tr s a t ∧ uses p a)

/-- Schedule transitions involving the first ready process in the queue. -/
def pidScheduler (A : LTS State Label) (uses : Pid → Label → Prop) (ids : List Pid) :
    LTS (State × Queue ids) Label where
  Tr x a y := A.Tr x.1 a y.1 ∧ ∃ pre p post,
    Queue.select? (pidReady A uses x.1) x.2.val = some (pre, p, post) ∧
    uses p a ∧ y.2.val = Queue.rotate pre post p

variable {uses : Pid → Label → Prop}

/-- Waiting for an enabled label decreases the rank of any queued participant of that label
at every independent step. -/
private theorem pid_rank_bound (hs : Smurf A I B)
    (hdis : ∀ {p a b}, I a b → uses p a → ¬ uses p b)
    {p : Pid} (hp : p ∈ ids) {a : Label} (hpa : uses p a)
    {x y : State × Queue ids} {w : List Label}
    (run : (pidScheduler A uses ids).MTr x w y) :
    A.HasOutLabel x.1 a → (∀ b ∈ w, I a b) →
    w.length + Queue.rank p y.2.val ≤ Queue.rank p x.2.val := by
  classical
  induction run with
  | refl => simp
  | @stepL x b z w y step _ ih =>
    rintro ⟨t, ha⟩ hind
    obtain ⟨hb, pre, k, post, sel, hkb, rot⟩ := step
    have hi := hind b List.mem_cons_self
    obtain ⟨t', _, ha'⟩ := hs.f _ _ _ _ _ ⟨hi, ha, hb⟩
    have tail := ih ⟨t', ha'⟩ (fun c hc => hind c (List.mem_cons_of_mem b hc))
    have ready : pidReady A uses x.1 p = true := by
      exact decide_eq_true ⟨a, t, ha, hpa⟩
    have hne : k ≠ p := fun e => hdis hi hpa (e ▸ hkb)
    have decrease := Queue.rank_lt_of_select sel ((Queue.perm _).mem_iff.mpr hp) ready hne
    rw [← rot] at decrease
    simp only [List.length_cons]
    omega

/-- Coverage needs only one queued participant per enabled action. The queue may use any
finite enumeration of the active process names. -/
theorem pidScheduler_isLinearisation (hs : Smurf A I B)
    (cover : ∀ {s a t}, A.Tr s a t → ∃ p ∈ ids, uses p a)
    (hdis : ∀ {p a b}, I a b → uses p a → ¬ uses p b)
    (hmatch : ∀ {p a b}, B.matching a b → uses p a → uses p b)
    (s₀ : State) : IsLinearisation (B := B) (I := I) (pidScheduler A uses ids) A
      (s₀, Queue.initial ids) s₀ Prod.fst := by
  classical
  refine ⟨⟨?_, ?_⟩, rfl, fun _ _ _ h => h.1, ?_, ?_⟩
  · rintro x a y ⟨ha, pre, p, post, sel, hpa, _⟩
    by_cases hc : B.conditional a
    · obtain ⟨b, t, hm, hb⟩ := hs.m _ _ _ ⟨hc, ha⟩
      have d := (Queue.select?_eq_some_spec _ sel).1
      exact Or.inr ⟨b, (t, Queue.rotateQueue x.2 pre post p d),
        ⟨hb, pre, p, post, sel, hmatch hm hpa, rfl⟩, hm⟩
    · exact Or.inl hc
  · rintro x a b y z ⟨⟨ha, _, p, _, sel, hpa, _⟩, ⟨hb, _, k, _, sel', hkb, _⟩, hne⟩
    obtain ⟨_, rfl, _⟩ := Queue.select?_unique _ sel sel'
    exact (hs.u _ _ _ _ _ hne ⟨ha, hb⟩).resolve_left (fun hi => hdis hi hpa hkb)
  · intro x terminal a t ha
    obtain ⟨p, hp, hpa⟩ := cover ha
    have ready : pidReady A uses x.1 p = true := decide_eq_true ⟨a, t, ha, hpa⟩
    obtain ⟨pre, k, post, sel⟩ :=
      Queue.select?_eq_some_of_mem _ ((Queue.perm x.2).mem_iff.mpr hp) ready
    obtain ⟨d, hk, _⟩ := Queue.select?_eq_some_spec _ sel
    obtain ⟨b, t', hb, hkb⟩ := of_decide_eq_true hk
    exact terminal b (t', Queue.rotateQueue x.2 pre post k d) ⟨hb, pre, k, post, sel, hkb, rfl⟩
  · intro x w hne run a t ha
    obtain ⟨p, hp, hpa⟩ := cover ha
    by_contra! hind
    have bound := pid_rank_bound (uses := uses) hs hdis hp hpa run ⟨t, ha⟩ hind
    exact hne (List.eq_nil_of_length_eq_zero (by omega))

end Cslib.Concurrency.RoundRobin
