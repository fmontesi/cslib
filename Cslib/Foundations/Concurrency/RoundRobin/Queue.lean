/-
Copyright (c) 2026 Luc Edixhoven. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luc Edixhoven
-/

module

public import Cslib.Init
public import Mathlib.Data.List.Permutation
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Basic.Finite.Prod

/-!
# Round-robin queues

This module contains the list-theoretic core of the round-robin scheduler that witnesses the
finite existence of linearisations of smurf LTSs.  A queue is a permutation of a finite alphabet
of labels; the scheduler always executes the first enabled label of the current ordering and then
rotates the queue so that the executed label moves to the end, behind the disabled labels that
were skipped before it.

## Main definitions

* `Queue alphabet`: the lists that are permutations of the alphabet `alphabet`.
* `Queue.initial`: the queue `alphabet` itself.
* `Queue.rotate p r a`: the list `r ++ p ++ [a]`, the rotation performed after selecting `a` from
  the decomposition `p ++ a :: r`.
* `Queue.rotateQueue`: the rotation of a queue, packaged again as a queue.
* `Queue.select? enabled q`: the first `enabled` label of `q`, together with the (disabled)
  prefix before it and the suffix after it.
* `Queue.rank a q`: the position of `a` in the queue `q`.

## Main results

* `Queue.select?_eq_some_spec` and `Queue.select?_eq_none_iff`: the specification of `select?`.
* `Queue.rank_rotate_lt`: rotating past an enabled label strictly decreases the rank of a
  different label that sits after it.  This is the central list-index decrease behind the cycle
  condition of the scheduler.
-/

@[expose] public section

namespace Cslib.Concurrency.RoundRobin

variable {Label : Type v}

/-- A queue is a permutation of the finite alphabet. -/
def Queue (alphabet : List Label) : Type v := {q : List Label // q ∈ alphabet.permutations}

namespace Queue

variable {alphabet : List Label}

/-- Queues over a fixed alphabet are finite: they are the members of the finite list of
permutations of the alphabet. -/
instance : Finite (Queue alphabet) :=
  Finite.of_surjective
    (fun n : Fin alphabet.permutations.length =>
      (⟨alphabet.permutations.get n, List.get_mem alphabet.permutations n⟩ : Queue alphabet))
    (fun ⟨q, hq⟩ => by
      obtain ⟨n, hn⟩ := List.get_of_mem hq
      exact ⟨n, Subtype.ext hn⟩)

/-- Queues over a fixed alphabet have decidable equality as soon as labels do, which makes them
usable as an index type. -/
instance [DecidableEq Label] : DecidableEq (Queue alphabet) :=
  inferInstanceAs (DecidableEq {q : List Label // q ∈ alphabet.permutations})

/-- Membership of a label in a queue. -/
def mem (q : Queue alphabet) (a : Label) : Prop := a ∈ q.val

/-- The initial queue is the alphabet itself. -/
def initial (alphabet : List Label) : Queue alphabet :=
  ⟨alphabet, List.mem_permutations.mpr (List.Perm.refl alphabet)⟩

/-- The underlying list of the initial queue is the alphabet. -/
@[simp]
theorem initial_val (alphabet : List Label) : (initial alphabet).val = alphabet := rfl

/-- Every queue is a permutation of the alphabet. -/
theorem perm (q : Queue alphabet) : q.val.Perm alphabet :=
  List.mem_permutations.mp q.2

/-- Queues over a duplicate-free alphabet are themselves duplicate-free. -/
theorem nodup (q : Queue alphabet) (halphabet : alphabet.Nodup) : q.val.Nodup :=
  (perm q).nodup_iff.mpr halphabet

/-- The rotation used by the scheduler: the selected label is moved to the end,
and so is the disabled prefix that was skipped before it. -/
def rotate (p r : List Label) (a : Label) : List Label := r ++ p ++ [a]

/-- A rotation is only a permutation: it moves the selected label to the end while keeping the
disabled prefix behind it. -/
theorem rotate_perm {p r : List Label} {a : Label} :
    (rotate p r a).Perm (p ++ a :: r) := by
  unfold rotate
  rw [List.append_assoc]
  refine (List.perm_append_comm (l₁ := r) (l₂ := p ++ [a])).trans ?_
  rw [List.append_assoc, List.singleton_append]

/-- Rotating a duplicate-free list keeps it duplicate-free. -/
theorem rotate_nodup {p r : List Label} {a : Label} (h : (p ++ a :: r).Nodup) :
    (rotate p r a).Nodup :=
  (rotate_perm (p := p) (r := r) (a := a)).nodup_iff.mpr h

/-- The queue obtained by rotating `q` at a decomposition `q.val = p ++ a :: r`. -/
def rotateQueue (q : Queue alphabet) (p r : List Label) (a : Label)
    (h : q.val = p ++ a :: r) : Queue alphabet :=
  ⟨rotate p r a,
    List.mem_permutations.mpr
      ((rotate_perm (p := p) (r := r) (a := a)).trans (by rw [← h]; exact perm q))⟩

/-- The underlying list of a rotated queue is the rotation of the underlying list. -/
@[simp]
theorem rotateQueue_val (q : Queue alphabet) (p r : List Label) (a : Label)
    (h : q.val = p ++ a :: r) : (rotateQueue q p r a h).val = rotate p r a := rfl

/-- A rotated list is still a permutation of the alphabet. -/
theorem rotate_perm_alphabet (q : Queue alphabet) (p r : List Label) (a : Label)
    (h : q.val = p ++ a :: r) : (rotate p r a).Perm alphabet :=
  rotateQueue_val q p r a h ▸ perm (rotateQueue q p r a h)

/-! ### First-enabled selection -/

/-- `select? enabled q` is the first enabled label of `q`, together with the disabled prefix
before it and the suffix after it.  `none` iff no label of `q` is enabled. -/
def select? (enabled : Label → Bool) : List Label → Option (List Label × Label × List Label)
  | [] => none
  | a :: r =>
    match enabled a with
    | true => some ([], a, r)
    | false =>
      match select? enabled r with
      | none => none
      | some (p, b, r') => some (a :: p, b, r')

/-- Selection on the empty queue fails. -/
private theorem select?_nil (enabled : Label → Bool) : select? enabled [] = none := rfl

/-- Selection on a queue whose head is enabled returns that head. -/
private theorem select?_cons_of_enabled (enabled : Label → Bool) {a : Label} (r : List Label)
    (h : enabled a = true) : select? enabled (a :: r) = some ([], a, r) := by
  simp only [select?, h]

/-- Selection on a queue whose head is disabled and whose tail has no enabled label fails. -/
private theorem select?_cons_of_disabled_none (enabled : Label → Bool) {a : Label}
    (r : List Label) (h : enabled a = false) (h' : select? enabled r = none) :
    select? enabled (a :: r) = none := by
  simp only [select?, h, h']

/-- Selection on a queue whose head is disabled skips the head. -/
private theorem select?_cons_of_disabled_some (enabled : Label → Bool) {a : Label}
    {r p : List Label} {b : Label} {r' : List Label} (h : enabled a = false)
    (h' : select? enabled r = some (p, b, r')) :
    select? enabled (a :: r) = some (a :: p, b, r') := by
  simp only [select?, h, h']

/-- A successful selection decomposes the queue at the selected label, which is enabled, and all
the labels of the skipped prefix are disabled. -/
theorem select?_eq_some_spec (enabled : Label → Bool) :
    ∀ {q p a r}, select? enabled q = some (p, a, r) →
      q = p ++ a :: r ∧ enabled a = true ∧ ∀ b ∈ p, enabled b = false := by
  intro q
  induction q with
  | nil =>
    intro p a r h
    rw [select?_nil] at h
    cases h
  | cons x xs ih =>
    intro p a r h
    cases hx : enabled x with
    | true =>
      rw [select?_cons_of_enabled enabled xs hx] at h
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
      exact ⟨rfl, hx, by simp only [List.not_mem_nil, false_implies, implies_true]⟩
    | false =>
      cases hs : select? enabled xs with
      | none =>
        rw [select?_cons_of_disabled_none enabled xs hx hs] at h
        cases h
      | some t =>
        obtain ⟨p', b, r'⟩ := t
        rw [select?_cons_of_disabled_some enabled (a := x) hx hs] at h
        obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
        obtain ⟨hq, ha, hp'⟩ := ih hs
        refine ⟨by rw [hq, List.cons_append], ha, ?_⟩
        intro c hc
        rw [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact hx
        · exact hp' c hc

/-- Selection fails exactly when every label of the queue is disabled. -/
theorem select?_eq_none_iff (enabled : Label → Bool) :
    ∀ q, select? enabled q = none ↔ ∀ b ∈ q, enabled b = false := by
  intro q
  induction q with
  | nil =>
    refine ⟨fun _ b hb => absurd hb (List.not_mem_nil), fun _ => select?_nil enabled⟩
  | cons x xs ih =>
    cases hx : enabled x with
    | true =>
      rw [select?_cons_of_enabled enabled xs hx]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · cases h
      · have h' := h x List.mem_cons_self
        rw [hx] at h'
        cases h'
    | false =>
      cases hs : select? enabled xs with
      | none =>
        rw [select?_cons_of_disabled_none enabled xs hx hs]
        refine ⟨fun _ b hb => ?_, fun _ => rfl⟩
        rw [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact hx
        · exact ih.mp hs b hb
      | some t =>
        obtain ⟨p', b, r'⟩ := t
        rw [select?_cons_of_disabled_some enabled (a := x) (p := p') (b := b) (r' := r') hx hs]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · cases h
        · have h' : ∀ c ∈ xs, enabled c = false := fun c hc => h c (List.mem_cons_of_mem x hc)
          rw [ih.mpr h'] at hs
          cases hs

/-- Selection succeeds exactly when some label of the queue is enabled. -/
theorem select?_isSome_iff (enabled : Label → Bool) (q : List Label) :
    (select? enabled q).isSome = true ↔ ∃ b ∈ q, enabled b = true := by
  rw [Option.isSome_iff_ne_none, Ne, select?_eq_none_iff]
  constructor
  · intro h
    by_contra hc
    apply h
    intro b hb
    cases hb' : enabled b with
    | false => rfl
    | true => exact absurd ⟨b, hb, hb'⟩ hc
  · rintro ⟨b, hb, hb'⟩ hc
    have := hc b hb
    rw [hb'] at this
    cases this

/-- A queue with an enabled member admits a selection. -/
theorem select?_eq_some_of_mem (enabled : Label → Bool) :
    ∀ {q a}, a ∈ q → enabled a = true → ∃ p b r, select? enabled q = some (p, b, r) := by
  intro q a hq ha
  have hsome : (select? enabled q).isSome = true := (select?_isSome_iff enabled q).mpr ⟨a, hq, ha⟩
  rw [Option.isSome_iff_ne_none] at hsome
  cases h : select? enabled q with
  | none => exact absurd h hsome
  | some s =>
    obtain ⟨p, b, r⟩ := s
    exact ⟨p, b, r, rfl⟩

/-- The selection is deterministic: the decomposition it returns is unique. -/
theorem select?_unique (enabled : Label → Bool) :
    ∀ {q p₁ a₁ r₁ p₂ a₂ r₂}, select? enabled q = some (p₁, a₁, r₁) →
      select? enabled q = some (p₂, a₂, r₂) → p₁ = p₂ ∧ a₁ = a₂ ∧ r₁ = r₂ := by
  intro q p₁ a₁ r₁ p₂ a₂ r₂ h₁ h₂
  have h : (p₁, a₁, r₁) = (p₂, a₂, r₂) :=
    Option.some.inj (show some (p₁, a₁, r₁) = some (p₂, a₂, r₂) by rw [← h₁, h₂])
  simpa only [Prod.mk.injEq] using h

/-- The selected label is not in the skipped prefix nor equal to `a`; so a member of the queue
that is enabled, different from `a`, and absent from the prefix lies in the suffix. -/
theorem select?_mem_post (enabled : Label → Bool) :
    ∀ {q p a r lam}, select? enabled q = some (p, a, r) →
      lam ∈ q → lam ∉ p → lam ≠ a → lam ∈ r := by
  intro q p a r lam hsel hmem hnotin hne
  obtain ⟨hq, -, -⟩ := select?_eq_some_spec enabled hsel
  rw [hq, List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · exact absurd hmem hnotin
  · rw [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact absurd rfl hne
    · exact hmem

/-- A queue that starts with a disabled prefix followed by an enabled label selects exactly that
decomposition. -/
theorem select?_eq_some_of_forall_disabled (enabled : Label → Bool) :
    ∀ {p a r}, (∀ b ∈ p, enabled b = false) → enabled a = true →
      select? enabled (p ++ a :: r) = some (p, a, r) := by
  intro p
  induction p with
  | nil => intro a r _ ha; simp only [List.nil_append, select?, ha]
  | cons x xs ih =>
    intro a r hp ha
    have hx : enabled x = false := hp x List.mem_cons_self
    have hxs : ∀ b ∈ xs, enabled b = false := fun b hb => hp b (List.mem_cons_of_mem x hb)
    rw [List.cons_append, select?, hx, ih hxs ha]

/-! ### Rank -/

/-- The rank of a label in a list is its position, i.e. the number of labels before it.
Positions are computed with classical decidable equality, so that `rank` carries no instance
arguments and `rank_rotate_lt` can be applied without a decidable equality on labels. -/
noncomputable def rank (a : Label) (q : List Label) : ℕ := by classical exact q.idxOf a

/-- The rank of a label never exceeds the length of the queue. -/
theorem rank_le_length (a : Label) (q : List Label) : rank a q ≤ q.length := by
  classical
  unfold rank
  exact List.idxOf_le_length

/-- A label occurring in the queue has a rank strictly smaller than the length. -/
theorem rank_lt_length {a : Label} {q : List Label} (h : a ∈ q) : rank a q < q.length := by
  classical
  unfold rank
  exact List.idxOf_lt_length_of_mem h

/-- The rank of an absent label is the length of the queue. -/
theorem rank_of_notMem {a : Label} {q : List Label} (h : a ∉ q) : rank a q = q.length := by
  classical
  unfold rank
  exact List.idxOf_of_notMem h

/-- The rank of a label occurring in a prefix does not depend on the suffix appended to it. -/
theorem rank_append_of_mem {a : Label} {p : List Label} (h : a ∈ p) (r : List Label) :
    rank a (p ++ r) = rank a p := by
  classical
  unfold rank
  exact List.idxOf_append_of_mem h

/-- The rank of a label absent from a prefix is shifted by the length of that prefix. -/
theorem rank_append_of_notMem {a : Label} {p : List Label} (h : a ∉ p) (r : List Label) :
    rank a (p ++ r) = p.length + rank a r := by
  classical
  unfold rank
  exact List.idxOf_append_of_notMem h

/-- **Central list-index decrease.**  If `q = p ++ a :: r` with `a ≠ lam` and `lam ∈ r`, then
rotating `q` so that `a` moves to the end, behind the skipped prefix `p`, strictly decreases the
rank of `lam`. -/
theorem rank_rotate_lt {lam a : Label} {p r : List Label}
    (hne : a ≠ lam) (hnotin : lam ∉ p) (hin : lam ∈ r) :
    rank lam (rotate p r a) < rank lam (p ++ a :: r) := by
  classical
  unfold rank rotate
  rw [List.idxOf_append_of_mem (l₁ := r ++ p) (l₂ := [a]) (List.mem_append_left p hin),
    List.idxOf_append_of_mem (l₁ := r) (l₂ := p) hin,
    List.idxOf_append_of_notMem (l₁ := p) (l₂ := a :: r) hnotin,
    List.idxOf_cons_ne (a := lam) (b := a) r hne]
  omega

/-- Permuting a queue does not change the rank of a label that the queue does not contain: in
both lists such a label has rank equal to the length.  (Rank is a position, so it is *not*
invariant under permutation for labels that do occur.) -/
theorem rank_eq_of_perm {lam : Label} {q₁ q₂ : List Label} (h : q₁.Perm q₂)
    (hnotMem : lam ∉ q₁) : rank lam q₁ = rank lam q₂ := by
  have hnotMem₂ : lam ∉ q₂ := fun hc => hnotMem ((h.mem_iff).mpr hc)
  rw [rank_of_notMem hnotMem, rank_of_notMem hnotMem₂, h.length_eq]

end Queue

end Cslib.Concurrency.RoundRobin
