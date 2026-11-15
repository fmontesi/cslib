/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, Aviv Bar Natan
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Lattice.Nat
public import Cslib.Computability.Machines.Turing.MultiTape.Nondeterministic

/-!
# Space usage of multi-tape Turing machines

Defines the space used by a run path of a multi-tape Turing machine. Space usage counts the
positions visited by each work-tape head along the path and sums over the tapes.

`MultiTapeNTM.RunPath.InWindow` says that every head of a run path stays within the window
`[-s, s]`, which bounds the space of the path.

`MultiTapeNTM.RunPath.space_map_le` bounds the space of a run path mapped by `RunPath.map` through
the head positions of the original path.

## Design

The input tape is read-only with bounded head movement, and the output tape is write-only, so we
ignore both for space usage. A work-tape cell is visited when its head occupies that position in any
configuration of the path, including the initial and final configurations. Each cell counts once,
regardless of repeated visits.

Instead of considering the cells _visited_ by the work tape heads, some textbooks
(including [AroraBarak09]) only consider the number of cells that contain
a non-blank symbol at some point in the execution or the number of cells written to. This allows
work tape heads to freely move at no cost as long as they do not write. It is
important to note that this causes `DSPACE(1)` to include `DSPACE(log log n)`, a class that
contains e.g. the non-regular language `{0^n 1^n | n ∈ ℕ}` (it is accepted by a TM that writes a
single marker on the work tape and then counts the number of symbols by work tape head movement
without writing).
Defining space usage via "cells visited" thus yields the more fine-grained "complexity world" in
which `DSPACE(1)` is exactly the class of regular languages.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing

/-- The window `[-s, s]` of tape positions allotted to a tape that uses `s` cells. -/
@[scoped grind =]
def window (s : ℕ) : Finset ℤ := Finset.Icc (-(s : ℤ)) s

@[scoped grind =]
lemma mem_window {s : ℕ} {z : ℤ} : z ∈ window s ↔ z.natAbs ≤ s := by
  grind

@[simp]
lemma card_window (s : ℕ) : (window s).card = 2 * s + 1 := by
  grind [Int.card_Icc]

end Turing

namespace Turing.MultiTapeNTM

variable {k k' : ℕ} {State State' Symbol : Type*} {input input' : List Symbol}
variable {ntm : MultiTapeNTM k Symbol State} {ntm' : MultiTapeNTM k' Symbol State'}

namespace RunPath

/-- The set of positions visited by the head of work tape `i` along a run path. -/
def visitedByTapeHead (p : ntm.RunPath input) (i : Fin k) : Finset ℤ :=
  Finset.univ.image fun n ↦ (p n).workTapePos i

/-- The number of positions visited by the head of work tape `i` along a run path. -/
def spaceUsedByTape (p : ntm.RunPath input) (i : Fin k) : ℕ :=
  (p.visitedByTapeHead i).card

/-- The number of work tape cells visited along a run path. -/
def space (p : ntm.RunPath input) : ℕ := ∑ i, p.spaceUsedByTape i

/-- A set containing every position of a head along a path bounds the space used by its tape. -/
lemma spaceUsedByTape_le_card (p : ntm.RunPath input) {i : Fin k} {S : Finset ℤ}
    (h : ∀ c ∈ p, c.workTapePos i ∈ S) : p.spaceUsedByTape i ≤ S.card :=
  Finset.card_le_card (Finset.image_subset_iff.mpr fun n _ => h (p n) ⟨n, rfl⟩)

/-- Sets containing every position of the heads along a path bound its space by their total
size. -/
lemma space_le_sum_card (p : ntm.RunPath input) {S : Fin k → Finset ℤ}
    (h : ∀ c ∈ p, ∀ i, c.workTapePos i ∈ S i) : p.space ≤ ∑ i, (S i).card :=
  Finset.sum_le_sum fun i _ => p.spaceUsedByTape_le_card fun c hc => h c hc i

/-- A path whose configurations all lie on another path visits no more cells. -/
lemma space_le_of_subset {p q : ntm.RunPath input} (h : ∀ c ∈ q, c ∈ p) : q.space ≤ p.space :=
  q.space_le_sum_card fun c hc _ =>
    let ⟨n, hn⟩ := h c hc
    hn ▸ Finset.mem_image_of_mem _ (Finset.mem_univ n)

/-- A path visits exactly the head positions of its configurations. -/
@[simp]
lemma mem_visitedByTapeHead (p : ntm.RunPath input) {i : Fin k} {z : ℤ} :
    z ∈ p.visitedByTapeHead i ↔ ∃ c ∈ p, c.workTapePos i = z := by
  simp [visitedByTapeHead, RelSeries.mem_def]

/-- A prefix of a path visits only cells that the path visits. -/
lemma visitedByTapeHead_take_subset (p : ntm.RunPath input) (j : Fin (p.length + 1)) (i : Fin k) :
    visitedByTapeHead (p.take j) i ⊆ p.visitedByTapeHead i :=
  Finset.image_subset_iff.mpr fun n _ =>
    p.mem_visitedByTapeHead.mpr ⟨_, ⟨Fin.castLE j.isLt n, rfl⟩, rfl⟩

/-- Extending a path by a configuration visits its head positions as well. -/
lemma visitedByTapeHead_snoc (p : ntm.RunPath input) (c : Cfg k Symbol State input)
    (h : ntm.Step p.last c) (i : Fin k) :
    visitedByTapeHead (p.snoc c h) i = insert (c.workTapePos i) (p.visitedByTapeHead i) := by
  ext z
  simp [RelSeries.mem_snoc, or_and_right, exists_or, eq_comm, or_comm]

/-! ### Windows -/

/-- Every head stays within the window `[-s, s]` along the path. -/
def InWindow (p : ntm.RunPath input) (s : ℕ) : Prop :=
  ∀ c ∈ p, ∀ i, c.workTapePos i ∈ window s

/-- A path whose heads stay within `[-s, s]` visits at most `2 * s + 1` cells on each tape. -/
lemma InWindow.space_le {p : ntm.RunPath input} {s : ℕ} (h : p.InWindow s) :
    p.space ≤ k * (2 * s + 1) := by
  simpa using p.space_le_sum_card h

/-- Joining two paths whose heads stay within `[-s, s]` keeps them there. -/
lemma InWindow.smash {p q : ntm.RunPath input} {h : p.last = q.head} {s : ℕ}
    (hp : p.InWindow s) (hq : q.InWindow s) : InWindow (p.smash q h) s :=
  fun _ hc => (RelSeries.mem_or_mem_of_mem_smash hc).elim (hp _) (hq _)

/-! ### Mapped paths -/

/-- If the head of tape `i'` of a mapped path follows the head of tape `i` of the source path, the
two tapes visit the same cells. -/
lemma visitedByTapeHead_map (p : ntm.RunPath input)
    (f : (ntm.stepRel input).Hom (ntm'.stepRel input')) {i : Fin k} {i' : Fin k'}
    (h : ∀ c ∈ p, (f c).workTapePos i' = c.workTapePos i) :
    (p.map f).visitedByTapeHead i' = p.visitedByTapeHead i :=
  Finset.image_congr fun n _ => h (p n) ⟨n, rfl⟩

/-- **Space of a mapped path.** If tape `e j` of the mapped path follows tape `j` of `p`, and every
other tape `l` stays in `window l`, the mapped path uses the space of `p` plus the cells of
`window l` for every other tape `l`. -/
lemma space_map_le (p : ntm.RunPath input) (f : (ntm.stepRel input).Hom (ntm'.stepRel input'))
    (e : Fin k ↪ Fin k') (window : Fin k' → Finset ℤ)
    (hfollow : ∀ c ∈ p, ∀ j, (f c).workTapePos (e j) = c.workTapePos j)
    (hwindow : ∀ c ∈ p, ∀ l ∉ Set.range e, (f c).workTapePos l ∈ window l) :
    (p.map f).space ≤ p.space + ∑ l ∈ (Finset.univ.map e)ᶜ, (window l).card := by
  rw [space, space, ← Finset.sum_add_sum_compl (Finset.univ.map e), Finset.sum_map]
  refine add_le_add (Finset.sum_le_sum fun j _ => (congrArg Finset.card
    (p.visitedByTapeHead_map f fun c hc => hfollow c hc j)).le) (Finset.sum_le_sum fun l hl => ?_)
  exact (p.map f).spaceUsedByTape_le_card fun _ ⟨n, hn⟩ =>
    hn ▸ hwindow (p n) ⟨n, rfl⟩ l (by simpa using hl)

end RunPath

/-- The number of positions visited by the head of work tape `i` along a computation path. -/
def ComputationPath.spaceUsedByTape (p : ntm.ComputationPath input) (i : Fin k) : ℕ :=
  RunPath.spaceUsedByTape p.toRunPath i

/-- The number of work tape cells visited along a computation path. -/
def ComputationPath.space (p : ntm.ComputationPath input) : ℕ := RunPath.space p.toRunPath

/-- Every computation prefix on `input` visits at most `s` work-tape cells, regardless of its
outcome. -/
def RunsInSpace (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) (s : ℕ) : Prop :=
  ∀ p : ntm.ComputationPath input, p.space ≤ s

/-- A space bound can be increased. -/
lemma RunsInSpace.mono {s s' : ℕ} (h : ntm.RunsInSpace input s) (hs : s ≤ s') :
    ntm.RunsInSpace input s' :=
  fun p ↦ (h p).trans hs

/-- A machine running in space `s` has a computation path visiting the most cells. -/
lemma RunsInSpace.exists_space_max {s : ℕ} (hs : ntm.RunsInSpace input s) :
    ∃ p : ntm.ComputationPath input, ∀ q : ntm.ComputationPath input, q.space ≤ p.space := by
  have hne : (Set.range fun p : ntm.ComputationPath input => p.space).Nonempty :=
    ⟨_, ⟨.singleton _ (ntm.initCfg input), rfl⟩, rfl⟩
  have hbdd : BddAbove (Set.range fun p : ntm.ComputationPath input => p.space) :=
    ⟨s, by rintro _ ⟨p, rfl⟩; exact hs p⟩
  obtain ⟨p, hp⟩ := Nat.sSup_mem hne hbdd
  exact ⟨p, fun q => (le_csSup hbdd ⟨q, rfl⟩).trans_eq hp.symm⟩

/-- A space bound is at least the number of work tapes, since the initial configuration
visits one cell on each tape. -/
lemma RunsInSpace.numTapes_le {s : ℕ} (h : ntm.RunsInSpace input s) : k ≤ s := by
  have hs := h ⟨RelSeries.singleton _ (ntm.initCfg input), rfl⟩
  change (∑ _ : Fin k, ((Finset.univ : Finset (Fin 1)).image fun _ => (0 : ℤ)).card) ≤ s at hs
  simpa using hs

/-- A machine without work tapes satisfies every space bound. -/
@[simp]
lemma runsInSpace_zero_tapes (ntm : MultiTapeNTM 0 Symbol State) (input : List Symbol) (s : ℕ) :
    ntm.RunsInSpace input s := by
  intro p
  simp [ComputationPath.space, RunPath.space]

end Turing.MultiTapeNTM
