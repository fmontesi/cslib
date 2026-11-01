/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ForwardWork
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential

/-!
# A machine that clears a work tape

`clearWork Symbol` erases the word on its work tape and returns the head to the start. It never
moves the input head and never outputs. It is the sequential composition of two one-tape machines:

* `forwardWork Symbol` moves the head right over the word until it reads the first blank, the
  frontier just past the word, and halts there (see `Plumbing.ForwardWork`).
* `rewindWork Symbol (some none)` rewinds the head to the start, erasing every symbol it walks
  over.

On a word of length `l` the forward pass takes `l + 1` steps and the erasing rewind `l + 2` steps.
The head stays within the cells `-1, …, l`, so the machine runs in time `3 * (l + 1)` and space
`l + 2`; placed on tape `i` of `k` tapes, the remaining tapes contribute one cell each.

## Main results

* `Turing.MultiTapeTM.clearWork`: the one-tape machine that clears its tape.
* `Turing.MultiTapeTM.transformsTapes_clearWork`: `clearWork` replaces the word on its tape by the
  empty word.
* `Turing.MultiTapeTM.transformsTapes_clearWork_tapeEmb`: placed on tape `i` of a `k`-tape machine
  it does so on that tape and leaves every other tape unchanged.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol : Type*} {input : List Symbol}

/-- The one-tape machine that clears its tape: it moves to the end of the word and erases it on
the way back. -/
public noncomputable def clearWork (Symbol : Type*) :
    MultiTapeTM 1 Symbol (Unit ⊕ RewindWorkState) :=
  (forwardWork Symbol).seq (rewindWork Symbol (some none))

/-- **The machine that clears its work tape** replaces the word on it by the empty word, in at most
`3 * (w.length + 1)` steps and `w.length + 2` cells. -/
public theorem transformsTapes_clearWork (w : List Symbol) :
    TransformsTapes (clearWork Symbol) (fun _ ws => ws 0 = w)
      (fun _ _ ws' emitted => ws' = (fun _ => []) ∧ emitted = [])
      (3 * (w.length + 1)) (w.length + 2) := by
  intro input ws out hws
  obtain rfl : ws = fun _ => w := funext fun x => Fin.fin_one_eq_zero x ▸ hws
  unfold clearWork
  -- the forward pass takes `w.length + 1` steps, the erasing rewind `w.length + 2`
  let p₀ := MultiTapeNTM.RunPath.ofDeterministic (forwardWork Symbol)
    (wordsCfg input (some ()) (fun _ => w) out) (w.length + 1)
  let p₁ := MultiTapeNTM.RunPath.ofDeterministic (rewindWork Symbol (some none))
    (⟨some (rewindWork Symbol (some none)).q₀, 1, fun _ => tapeOfList w, fun _ => w.length, out⟩ :
      Cfg 1 Symbol RewindWorkState input) (w.length + 2)
  have h₀ : p₀.last = _ := runFrom_forwardWork (input := input) 1 w out (zero_add _)
  have h₁ : p₁.last = _ := runFrom_rewindWork_erase (input := input) 1 (tapeOfList w) out rfl
  obtain ⟨p, hh, hl, ht, hvisited⟩ := exists_runPath_seq (p₀ := p₀) (p₁ := p₁) (by rw [h₀])
    (by rw [h₀]; rfl)
  refine ⟨fun _ => [], [], ⟨rfl, rfl⟩, p, hh,
    by rw [hl, h₁]; simp [Cfg.mapState, wordsCfg],
    (show p.length ≤ w.length + 1 + (w.length + 2) from ht).trans (by lia), ?_⟩
  -- both passes keep the head within `[-1, w.length]`
  rw [MultiTapeNTM.RunPath.space, Fin.sum_univ_one]
  refine (Finset.card_le_card (t := .Icc (-1 : ℤ) w.length)
    ((hvisited 0).trans (Finset.union_subset ?_ ?_))).trans (by simp; lia) <;>
    refine Finset.image_subset_iff.mpr fun m _ => Finset.mem_Icc.2 ?_
  · exact Set.Icc_subset_Icc_left (by lia)
      (workTapePos_runFrom_forwardWork (input := input) 1 w out (Nat.zero_le w.length) m)
  · exact workTapePos_runFrom_rewindWork (some none) (input := input) 1 (tapeOfList w) out rfl
      le_rfl m

/-! ### Clearing one of several work tapes -/

/-- **The machine that clears a work tape**, placed on tape `i` of a `k`-tape machine, replaces the
word on that tape by the empty word and leaves every other tape unchanged, in at most
`3 * (w.length + 1)` steps and `w.length + 1 + k` cells. -/
public theorem transformsTapes_clearWork_tapeEmb (i : Fin k) (w : List Symbol) :
    TransformsTapes ((clearWork Symbol).extendTapes (tapeEmb i)) (fun _ ws => ws i = w)
      (fun _ ws ws' emitted => ws' = Function.update ws i [] ∧ emitted = [])
      (3 * (w.length + 1)) (w.length + 1 + k) :=
  ((transformsTapes_clearWork (Symbol := Symbol) w).tapeEmb i).imp (fun _ _ h => h)
    (fun _ ws ws' _ _ ⟨v, ⟨hv, he⟩, hws'⟩ => ⟨by rw [hws', hv], he⟩) le_rfl
    (by have := i.pos; lia)

end Turing.MultiTapeTM
