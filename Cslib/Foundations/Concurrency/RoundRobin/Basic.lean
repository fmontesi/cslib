/-
Copyright (c) 2026 Luc Edixhoven. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luc Edixhoven
-/

module

public import Cslib.Foundations.Concurrency.Linearisation
public import Cslib.Foundations.Concurrency.RoundRobin.Scheduler
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Finset.Lattice.Union

/-!
# Finite linearisations

This module assembles the round-robin construction into existence theorems.  A finitely branching
LTS with finitely many states has a finite set of transition labels, so the scheduler of
`Cslib.Foundations.Concurrency.RoundRobin.Scheduler` can be instantiated with an alphabet covering
every transition.  The resulting linearisation has finitely many states, and composing it with
theorem 18 (`linearisation_is_representative`) yields a finite linear LTS whose traces are
representative of the original traces.

## Main definitions

* `finiteAlphabet A`: a finite set of labels covering every transition label of `A`.

## Main results

* `exists_finite_linearisation`: a finite linearisation exists for every smurf LTS that has
  finitely many states, finitely many outgoing labels, and whose matching branches are dependent.
* `exists_finite_representative`: the same, composed with theorem 18, giving a finite linear LTS
  that represents every trace of the original up to an extra suffix and swaps of independent
  labels.

## Implementation notes

The construction decides enabledness classically (`enabledAt`), so it is an existence proof:
it does not provide a computable extractor, which would require an effective representation of
the transition relation.  It also does not prove termination of the greedy graph-growth algorithm
sketched in the paper; only finite existence is established.

Luc Edixhoven, with help from DeepSeek-V4.1-Flash-1017 and ChatGPT-6 Astra.
-/

@[expose] public section

namespace Cslib.Concurrency.RoundRobin

universe u v w

variable {State : Type u} {Label : Type v}

open Classical in
/-- A finite set of labels covering all transition labels of `A`. -/
noncomputable def finiteAlphabet (A : LTS State Label) [Finite State] [A.FinitelyBranching] :
    Finset Label :=
  (Set.finite_iUnion
    (fun s : State => (Set.finite_coe_iff.mp (inferInstance : Finite (A.outgoingLabels s))))
  ).toFinset

open Classical in
/-- Every transition label belongs to `finiteAlphabet A`. -/
theorem mem_finiteAlphabet (A : LTS State Label) [Finite State] [A.FinitelyBranching]
    {s : State} {a : Label} {t : State} (h : A.Tr s a t) : a ∈ finiteAlphabet A :=
  Set.Finite.mem_toFinset _ |>.mpr (Set.mem_iUnion.mpr ⟨s, ⟨t, h⟩⟩)

/-- Every transition label belongs to the list enumerating `finiteAlphabet A`. -/
theorem mem_finiteAlphabet_toList (A : LTS State Label) [Finite State] [A.FinitelyBranching]
    {s : State} {a : Label} {t : State} (h : A.Tr s a t) :
    a ∈ (finiteAlphabet A).toList :=
  Finset.mem_toList.mpr (mem_finiteAlphabet A h)

/-- The list enumerating `finiteAlphabet A` has no duplicates. -/
theorem nodup_finiteAlphabet_toList (A : LTS State Label) [Finite State] [A.FinitelyBranching] :
    (finiteAlphabet A).toList.Nodup :=
  Finset.nodup_toList _

/-- **Finite existence.** Every smurf LTS with finitely many states and finitely many outgoing
labels has a linearisation with finitely many states, provided matching branches are never
independent.  The witness is the round-robin scheduler over `finiteAlphabet A`. -/
theorem exists_finite_linearisation {B : Branching Label} {I : Label → Label → Prop}
    [Independence I] {A : LTS State Label} [Finite State] [A.FinitelyBranching]
    (hsmurf : Smurf A I B) (hno : ∀ a b, B.matching a b → ¬ I a b) (s₀ : State) :
    ∃ (RState : Type (max u v)) (_ : Finite RState) (R : LTS RState Label) (r₀ : RState)
      (φ : RState → State), IsLinearisation (B := B) (I := I) R A r₀ s₀ φ :=
  ⟨State × Queue (finiteAlphabet A).toList, inferInstance,
    scheduler (B := B) A (finiteAlphabet A).toList, (s₀, Queue.initial _), Prod.fst,
    scheduler_isLinearisation hsmurf hno
      (fun _ _ _ h => mem_finiteAlphabet_toList A h) s₀⟩

/-- **Theorem 19.** Every smurf LTS with finitely many states and finitely many outgoing labels
has a finite linear LTS whose traces are representative of the original traces, up to an extra
suffix and swaps of independent labels.  This composes `exists_finite_linearisation` with
theorem 18. -/
theorem exists_finite_representative {B : Branching Label} {I : Label → Label → Prop}
    [Independence I] {A : LTS State Label} [Finite State] [A.FinitelyBranching]
    (hsmurf : Smurf A I B) (hno : ∀ a b, B.matching a b → ¬ I a b)
    {Pid : Type w} {pn : Label → Finset Pid}
    (hpn₀ : ∀ l, (pn l).Nonempty)
    (hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂))
    (hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → (pn l₁) = (pn l₂))
    (s₀ : State) :
    ∃ (RState : Type (max u v)) (_ : Finite RState) (R : LTS RState Label) (r₀ : RState),
      IsRepresentative I (R.traces r₀) (A.traces s₀) := by
  obtain ⟨RState, hfin, R, r₀, φ, hlin⟩ := exists_finite_linearisation hsmurf hno s₀
  exact ⟨RState, hfin, R, r₀,
    linearisation_is_representative (hpn₀ := hpn₀) (hpn₁ := hpn₁) (hpn₂ := hpn₂)
      R A hsmurf r₀ s₀ φ hlin⟩

/-- **Theorem 19, participation form.** The matching-dependence hypothesis is derived from the
participation assumptions already used by theorem 18, so no additional assumption is needed
beyond finite states, finite branching, and `Smurf`. -/
theorem exists_finite_representative_of_participation {B : Branching Label}
    {I : Label → Label → Prop} [Independence I] {A : LTS State Label} [Finite State]
    [A.FinitelyBranching] (hsmurf : Smurf A I B) {Pid : Type w}
    {pn : Label → Finset Pid}
    (hpn₀ : ∀ l, (pn l).Nonempty)
    (hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂))
    (hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → (pn l₁) = (pn l₂))
    (s₀ : State) :
    ∃ (RState : Type (max u v)) (_ : Finite RState) (R : LTS RState Label) (r₀ : RState),
      IsRepresentative I (R.traces r₀) (A.traces s₀) :=
  exists_finite_representative hsmurf (matching_not_independent hpn₀ hpn₁ hpn₂)
    hpn₀ hpn₁ hpn₂ s₀

end Cslib.Concurrency.RoundRobin
