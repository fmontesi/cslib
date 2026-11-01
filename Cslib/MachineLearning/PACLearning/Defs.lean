/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Cslib.Init
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Order.SymmDiff

/-! # PAC Learning

This file defines the Probably Approximately Correct (PAC) learning model
introduced by Valiant [Valiant1984], generalized to an arbitrary label type `β`
and parameterized by a family of distributions `𝒟` on `α × β`.

A concept class `C` over domain `α` with labels in `β` is a collection of
functions `α → β`. A learning algorithm receives a labeled sample drawn i.i.d.
from an unknown joint distribution `D` on `α × β` and must produce a hypothesis
whose 0-1 error is within `ε` of the best concept in `C`, with probability at
least `1 - δ`.

The single definition `IsPACLearnerFor` captures the realizable, agnostic, and
noise-tolerant settings by varying the distribution family `𝒟`:

- **Agnostic** [Haussler1992]: `𝒟 = Set.univ` — the learner must work for all distributions.
- **Realizable**: `𝒟` consists of pushforwards of arbitrary probability measures
  `P` on `α` along the graph `x ↦ (x, c x)` of some concept `c ∈ C`, so that
  `optimalError D C = 0`.
- **Noise-tolerant** [AngluinLaird1988]: `𝒟` consists of noisy versions of realizable
  distributions, where each label is corrupted independently with some probability `η`.

The accuracy and confidence parameters `ε` and `δ` are elements of the subtype
`Set.Ioo (0 : ℝ≥0) 1`, which bundles the value together with the proof that it
lies in the open interval `(0, 1)`, ensuring the learning condition is non-vacuous.

All declarations live under the `Cslib.MachineLearning.PACLearning` namespace so that
generic names like `error` and `optimalError` do not pollute the parent namespace.

## Main definitions

- `ConceptClass`: a set of functions `α → β` (classifiers).
- `LabeledSample`: a finite sequence of `(point, label)` pairs.
- `Learner`: a function from labeled samples to hypotheses.
- `error`: the 0-1 error of a hypothesis under a joint distribution.
- `optimalError`: the infimum of `error` over a concept class.
- `IsPACLearnerFor`: deterministic `(ε, δ)`-PAC learner over a distribution family.
- `IsRPACLearnerFor`: randomized variant of `IsPACLearnerFor`. Universe-polymorphic in the
  randomness space `Ω : Type*`.
- `IsPACLearnable`: a concept class is PAC learnable if `IsPACLearnerFor` holds for
  all `ε, δ : Set.Ioo (0 : ℝ≥0) 1` with some sample size `m`.
- `IsRPACLearnable`: randomized variant of `IsPACLearnable`. Pins the randomness space to
  `Type 0`; `IsRPACLearnerFor` itself remains universe-polymorphic for users who need it.
- `LearnerModel`: the common predicate shape `ℕ → ε → δ → C → 𝒟 → Prop` abstracting both
  the deterministic and randomized learners so sample-complexity lemmas can be shared.
- `sampleComplexity`: sample complexity of a generic learner model.
- `rsampleComplexity`: randomized sample complexity, i.e. `sampleComplexity IsRPACLearnerFor`.

## Binary classification

When `β = Bool`, concepts correspond to subsets of `α`. The section
*Binary Classification* provides:

- `hypothesisError`: the symmetric-difference error `P(h ∆ c)`.
- `falsePositiveError`, `falseNegativeError`: its decomposition.
- `hypothesisError_eq_add`: the decomposition theorem.
- `error_map_eq_hypothesisError`: bridge between the general `error` and
  the binary `hypothesisError` under a realizable distribution.

## Main statements

- `IsPACLearnerFor.toIsRPACLearnerFor`: every deterministic PAC learner is a
  randomized one (via the trivial randomness space `PUnit`).
- `IsPACLearnerFor.antitone_family`, `.antitone_C`: the deterministic PAC learner
  predicate is antitone in the distribution family and concept class.
- `IsPACLearnerFor.mono_δ`, `.mono_ε`: the predicate is monotone in the confidence and
  accuracy parameters (a weaker bound still holds).
- `IsRPACLearnerFor.antitone_family`, `.mono_δ`: analogues for the randomized predicate.
  (`mono_ε` and `antitone_C` are not provided because they change the integrand and
  would require an extra measurability assumption.)
- `IsPACLearnable.toIsRPACLearnable`: deterministic learnability implies randomized.
- `IsPACLearnable.antitone_family`, `.antitone_C`, `IsRPACLearnable.antitone_family`:
  PAC learnability is antitone in the distribution family and concept class.
- `sampleComplexity_antitone_δ`, `_antitone_ε`, `_mono_family`, `_mono_C`: variation of
  deterministic sample complexity in confidence, accuracy, distribution family, and concept
  class (antitone in the numeric parameters, monotone under `⊆` in the set parameters). The
  randomized analogues `rsampleComplexity_antitone_δ` and `_mono_family` are provided.
- `IsPACLearnable.sampleComplexity_*`, `IsRPACLearnable.rsampleComplexity_*`: the same
  monotonicity facts phrased with a learnability hypothesis in place of the ad-hoc
  `∃ m, IsPACLearnerFor m …` existence witness, so callers who already know the class is
  learnable need not thread it through.
- `hypothesisError_eq_add`: total error = false positive + false negative.

## References

* [L. G. Valiant, *A Theory of the Learnable*][Valiant1984]
* [A. Ehrenfeucht, D. Haussler, M. Kearns, L. Valiant,
  *A General Lower Bound on the Number of Examples Needed for Learning*][EHKV1989]
* [M. J. Kearns, U. V. Vazirani,
  *An Introduction to Computational Learning Theory*][KearnsVazirani1994]
* [D. Haussler, *Decision Theoretic Generalizations of the PAC Model for Neural Net
  and Other Learning Applications*][Haussler1992]
* [D. Angluin, P. Laird, *Learning from Noisy Examples*][AngluinLaird1988]
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Cslib.MachineLearning.PACLearning

/-! ### Core Definitions -/

/-- A *concept class* over domain `α` with label type `β` is a set of functions `α → β`.
For binary classification (`β = Bool`), this is equivalent to a collection of subsets of `α`
via the characteristic function. -/
abbrev ConceptClass (α β : Type*) := Set (α → β)

/-- A *labeled sample* of size `m` over domain `α` with label type `β` is a finite sequence
of `(point, label)` pairs. -/
abbrev LabeledSample (α β : Type*) (m : ℕ) := Fin m → (α × β)

/-- A *learner* using `m` samples is a function that takes a labeled sample and produces
a hypothesis (a function from the domain to the label type). -/
abbrev Learner (α β : Type*) (m : ℕ) := LabeledSample α β m → (α → β)

section
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The *prediction error* (0-1 loss) of a hypothesis `h` under a joint distribution `D`
on `α × β`, defined as the probability that the prediction disagrees with the label:
`D({(x, y) | h(x) ≠ y})`. -/
noncomputable def error (D : Measure (α × β)) (h : α → β) : ℝ≥0∞ :=
  D {p : α × β | h p.1 ≠ p.2}

/-- The *optimal error* of a concept class `C` under a joint distribution `D`, defined as the
infimum of `error D c` over all concepts `c ∈ C`. When `C` is empty this is `⊤`, making the
PAC learning condition vacuously true. -/
noncomputable def optimalError (D : Measure (α × β)) (C : ConceptClass α β) : ℝ≥0∞ :=
  ⨅ c ∈ C, error D c

/-! ### PAC Learners -/

/-- `IsPACLearnerFor m ε δ C 𝒟` asserts that there exists a learner using `m` samples
that is `(ε, δ)`-correct for the concept class `C` over the distribution family `𝒟`: for every
probability measure `D ∈ 𝒟` on `α × β`, the probability (over i.i.d. samples from `D`) that
the learner's hypothesis has error exceeding `opt_C(D) + ε` is at most `δ`.

The parameters `ε` and `δ` are elements of `Set.Ioo (0 : ℝ≥0) 1`, bundling the value with
the proof that it lies in `(0, 1)`. This ensures the condition is non-vacuous:
`ε < 1` prevents the error threshold from exceeding the maximum possible error under a
probability measure, and `δ < 1` prevents the confidence bound from being trivially
satisfied. -/
def IsPACLearnerFor (m : ℕ) (ε δ : Set.Ioo (0 : ℝ≥0) 1)
    (C : ConceptClass α β) (𝒟 : Set (Measure (α × β))) : Prop :=
  ∃ A : Learner α β m,
    ∀ (D : Measure (α × β)) [IsProbabilityMeasure D], D ∈ 𝒟 →
      (Measure.pi (fun _ : Fin m => D))
        {S : LabeledSample α β m |
          optimalError D C + ↑ε.val < error D (A S)} ≤ ↑δ.val

/-- `IsRPACLearnerFor m ε δ C 𝒟` asserts that there exists a *randomized* learner using
`m` samples that is `(ε, δ)`-correct for the concept class `C` over the distribution family
`𝒟`. A randomized learner draws internal randomness `ω` from a probability space `(Ω, Q)` and
acts as the deterministic learner `A(ω)`.

For every probability measure `D ∈ 𝒟`, the failure probability function
`ω ↦ D^m{S | error(A(ω)(S)) > opt_C(D) + ε}` must be `Q`-a.e. measurable, and its
expectation over `ω` must be at most `δ`.

The randomness space `Ω : Type*` is universe-polymorphic; the universe is an implicit
parameter of `IsRPACLearnerFor`, and downstream statements reference it via the pattern
`IsRPACLearnerFor.{_, _, u}`. Fix `u := 0` for the usual case of a standard randomness space.

A deterministic learner (`IsPACLearnerFor`) is the special case `Ω = PUnit`;
see `IsPACLearnerFor.toIsRPACLearnerFor`. -/
def IsRPACLearnerFor (m : ℕ) (ε δ : Set.Ioo (0 : ℝ≥0) 1)
    (C : ConceptClass α β) (𝒟 : Set (Measure (α × β))) : Prop :=
  ∃ (Ω : Type*) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
    (A : Ω → Learner α β m),
    ∀ (D : Measure (α × β)) [IsProbabilityMeasure D], D ∈ 𝒟 →
      AEMeasurable (fun ω => (Measure.pi (fun _ : Fin m => D))
        {S : LabeledSample α β m |
          optimalError D C + ↑ε.val < error D ((A ω) S)}) Q ∧
      ∫⁻ ω, (Measure.pi (fun _ : Fin m => D))
        {S : LabeledSample α β m |
          optimalError D C + ↑ε.val < error D ((A ω) S)} ∂Q ≤ ↑δ.val

/-- Every deterministic PAC learner is in particular a randomized PAC learner
(with the trivial one-point randomness space `PUnit`). -/
theorem IsPACLearnerFor.toIsRPACLearnerFor {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    {C : ConceptClass α β} {𝒟 : Set (Measure (α × β))}
    (h : IsPACLearnerFor m ε δ C 𝒟) :
    IsRPACLearnerFor m ε δ C 𝒟 := by
  obtain ⟨A, hA⟩ := h
  refine ⟨PUnit, inferInstance, Measure.dirac PUnit.unit, inferInstance, fun _ => A, ?_⟩
  intro D _ hD
  refine ⟨measurable_const.aemeasurable, ?_⟩
  simp only [lintegral_const, measure_univ, mul_one]
  exact hA D hD

/-- The deterministic PAC learner predicate is antitone in the distribution family: a
learner for a larger family `𝒟'` is also a learner for any subfamily `𝒟 ⊆ 𝒟'`. -/
theorem IsPACLearnerFor.antitone_family {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    {C : ConceptClass α β} {𝒟 𝒟' : Set (Measure (α × β))}
    (h𝒟 : 𝒟 ⊆ 𝒟') (h : IsPACLearnerFor m ε δ C 𝒟') :
    IsPACLearnerFor m ε δ C 𝒟 := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, fun D inst hD => @hA D inst (h𝒟 hD)⟩

/-- A PAC learner with confidence `δ₁` is also a PAC learner with any weaker confidence
`δ₂ ≥ δ₁`: the failure-probability bound only gets looser. -/
theorem IsPACLearnerFor.mono_δ {m : ℕ} {ε : Set.Ioo (0 : ℝ≥0) 1}
    {δ₁ δ₂ : Set.Ioo (0 : ℝ≥0) 1} (hδ : δ₁.val ≤ δ₂.val)
    {C : ConceptClass α β} {𝒟 : Set (Measure (α × β))}
    (h : IsPACLearnerFor m ε δ₁ C 𝒟) :
    IsPACLearnerFor m ε δ₂ C 𝒟 := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A, fun D inst hD => le_trans (@hA D inst hD) ?_⟩
  exact_mod_cast hδ

/-- A PAC learner with accuracy `ε₁` is also a PAC learner with any weaker accuracy
`ε₂ ≥ ε₁`: the bad event `{error > opt + ε}` only shrinks. -/
theorem IsPACLearnerFor.mono_ε {m : ℕ} {δ : Set.Ioo (0 : ℝ≥0) 1}
    {ε₁ ε₂ : Set.Ioo (0 : ℝ≥0) 1} (hε : ε₁.val ≤ ε₂.val)
    {C : ConceptClass α β} {𝒟 : Set (Measure (α × β))}
    (h : IsPACLearnerFor m ε₁ δ C 𝒟) :
    IsPACLearnerFor m ε₂ δ C 𝒟 := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A, fun D inst hD => le_trans (measure_mono ?_) (@hA D inst hD)⟩
  intro S hS
  have hε' : (↑ε₁.val : ℝ≥0∞) ≤ ↑ε₂.val := by exact_mod_cast hε
  calc optimalError D C + (↑ε₁.val : ℝ≥0∞)
      ≤ optimalError D C + ↑ε₂.val := by gcongr
    _ < error D (A S) := hS

/-- The deterministic PAC learner predicate is antitone in the concept class: a learner
for a larger class `C'` is also a learner for any subclass `C ⊆ C'`, since the agnostic
benchmark `optimalError _ C ≥ optimalError _ C'` makes the error requirement easier. -/
theorem IsPACLearnerFor.antitone_C {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    {C C' : ConceptClass α β} (hC : C ⊆ C')
    {𝒟 : Set (Measure (α × β))} (h : IsPACLearnerFor m ε δ C' 𝒟) :
    IsPACLearnerFor m ε δ C 𝒟 := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A, fun D inst hD => le_trans (measure_mono ?_) (@hA D inst hD)⟩
  intro S hS
  have h_opt : optimalError D C' ≤ optimalError D C := iInf_le_iInf_of_subset hC
  calc optimalError D C' + (↑ε.val : ℝ≥0∞)
      ≤ optimalError D C + ↑ε.val := by gcongr
    _ < error D (A S) := hS

/-- The randomized PAC learner predicate is antitone in the distribution family. The
universe of the randomness space `Ω` is pinned so the hypothesis and conclusion share it. -/
theorem IsRPACLearnerFor.antitone_family.{u} {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    {C : ConceptClass α β} {𝒟 𝒟' : Set (Measure (α × β))}
    (h𝒟 : 𝒟 ⊆ 𝒟') (h : IsRPACLearnerFor.{_, _, u} m ε δ C 𝒟') :
    IsRPACLearnerFor.{_, _, u} m ε δ C 𝒟 := by
  obtain ⟨Ω, mΩ, Q, hQ, A, hA⟩ := h
  exact ⟨Ω, mΩ, Q, hQ, A, fun D inst hD => @hA D inst (h𝒟 hD)⟩

/-- A randomized PAC learner with confidence `δ₁` is also a randomized PAC learner with
any weaker confidence `δ₂ ≥ δ₁`. Unlike `mono_ε` or `antitone_C`, this does not touch the
integrand, so it carries the `AEMeasurable` part through unchanged. -/
theorem IsRPACLearnerFor.mono_δ.{u} {m : ℕ} {ε : Set.Ioo (0 : ℝ≥0) 1}
    {δ₁ δ₂ : Set.Ioo (0 : ℝ≥0) 1} (hδ : δ₁.val ≤ δ₂.val)
    {C : ConceptClass α β} {𝒟 : Set (Measure (α × β))}
    (h : IsRPACLearnerFor.{_, _, u} m ε δ₁ C 𝒟) :
    IsRPACLearnerFor.{_, _, u} m ε δ₂ C 𝒟 := by
  obtain ⟨Ω, mΩ, Q, hQ, A, hA⟩ := h
  refine ⟨Ω, mΩ, Q, hQ, A, fun D inst hD => ?_⟩
  obtain ⟨hmeas, hint⟩ := @hA D inst hD
  refine ⟨hmeas, le_trans hint ?_⟩
  exact_mod_cast hδ

/-! ### PAC Learnability -/

/-- A concept class `C` is *PAC learnable* over the distribution family `𝒟` if for every
accuracy `ε ∈ (0, 1)` and confidence `δ ∈ (0, 1)`, there exists a sample size `m` admitting
a deterministic `(ε, δ)`-PAC learner for `C`. Here `ε` and `δ` are elements of the subtype
`Set.Ioo (0 : ℝ≥0) 1`. -/
def IsPACLearnable (C : ConceptClass α β) (𝒟 : Set (Measure (α × β))) : Prop :=
  ∀ (ε δ : Set.Ioo (0 : ℝ≥0) 1),
    ∃ m, IsPACLearnerFor m ε δ C 𝒟

/-- A concept class `C` is *randomized PAC learnable* over the distribution family `𝒟` if for
every accuracy `ε ∈ (0, 1)` and confidence `δ ∈ (0, 1)`, there exists a sample size `m`
admitting a randomized `(ε, δ)`-PAC learner for `C`. The randomness space is pinned to
`Type 0` at the learnability level; `IsRPACLearnerFor` itself remains universe-polymorphic. -/
def IsRPACLearnable (C : ConceptClass α β) (𝒟 : Set (Measure (α × β))) : Prop :=
  ∀ (ε δ : Set.Ioo (0 : ℝ≥0) 1),
    ∃ m, IsRPACLearnerFor.{_, _, 0} m ε δ C 𝒟

/-- Deterministic PAC learnability implies randomized PAC learnability. -/
theorem IsPACLearnable.toIsRPACLearnable {C : ConceptClass α β}
    {𝒟 : Set (Measure (α × β))} (h : IsPACLearnable C 𝒟) :
    IsRPACLearnable C 𝒟 := by
  intro ε δ
  obtain ⟨m, hm⟩ := h ε δ
  exact ⟨m, hm.toIsRPACLearnerFor⟩

/-- PAC learnability is antitone in the distribution family: a subfamily of a learnable
family is learnable. -/
theorem IsPACLearnable.antitone_family {C : ConceptClass α β} {𝒟 𝒟' : Set (Measure (α × β))}
    (h𝒟 : 𝒟 ⊆ 𝒟') (h : IsPACLearnable C 𝒟') : IsPACLearnable C 𝒟 :=
  fun ε δ => (h ε δ).imp fun _ hm => hm.antitone_family h𝒟

/-- PAC learnability is antitone in the concept class: a subclass of a learnable class is
learnable. -/
theorem IsPACLearnable.antitone_C {C C' : ConceptClass α β} (hC : C ⊆ C')
    {𝒟 : Set (Measure (α × β))} (h : IsPACLearnable C' 𝒟) : IsPACLearnable C 𝒟 :=
  fun ε δ => (h ε δ).imp fun _ hm => hm.antitone_C hC

/-- Randomized PAC learnability is antitone in the distribution family. -/
theorem IsRPACLearnable.antitone_family {C : ConceptClass α β}
    {𝒟 𝒟' : Set (Measure (α × β))} (h𝒟 : 𝒟 ⊆ 𝒟')
    (h : IsRPACLearnable C 𝒟') : IsRPACLearnable C 𝒟 :=
  fun ε δ => (h ε δ).imp fun _ hm => hm.antitone_family h𝒟

/-! ### Sample Complexity -/

/-- A *learner model* is a predicate on (sample size, accuracy, confidence, concept class,
distribution family) that classifies which sample sizes admit a learner of the given kind.
Instantiating with `IsPACLearnerFor` gives the deterministic model; with `IsRPACLearnerFor`
gives the randomized one. -/
abbrev LearnerModel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] :=
  ℕ → Set.Ioo (0 : ℝ≥0) 1 → Set.Ioo (0 : ℝ≥0) 1 →
    ConceptClass α β → Set (Measure (α × β)) → Prop

/-- The *sample complexity* of a concept class `C` under a learner model `L`, at accuracy
`ε ∈ (0, 1)` and confidence `δ ∈ (0, 1)` over distribution family `𝒟`, is the smallest sample
size `m` with `L m ε δ C 𝒟`. Specialize with `L := IsPACLearnerFor` for the deterministic model
and `L := IsRPACLearnerFor` for the randomized one.

**Caveat**: because `sInf` on `ℕ` returns `0` for the empty set, this definition returns `0`
when no learner exists (e.g., a concept class of infinite VC dimension). It is only meaningful
when the defining set `{m | L m ε δ C 𝒟}` is nonempty. The `IsPACLearnable.sampleComplexity_*`
variants below discharge this nonemptiness from a learnability hypothesis. -/
noncomputable def sampleComplexity (L : LearnerModel α β) (C : ConceptClass α β)
    (ε δ : Set.Ioo (0 : ℝ≥0) 1) (𝒟 : Set (Measure (α × β))) : ℕ :=
  sInf {m : ℕ | L m ε δ C 𝒟}

/-- The *randomized sample complexity* of `C`, i.e. `sampleComplexity` instantiated at the
randomized learner model `IsRPACLearnerFor`. The randomness space is pinned to `Type 0`. -/
noncomputable def rsampleComplexity (C : ConceptClass α β) (ε δ : Set.Ioo (0 : ℝ≥0) 1)
    (𝒟 : Set (Measure (α × β))) : ℕ :=
  sampleComplexity IsRPACLearnerFor.{_, _, 0} C ε δ 𝒟

/-! ### Monotonicity of Sample Complexity

These lemmas are all special cases of the following observation: if `{m | L₁ m ε₁ δ₁ C₁ 𝒟₁} ⊆
{m | L₂ m ε₂ δ₂ C₂ 𝒟₂}` and the first set is nonempty, then the sample complexity under
`(L₂, ε₂, δ₂, C₂, 𝒟₂)` is at most the sample complexity under `(L₁, ε₁, δ₁, C₁, 𝒟₁)`. The
nonemptiness hypothesis is essential: `sInf` on `ℕ` returns `0` for an empty set, so without
it the inequality can fail at the degenerate boundary. The `IsPACLearnable`-flavoured variants
at the end of this section discharge that witness from a learnability hypothesis. -/

/-- General pointwise monotonicity of `sampleComplexity`: if every witness sample size for
`(L₁, ε₁, δ₁, C₁, 𝒟₁)` is also a witness for `(L₂, ε₂, δ₂, C₂, 𝒟₂)`, then the latter's
sample complexity is at most the former's (provided the former is attained). -/
theorem sampleComplexity_le_of_forall {L₁ L₂ : LearnerModel α β}
    {ε₁ δ₁ ε₂ δ₂ : Set.Ioo (0 : ℝ≥0) 1} {C₁ C₂ : ConceptClass α β}
    {𝒟₁ 𝒟₂ : Set (Measure (α × β))}
    (hL : ∀ {m : ℕ}, L₁ m ε₁ δ₁ C₁ 𝒟₁ → L₂ m ε₂ δ₂ C₂ 𝒟₂)
    (h : ∃ m, L₁ m ε₁ δ₁ C₁ 𝒟₁) :
    sampleComplexity L₂ C₂ ε₂ δ₂ 𝒟₂ ≤ sampleComplexity L₁ C₁ ε₁ δ₁ 𝒟₁ :=
  Nat.sInf_le (hL (Nat.sInf_mem (s := {m | L₁ m ε₁ δ₁ C₁ 𝒟₁}) h))

/-- Deterministic sample complexity is antitone in the confidence parameter `δ`: weaker
confidence requires no more samples. -/
theorem sampleComplexity_antitone_δ {ε δ₁ δ₂ : Set.Ioo (0 : ℝ≥0) 1} (hδ : δ₁.val ≤ δ₂.val)
    {C : ConceptClass α β} {𝒟 : Set (Measure (α × β))}
    (h : ∃ m, IsPACLearnerFor m ε δ₁ C 𝒟) :
    sampleComplexity IsPACLearnerFor C ε δ₂ 𝒟 ≤ sampleComplexity IsPACLearnerFor C ε δ₁ 𝒟 :=
  sampleComplexity_le_of_forall (fun h' => h'.mono_δ hδ) h

/-- Deterministic sample complexity is antitone in the accuracy parameter `ε`: weaker
accuracy requires no more samples. -/
theorem sampleComplexity_antitone_ε {ε₁ ε₂ δ : Set.Ioo (0 : ℝ≥0) 1} (hε : ε₁.val ≤ ε₂.val)
    {C : ConceptClass α β} {𝒟 : Set (Measure (α × β))}
    (h : ∃ m, IsPACLearnerFor m ε₁ δ C 𝒟) :
    sampleComplexity IsPACLearnerFor C ε₂ δ 𝒟 ≤ sampleComplexity IsPACLearnerFor C ε₁ δ 𝒟 :=
  sampleComplexity_le_of_forall (fun h' => h'.mono_ε hε) h

/-- Deterministic sample complexity is monotone in the distribution family under `⊆`: a
smaller family (fewer distributions to cover) requires no more samples. -/
theorem sampleComplexity_mono_family {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    {C : ConceptClass α β} {𝒟 𝒟' : Set (Measure (α × β))} (h𝒟 : 𝒟 ⊆ 𝒟')
    (h : ∃ m, IsPACLearnerFor m ε δ C 𝒟') :
    sampleComplexity IsPACLearnerFor C ε δ 𝒟 ≤ sampleComplexity IsPACLearnerFor C ε δ 𝒟' :=
  sampleComplexity_le_of_forall (fun h' => h'.antitone_family h𝒟) h

/-- Deterministic sample complexity is monotone in the concept class under `⊆`: a smaller
class (weaker agnostic benchmark) requires no more samples. -/
theorem sampleComplexity_mono_C {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    {C C' : ConceptClass α β} (hC : C ⊆ C') {𝒟 : Set (Measure (α × β))}
    (h : ∃ m, IsPACLearnerFor m ε δ C' 𝒟) :
    sampleComplexity IsPACLearnerFor C ε δ 𝒟 ≤ sampleComplexity IsPACLearnerFor C' ε δ 𝒟 :=
  sampleComplexity_le_of_forall (fun h' => h'.antitone_C hC) h

/-- Randomized sample complexity is antitone in the confidence parameter `δ`. -/
theorem rsampleComplexity_antitone_δ {ε δ₁ δ₂ : Set.Ioo (0 : ℝ≥0) 1}
    (hδ : δ₁.val ≤ δ₂.val) {C : ConceptClass α β} {𝒟 : Set (Measure (α × β))}
    (h : ∃ m, IsRPACLearnerFor.{_, _, 0} m ε δ₁ C 𝒟) :
    rsampleComplexity C ε δ₂ 𝒟 ≤ rsampleComplexity C ε δ₁ 𝒟 :=
  sampleComplexity_le_of_forall (fun h' => h'.mono_δ hδ) h

/-- Randomized sample complexity is monotone in the distribution family under `⊆`. -/
theorem rsampleComplexity_mono_family {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    {C : ConceptClass α β} {𝒟 𝒟' : Set (Measure (α × β))} (h𝒟 : 𝒟 ⊆ 𝒟')
    (h : ∃ m, IsRPACLearnerFor.{_, _, 0} m ε δ C 𝒟') :
    rsampleComplexity C ε δ 𝒟 ≤ rsampleComplexity C ε δ 𝒟' :=
  sampleComplexity_le_of_forall (fun h' => h'.antitone_family h𝒟) h

/-! Convenience variants conditional on learnability, which discharge the nonemptiness
hypothesis `(∃ m, IsPACLearnerFor m …)` from an `IsPACLearnable` / `IsRPACLearnable` witness.
Bodies go through `sampleComplexity_le_of_forall` directly rather than the top-level
`sampleComplexity_*` lemmas, whose unqualified names would resolve as self-recursion inside
these theorems' `IsPACLearnable.*` / `IsRPACLearnable.*` namespaces. -/

/-- `sampleComplexity_antitone_δ` for a learnable class: the nonemptiness hypothesis comes
for free from `IsPACLearnable`. -/
theorem IsPACLearnable.sampleComplexity_antitone_δ
    {C : ConceptClass α β} {𝒟 : Set (Measure (α × β))} (hL : IsPACLearnable C 𝒟)
    {ε δ₁ δ₂ : Set.Ioo (0 : ℝ≥0) 1} (hδ : δ₁.val ≤ δ₂.val) :
    sampleComplexity IsPACLearnerFor C ε δ₂ 𝒟 ≤ sampleComplexity IsPACLearnerFor C ε δ₁ 𝒟 :=
  sampleComplexity_le_of_forall (fun h' => h'.mono_δ hδ) (hL ε δ₁)

/-- `sampleComplexity_antitone_ε` for a learnable class. -/
theorem IsPACLearnable.sampleComplexity_antitone_ε
    {C : ConceptClass α β} {𝒟 : Set (Measure (α × β))} (hL : IsPACLearnable C 𝒟)
    {ε₁ ε₂ δ : Set.Ioo (0 : ℝ≥0) 1} (hε : ε₁.val ≤ ε₂.val) :
    sampleComplexity IsPACLearnerFor C ε₂ δ 𝒟 ≤ sampleComplexity IsPACLearnerFor C ε₁ δ 𝒟 :=
  sampleComplexity_le_of_forall (fun h' => h'.mono_ε hε) (hL ε₁ δ)

/-- `sampleComplexity_mono_family` for a learnable class (learnability at the *larger*
family `𝒟'` is the hypothesis). -/
theorem IsPACLearnable.sampleComplexity_mono_family
    {C : ConceptClass α β} {𝒟 𝒟' : Set (Measure (α × β))}
    (hL : IsPACLearnable C 𝒟') (h𝒟 : 𝒟 ⊆ 𝒟') {ε δ : Set.Ioo (0 : ℝ≥0) 1} :
    sampleComplexity IsPACLearnerFor C ε δ 𝒟 ≤ sampleComplexity IsPACLearnerFor C ε δ 𝒟' :=
  sampleComplexity_le_of_forall (fun h' => h'.antitone_family h𝒟) (hL ε δ)

/-- `sampleComplexity_mono_C` for a learnable class (learnability at the *larger* class
`C'` is the hypothesis). -/
theorem IsPACLearnable.sampleComplexity_mono_C
    {C C' : ConceptClass α β} {𝒟 : Set (Measure (α × β))}
    (hL : IsPACLearnable C' 𝒟) (hC : C ⊆ C') {ε δ : Set.Ioo (0 : ℝ≥0) 1} :
    sampleComplexity IsPACLearnerFor C ε δ 𝒟 ≤ sampleComplexity IsPACLearnerFor C' ε δ 𝒟 :=
  sampleComplexity_le_of_forall (fun h' => h'.antitone_C hC) (hL ε δ)

/-- `rsampleComplexity_antitone_δ` for a randomized-learnable class. -/
theorem IsRPACLearnable.rsampleComplexity_antitone_δ
    {C : ConceptClass α β} {𝒟 : Set (Measure (α × β))} (hL : IsRPACLearnable C 𝒟)
    {ε δ₁ δ₂ : Set.Ioo (0 : ℝ≥0) 1} (hδ : δ₁.val ≤ δ₂.val) :
    rsampleComplexity C ε δ₂ 𝒟 ≤ rsampleComplexity C ε δ₁ 𝒟 :=
  sampleComplexity_le_of_forall (fun h' => h'.mono_δ hδ) (hL ε δ₁)

/-- `rsampleComplexity_mono_family` for a randomized-learnable class. -/
theorem IsRPACLearnable.rsampleComplexity_mono_family
    {C : ConceptClass α β} {𝒟 𝒟' : Set (Measure (α × β))}
    (hL : IsRPACLearnable C 𝒟') (h𝒟 : 𝒟 ⊆ 𝒟') {ε δ : Set.Ioo (0 : ℝ≥0) 1} :
    rsampleComplexity C ε δ 𝒟 ≤ rsampleComplexity C ε δ 𝒟' :=
  sampleComplexity_le_of_forall (fun h' => h'.antitone_family h𝒟) (hL ε δ)

end

/-! ### Binary Classification

When `β = Bool`, concepts correspond to subsets of `α` via the characteristic function.
The symmetric-difference error `P(h ∆ c)` is the natural error metric, and it decomposes
into false positive and false negative components.

The bridge lemma `error_map_eq_hypothesisError` connects the general `error` on `α × Bool`
to the binary `hypothesisError` on `α`, showing they coincide for realizable distributions. -/

section Binary
variable {α : Type*} [MeasurableSpace α]

/-- The *symmetric-difference error* of a hypothesis `h` with respect to a target concept `c`
(both viewed as subsets of `α`) under distribution `P`, defined as `P(h ∆ c)`. -/
noncomputable def hypothesisError (P : Measure α) (h c : Set α) : ℝ≥0∞ :=
  P (symmDiff h c)

/-- The *false positive error* `P(h \ c)` — points classified positive but not in the
concept. -/
noncomputable def falsePositiveError (P : Measure α) (h c : Set α) : ℝ≥0∞ :=
  P (h \ c)

/-- The *false negative error* `P(c \ h)` — points in the concept but classified negative. -/
noncomputable def falseNegativeError (P : Measure α) (h c : Set α) : ℝ≥0∞ :=
  P (c \ h)

/-- The total hypothesis error decomposes as the sum of false positive and false negative
errors, since `h ∆ c = (h \ c) ∪ (c \ h)` is a disjoint union. -/
theorem hypothesisError_eq_add {P : Measure α} {h c : Set α}
    (hh : MeasurableSet h) (hc : MeasurableSet c) :
    hypothesisError P h c = falsePositiveError P h c + falseNegativeError P h c :=
  measure_union disjoint_sdiff_sdiff (hc.diff hh)

open scoped Classical in
/-- Under a realizable distribution `P.map (x ↦ (x, c(x)))`, the general 0-1 `error`
coincides with the binary `hypothesisError P h c`, where `h` and `c` are viewed as subsets
of `α` via the characteristic function `decide (· ∈ ·)`. -/
theorem error_map_eq_hypothesisError (P : Measure α) (h c : Set α)
    (hh : MeasurableSet h) (hc : MeasurableSet c) :
    error (P.map (fun x => (x, decide (x ∈ c)))) (fun x => decide (x ∈ h)) =
    hypothesisError P h c := by
  simp only [error, hypothesisError]
  have hf : Measurable (fun x => (x, decide (x ∈ c))) :=
    Measurable.prodMk measurable_id
      (measurable_to_bool (by convert hc using 1; ext x; simp [decide_eq_true_eq]))
  rw [Measure.map_apply_of_aemeasurable hf.aemeasurable]
  · congr 1; ext x
    by_cases hx : x ∈ h <;> simp_all [symmDiff_def]
  · convert (hh.prod (measurableSet_singleton false)).union
      (hh.compl.prod (measurableSet_singleton true)) using 1
    ext ⟨x, b⟩; cases b <;> simp

end Binary

end Cslib.MachineLearning.PACLearning
