/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/

module

public import Cslib.MachineLearning.PACLearning.Defs
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Map

/-! # Version Space

The *version space* of a concept class `C` given a labeled sample `S` is the
subset of `C` whose concepts agree with `S` on every observed point — the
classical "concepts still consistent with the data" of Mitchell (1977) and
Angluin (1980).

## Main definitions

- `VersionSpace C S`: the subset of `C` whose concepts agree with `S` on every
  sample point.
- `IsConsistent A C`: a learner is consistent with `C` if its output lies in
  the version space at every realizable sample.
- `empiricalMiscount h S`: number of sample points where `h` errs (`[DecidableEq β]`).
- `empiricalMeasure S`: the uniform Dirac mixture over the sample.
- `empiricalError h S`: the empirical distribution's mass on the disagreement set.
- `Realizable C S`: some concept in `C` labels every sample point correctly.

## Main results

- `versionSpace_subset`, `versionSpace_empty_sample`, `versionSpace_reindex`,
  `versionSpace_antitone`, `versionSpace_mono_C`: structural properties.
- `mem_versionSpace_iff_empiricalMiscount_zero`: combinatorial bridge.
- `mem_versionSpace_iff_empiricalError_zero`: measure-theoretic bridge.
- `IsConsistent.empiricalMiscount_eq_zero`, `IsConsistent.empiricalError_eq_zero`:
  consistent learners achieve zero error / miscount on every realizable sample.
- `mem_versionSpace_of_realizable`, `Realizable.versionSpace_nonempty`: realizable
  samples give non-empty version spaces.
- `ae_mem_versionSpace_of_realizable`: under iid sampling from a realizable
  joint distribution, the target concept lies in the version space almost surely.

## References

* [Mitchell1977]
* [Mitchell1982]
* [Angluin1980]
* [Mitchell1997]
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Cslib.MachineLearning.PACLearning

variable {α : Type*} {β : Type*}

/-! ### Version Space -/

/-- The *version space* of a concept class `C` given a labeled sample `S`:
the set of concepts in `C` whose labels agree with `S` on every observed point. -/
def VersionSpace {m : ℕ} (C : ConceptClass α β) (S : LabeledSample α β m) :
    ConceptClass α β :=
  {h ∈ C | ∀ i : Fin m, h (S i).1 = (S i).2}

/-- Membership in the version space unfolds to concept membership plus
per-sample consistency. -/
theorem mem_versionSpace_iff {m : ℕ} {C : ConceptClass α β}
    {S : LabeledSample α β m} {h : α → β} :
    h ∈ VersionSpace C S ↔ h ∈ C ∧ ∀ i : Fin m, h (S i).1 = (S i).2 := Iff.rfl

/-- The version space is a subset of the original concept class. -/
theorem versionSpace_subset {m : ℕ} (C : ConceptClass α β)
    (S : LabeledSample α β m) :
    VersionSpace C S ⊆ C := fun _ hh => hh.1

/-- Version space on the empty sample equals the whole concept class. -/
theorem versionSpace_empty_sample (C : ConceptClass α β)
    (S : LabeledSample α β 0) :
    VersionSpace C S = C := by
  ext h
  exact ⟨fun hh => hh.1, fun hh => ⟨hh, fun i => i.elim0⟩⟩

/-- *Version space reindexing.* For any reindexing `f : Fin m → Fin n`, the
version space on `S` is contained in the version space on the reindexed sample
`S ∘ f`. -/
theorem versionSpace_reindex {m n : ℕ} (f : Fin m → Fin n) (C : ConceptClass α β)
    (S : LabeledSample α β n) :
    VersionSpace C S ⊆ VersionSpace C (S ∘ f) :=
  fun _ hh => ⟨hh.1, fun i => hh.2 (f i)⟩

/-- *Version space antitonicity.* Given a sample of size `n` and `m ≤ n`, the
version space on all `n` observations is a subset of the version space on the
first `m` observations. Special case of `versionSpace_reindex` with
`f := Fin.castLE hmn`. -/
theorem versionSpace_antitone {m n : ℕ} (hmn : m ≤ n) (C : ConceptClass α β)
    (S : LabeledSample α β n) :
    VersionSpace C S ⊆ VersionSpace C (S ∘ Fin.castLE hmn) :=
  versionSpace_reindex (Fin.castLE hmn) C S

/-- *Version space is monotone in the concept class.* -/
theorem versionSpace_mono_C {m : ℕ} {C C' : ConceptClass α β} (hCC' : C ⊆ C')
    (S : LabeledSample α β m) :
    VersionSpace C S ⊆ VersionSpace C' S :=
  fun _ hh => ⟨hCC' hh.1, hh.2⟩

/-! ### Empirical Error -/

/-- The *empirical miscount* of a hypothesis `h` on a labeled sample `S`: the
number of sample points where `h` predicts incorrectly. -/
def empiricalMiscount [DecidableEq β] {m : ℕ} (h : α → β)
    (S : LabeledSample α β m) : ℕ :=
  (Finset.univ.filter fun i : Fin m => h (S i).1 ≠ (S i).2).card

section EmpiricalMeasure
variable [MeasurableSpace α] [MeasurableSpace β]

/-- The *empirical distribution* of a labeled sample: the uniform mixture of
Dirac measures at each sample point. Equals the zero measure when `m = 0`. -/
noncomputable def empiricalMeasure {m : ℕ} (S : LabeledSample α β m) :
    Measure (α × β) :=
  if _hm : m = 0 then 0
  else (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (S i)

/-- The *empirical 0-1 error* of `h` on `S`: the empirical distribution's
mass on the disagreement set. -/
noncomputable def empiricalError {m : ℕ} (h : α → β) (S : LabeledSample α β m) :
    ℝ≥0∞ :=
  error (empiricalMeasure S) h

end EmpiricalMeasure

/-- Version-space membership equals concept-class membership plus zero empirical
miscount (combinatorial bridge). -/
theorem mem_versionSpace_iff_empiricalMiscount_zero [DecidableEq β]
    {m : ℕ} {C : ConceptClass α β} {S : LabeledSample α β m} {h : α → β} :
    h ∈ VersionSpace C S ↔ h ∈ C ∧ empiricalMiscount h S = 0 := by
  simp only [empiricalMiscount, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
             Finset.mem_univ, true_implies, ne_eq, Decidable.not_not]
  rfl

/-- Version-space membership equals concept-class membership plus zero empirical
error (measure-theoretic bridge). -/
theorem mem_versionSpace_iff_empiricalError_zero
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {m : ℕ} {C : ConceptClass α β} {S : LabeledSample α β m} {h : α → β} :
    h ∈ VersionSpace C S ↔ h ∈ C ∧ empiricalError h S = 0 := by
  refine and_congr_right fun _ => ?_
  unfold empiricalError empiricalMeasure error
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · simp_all [Nat.pos_iff_ne_zero]

/-- The empirical 0-1 error equals the empirical miscount divided by the
sample size. -/
theorem empiricalError_eq_div [DecidableEq β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {m : ℕ} (hm : 0 < m) (h : α → β) (S : LabeledSample α β m) :
    empiricalError h S = (empiricalMiscount h S : ℝ≥0∞) / m := by
  have hm_ne : m ≠ 0 := hm.ne'
  unfold empiricalError empiricalMeasure error empiricalMiscount
  rw [dite_eq_right hm_ne, smul_apply, sum_apply]
  simp only [Measure.dirac_apply, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply, smul_eq_mul]
  rw [Finset.sum_boole, ← ENNReal.div_eq_inv_mul]

/-! ### Realizable Samples -/

/-- A labeled sample `S` is *realizable* by concept class `C` if some concept
in `C` labels every sample point correctly. -/
def Realizable {m : ℕ} (C : ConceptClass α β) (S : LabeledSample α β m) : Prop :=
  ∃ c ∈ C, ∀ i : Fin m, (S i).2 = c (S i).1

/-! ### Consistent Learners -/

/-- A learner is *consistent* with the concept class `C` if, on every sample
realizable by `C`, its output hypothesis lies in the version space of `C` at
that sample — i.e. the output is in `C` and agrees with every observed labeled
pair. No condition is imposed on samples that no concept in `C` can realize. -/
def IsConsistent {m : ℕ} (A : Learner α β m) (C : ConceptClass α β) : Prop :=
  ∀ S : LabeledSample α β m, Realizable C S → A S ∈ VersionSpace C S

/-- A consistent learner's output is in the concept class on every realizable sample. -/
theorem IsConsistent.output_mem_conceptClass {m : ℕ} {A : Learner α β m}
    {C : ConceptClass α β} (hA : IsConsistent A C) (S : LabeledSample α β m)
    (hS : Realizable C S) :
    A S ∈ C := (hA S hS).1

/-- On every realizable sample, a consistent learner's output agrees with
every observed point. -/
theorem IsConsistent.output_agrees {m : ℕ} {A : Learner α β m}
    {C : ConceptClass α β} (hA : IsConsistent A C) (S : LabeledSample α β m)
    (hS : Realizable C S) (i : Fin m) :
    A S (S i).1 = (S i).2 := (hA S hS).2 i

/-- A consistent learner has zero empirical miscount on every realizable sample. -/
theorem IsConsistent.empiricalMiscount_eq_zero [DecidableEq β]
    {m : ℕ} {A : Learner α β m} {C : ConceptClass α β} (hA : IsConsistent A C)
    (S : LabeledSample α β m) (hS : Realizable C S) :
    empiricalMiscount (A S) S = 0 :=
  (mem_versionSpace_iff_empiricalMiscount_zero.mp (hA S hS)).2

/-- A consistent learner has zero empirical error on every realizable sample. -/
theorem IsConsistent.empiricalError_eq_zero
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {m : ℕ} {A : Learner α β m} {C : ConceptClass α β}
    (hA : IsConsistent A C) (S : LabeledSample α β m) (hS : Realizable C S) :
    empiricalError (A S) S = 0 :=
  (mem_versionSpace_iff_empiricalError_zero.mp (hA S hS)).2

/-! ### Realizable Version Spaces -/

/-- *Realizable version-space nonemptiness.* If a target concept `c` lies in
`C` and the sample `S` is labeled by `c` (i.e. every `(S i).2 = c (S i).1`),
then `c` itself lies in the version space `VersionSpace C S`. -/
theorem mem_versionSpace_of_realizable {m : ℕ} {C : ConceptClass α β}
    {c : α → β} (hc : c ∈ C) (S : LabeledSample α β m)
    (hS : ∀ i : Fin m, (S i).2 = c (S i).1) :
    c ∈ VersionSpace C S :=
  ⟨hc, fun i => (hS i).symm⟩

/-- A realizable sample has nonempty version space. -/
theorem Realizable.versionSpace_nonempty {m : ℕ} {C : ConceptClass α β}
    {S : LabeledSample α β m} (h : Realizable C S) :
    (VersionSpace C S).Nonempty :=
  ⟨h.choose, mem_versionSpace_of_realizable h.choose_spec.1 S h.choose_spec.2⟩

/-! ### Probabilistic Realizable -/

/-- Under the pushforward of a probability measure `P` along the graph map
`x ↦ (x, c x)`, the graph of `c` has measure `1`. -/
private lemma map_graph_eq_one
    [MeasurableSpace α] [MeasurableSpace β]
    {c : α → β} (hcm : Measurable c) (P : Measure α) [IsProbabilityMeasure P]
    (hG : MeasurableSet {p : α × β | p.2 = c p.1}) :
    (P.map (fun x => (x, c x))) {p : α × β | p.2 = c p.1} = 1 := by
  have hφ : Measurable (fun x : α => (x, c x)) := by fun_prop
  rw [Measure.map_apply hφ hG]
  have hpre : (fun x : α => (x, c x)) ⁻¹' {p : α × β | p.2 = c p.1} = Set.univ := by
    ext x; simp
  rw [hpre, measure_univ]

/-- The iid product of the realizable joint distribution assigns measure `1`
to the set of samples where every coordinate lies on the graph of `c`. -/
private lemma pi_map_graph_eq_one
    [MeasurableSpace α] [MeasurableSpace β]
    {c : α → β} (hcm : Measurable c) (P : Measure α) [IsProbabilityMeasure P]
    (hG : MeasurableSet {p : α × β | p.2 = c p.1}) {m : ℕ} :
    (Measure.pi (fun _ : Fin m => P.map (fun x => (x, c x))))
      (Set.univ.pi (fun _ : Fin m => {p : α × β | p.2 = c p.1})) = 1 := by
  have hφ : Measurable (fun x : α => (x, c x)) := by fun_prop
  simp [map_graph_eq_one hcm P hG]

/-- Under iid sampling from the realizable joint distribution induced by
`c ∈ C` and a probability measure `P` on `α`, the target concept `c` lies in
the version space almost surely. -/
theorem ae_mem_versionSpace_of_realizable
    [MeasurableSpace α] [MeasurableSpace β]
    {C : ConceptClass α β} {c : α → β} (hc : c ∈ C) (hcm : Measurable c)
    (hG : MeasurableSet {p : α × β | p.2 = c p.1})
    (P : Measure α) [IsProbabilityMeasure P] (m : ℕ) :
    ∀ᵐ S : LabeledSample α β m
      ∂(Measure.pi (fun _ : Fin m => P.map (fun x => (x, c x)))),
      c ∈ VersionSpace C S := by
  have hsub : {S : Fin m → α × β | ¬ c ∈ VersionSpace C S} ⊆
      (Set.univ.pi (fun _ : Fin m => {p : α × β | p.2 = c p.1}))ᶜ := by
    intro S hS hcontra
    exact hS ⟨hc, by simp_all⟩
  have hcompl : (Measure.pi (fun _ : Fin m => P.map (fun x : α => (x, c x))))
      ((Set.univ.pi (fun _ : Fin m => {p : α × β | p.2 = c p.1}))ᶜ) = 0 := by
    rw [prob_compl_eq_one_sub (MeasurableSet.univ_pi fun _ => hG),
        pi_map_graph_eq_one hcm P hG, tsub_self]
  exact measure_mono_null hsub hcompl

end Cslib.MachineLearning.PACLearning
