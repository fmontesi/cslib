import Cslib.Foundations.Semantics.LTS.Bisimulation
import Cslib.Foundations.Concurrency.Basic
import Mathlib.Data.List.Basic

/-! Luc's playground
  With help from DeepSeek-V4.1-Flash-1017.
-/

namespace Cslib.Concurrency

-- placeholder characterisation of sane' alphabet
def SaneAlphabet (_ : Type*) : Prop :=
  true

-- identify conditionals and matching sets of labels within an alphabet
structure Branching (α : Type*) where
  conditional : α → Prop
  matching : α → α → Prop
  [symm : Std.Symm matching]

attribute [instance] Branching.symm

variable {State Label : Type*}

-- Defines a set of smurf LTSs.
structure Smurf (lts : LTS State Label) (I : Label → Label → Prop) [Independence I]
    (B : Branching Label) where
  -- labelling alphabet should be sane
  s : SaneAlphabet Label
  -- conditionals should come in matching sets
  m : ∀ s s₁ l₁, B.conditional l₁ ∧ lts.Tr s l₁ s₁ ↔
    ∃ l₂, B.matching l₁ l₂ ∧ ∃ s₂, lts.Tr s l₂ s₂
  -- no local concurrency
  -- pairs of outgoing transitions are either independent or part of a matching set
  u : ∀ s s₁ s₂ l₁ l₂, lts.Tr s l₁ s₁ ∧ lts.Tr s l₂ s₂ →
    I l₁ l₂ ∨ B.matching l₁ l₂
  -- backward concurrency
  r : ∀ s s₁ l₁ l₂, I l₁ l₂ ∧ lts.MTr s [l₁, l₂] s₁ →
    ∃ s₂, lts.Tr s l₂ s₂
  -- forward concurrency (diamond)
  f : ∀ s s₁ s₂ l₁ l₂, I l₁ l₂ ∧ lts.Tr s l₁ s₁ ∧ lts.Tr s l₂ s₂ →
    ∃ s₃, lts.Tr s₁ l₂ s₃ ∧ lts.Tr s₂ l₁ s₃

variable {Pid : Type*} [DecidableEq Pid]

-- projection of an execution trace onto a process
def ProjectTrace {pn : Label → Finset Pid} (lst : List Label) (p : Pid) : List Label :=
  lst.filter (fun l => decide (p ∈ pn l))

/-- An enabled action either commutes past an unobserved trace or encounters a matching action. -/
private lemma smurf_commute_or_matching
    {pn : Label → Finset Pid} {lts : LTS State Label}
    {I : Label → Label → Prop} [Independence I] {B : Branching Label}
    (h : Smurf lts I B) {s s₁ s₂ : State} {a : Label} {u : List Label} {p : Pid}
    (ha : lts.Tr s a s₁) (hu : lts.MTr s u s₂)
    (hproj : ProjectTrace (pn := pn) u p = []) :
    (∃ v b, v ++ [b] <+: u ∧ B.matching a b ∧ ProjectTrace (pn := pn) v p = []) ∨
      ∃ s₃, lts.MTr s₁ u s₃ ∧ lts.Tr s₂ a s₃ := by
  induction hu generalizing s₁ with
  | refl => exact Or.inr ⟨s₁, .refl, ha⟩
  | @stepL s b sm v se hb hv ih =>
    have hpb : p ∉ pn b := by
      intro hp
      simp [ProjectTrace, hp] at hproj
    have hvproj : ProjectTrace (pn := pn) v p = [] := by
      simpa [ProjectTrace, hpb] using hproj
    rcases h.u s s₁ sm a b ⟨ha, hb⟩ with hind | hm
    · obtain ⟨sx, hs₁x, hsmx⟩ := h.f s s₁ sm a b ⟨hind, ha, hb⟩
      rcases ih hsmx hvproj with ⟨w, c, hw, hm, hwp⟩ | ⟨s₃, hx₃, he₃⟩
      · refine Or.inl ⟨b :: w, c, ?_, hm, ?_⟩
        · obtain ⟨suffix, hsuffix⟩ := hw
          exact ⟨suffix, congrArg (b :: ·) hsuffix⟩
        · simpa [ProjectTrace, hpb] using hwp
      · exact Or.inr ⟨s₃, .stepL hs₁x hx₃, he₃⟩
    · exact Or.inl ⟨[], b, ⟨v, rfl⟩, hm, rfl⟩

/-- Two traces reaching their first action involving `p` encounter matching actions
after prefixes whose projections onto `p` agree. -/
private lemma smurf_first_matching
    {pn : Label → Finset Pid} {lts : LTS State Label}
    {I : Label → Label → Prop} [Independence I] {B : Branching Label}
    (h : Smurf lts I B)
    (hpn : ∀ a b, I a b → Disjoint (pn a) (pn b))
    {s s₁ s₂ : State} {u v : List Label} {a b : Label} {p : Pid}
    (hu : lts.MTr s (u ++ [a]) s₁) (hv : lts.MTr s (v ++ [b]) s₂)
    (hup : ProjectTrace (pn := pn) u p = [])
    (hvp : ProjectTrace (pn := pn) v p = []) (hap : p ∈ pn a) (hbp : p ∈ pn b) :
    ∃ u' v' a' b', u' ++ [a'] <+: u ++ [a] ∧ v' ++ [b'] <+: v ++ [b] ∧
      B.matching a' b' ∧ ProjectTrace (pn := pn) u' p = ProjectTrace (pn := pn) v' p := by
  induction u generalizing s s₂ with
  | nil =>
    have ha := LTS.MTr.single_invert lts _ _ _ hu
    obtain ⟨sv, hv', hb'⟩ := hv.split
    have hb := LTS.MTr.single_invert lts _ _ _ hb'
    rcases smurf_commute_or_matching h ha hv' hvp with
      ⟨w, c, hw, hm, hwp⟩ | ⟨sx, _, hva⟩
    · exact ⟨[], w, a, c, ⟨[], rfl⟩,
        hw.trans (List.prefix_append v [b]), hm, hwp.symm⟩
    · rcases h.u sv sx s₂ a b ⟨hva, hb⟩ with hind | hm
      · exact False.elim ((Finset.disjoint_left.mp (hpn a b hind)) hap hbp)
      · exact ⟨[], v, a, b, ⟨[], rfl⟩, ⟨[], by simp⟩, hm, hvp.symm⟩
  | cons c u ih =>
    obtain ⟨su, hc, hu'⟩ := LTS.MTr.cons_iff.mp hu
    have hpc : p ∉ pn c := by
      intro hp
      simp [ProjectTrace, hp] at hup
    have hup' : ProjectTrace (pn := pn) u p = [] := by
      simpa [ProjectTrace, hpc] using hup
    obtain ⟨sv, hv', hb'⟩ := hv.split
    have hb := LTS.MTr.single_invert lts _ _ _ hb'
    rcases smurf_commute_or_matching h hc hv' hvp with
      ⟨w, d, hw, hm, hwp⟩ | ⟨sx, huv, hvc⟩
    · exact ⟨[], w, c, d, ⟨u ++ [a], rfl⟩,
        hw.trans (List.prefix_append v [b]), hm, hwp.symm⟩
    · rcases h.u sv sx s₂ c b ⟨hvc, hb⟩ with hind | hm
      · obtain ⟨sy, hxb, _⟩ := h.f sv sx s₂ c b ⟨hind, hvc, hb⟩
        obtain ⟨u', v', a', b', hu'', hv'', hm, hp⟩ :=
          ih hu' (huv.stepR lts hxb) hup'
        refine ⟨c :: u', v', a', b', ?_, hv'', hm, ?_⟩
        · obtain ⟨suffix, hsuffix⟩ := hu''
          exact ⟨suffix, congrArg (c :: ·) hsuffix⟩
        · simpa [ProjectTrace, hpc] using hp
      · exact ⟨[], v, c, b, ⟨u ++ [a], rfl⟩, ⟨[], by simp⟩, hm, hvp.symm⟩

theorem ifSmurfThenTraces {pn : Label → Finset Pid} {lts : LTS State Label}
    {I : Label → Label → Prop} [Independence I] {B : Branching Label}
    {hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂)}
    -- {_hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → (pn l₁) = (pn l₂)}
    (h : Smurf lts I B) :
  ∀ {s : State} {t₁ t₂ : List Label} {p : Pid},
    t₁ ∈ lts.traces s ∧ t₂ ∈ lts.traces s →
    (
      ProjectTrace (pn := pn) t₁ p <+: ProjectTrace (pn := pn) t₂ p
      ∨
      ProjectTrace (pn := pn) t₂ p <+: ProjectTrace (pn := pn) t₁ p
      ∨
      (
        ∃ (q : Pid) (t₁' t₂' : List Label) (l₁ l₂ : Label),
          (
            t₁' ++ [l₁] <+: t₁
            ∧ t₂' ++ [l₂] <+: t₂
            ∧ B.matching l₁ l₂
            ∧ ProjectTrace (pn := pn) t₁' q = ProjectTrace (pn := pn) t₂' q
          )
      )
    )
  := by
  intro s t₁ t₂ p ⟨ht₁, ht₂⟩
  by_cases hp₁ : ProjectTrace (pn := pn) t₁ p = []
  · exact Or.inl (hp₁ ▸ List.nil_prefix)
  by_cases hp₂ : ProjectTrace (pn := pn) t₂ p = []
  · exact Or.inr (Or.inl (hp₂ ▸ List.nil_prefix))
  obtain ⟨a, as, hpa⟩ := List.exists_cons_of_ne_nil hp₁
  obtain ⟨b, bs, hpb⟩ := List.exists_cons_of_ne_nil hp₂
  obtain ⟨u, urest, htu, hup, hap, _⟩ := List.filter_eq_cons_iff.mp hpa
  obtain ⟨v, vrest, htv, hvp, hbp, _⟩ := List.filter_eq_cons_iff.mp hpb
  have hu : ProjectTrace (pn := pn) u p = [] := List.filter_eq_nil_iff.mpr hup
  have hv : ProjectTrace (pn := pn) v p = [] := List.filter_eq_nil_iff.mpr hvp
  have ha : p ∈ pn a := of_decide_eq_true hap
  have hb : p ∈ pn b := of_decide_eq_true hbp
  have hprefix₁ : u ++ [a] <+: t₁ := ⟨urest, by simp [htu]⟩
  have hprefix₂ : v ++ [b] <+: t₂ := ⟨vrest, by simp [htv]⟩
  obtain ⟨se₁, htr₁⟩ := ht₁
  obtain ⟨se₂, htr₂⟩ := ht₂
  rw [htu, ← List.singleton_append, ← List.append_assoc] at htr₁
  rw [htv, ← List.singleton_append, ← List.append_assoc] at htr₂
  obtain ⟨s₁, hu', _⟩ := htr₁.split
  obtain ⟨s₂, hv', _⟩ := htr₂.split
  obtain ⟨u', v', a', b', hu'', hv'', hm, hp⟩ :=
    smurf_first_matching h hpn₁ hu' hv' hu hv ha hb
  exact Or.inr (Or.inr
    ⟨p, u', v', a', b', hu''.trans hprefix₁, hv''.trans hprefix₂, hm, hp⟩)

end Cslib.Concurrency
