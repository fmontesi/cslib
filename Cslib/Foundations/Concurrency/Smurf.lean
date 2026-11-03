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
  symm: matching a b → matching b a

variable {State Label : Type*}

-- Defines a set of smurf LTSs.
structure Smurf (lts : LTS State Label) (I : Independence Label) (B : Branching Label) where
  -- labelling alphabet should be sane
  s : SaneAlphabet Label
  -- conditionals should come in matching sets
  m : ∀ s s₁ l₁, B.conditional l₁ ∧ lts.Tr s l₁ s₁ ↔
    ∃ l₂, B.matching l₁ l₂ ∧ ∃ s₂, lts.Tr s l₂ s₂
  -- no local concurrency
  -- pairs of outgoing transitions are either independent or part of a matching set
  u : ∀ s s₁ s₂ l₁ l₂, lts.Tr s l₁ s₁ ∧ lts.Tr s l₂ s₂ →
    I.independent l₁ l₂ ∨ B.matching l₁ l₂
  -- backward concurrency
  r : ∀ s s₁ l₁ l₂, I.independent l₁ l₂ ∧ lts.MTr s [l₁, l₂] s₁ →
    ∃ s₂, lts.Tr s l₂ s₂
  -- forward concurrency (diamond)
  f : ∀ s s₁ s₂ l₁ l₂, I.independent l₁ l₂ ∧ lts.Tr s l₁ s₁ ∧ lts.Tr s l₂ s₂ →
    ∃ s₃, lts.Tr s₁ l₂ s₃ ∧ lts.Tr s₂ l₁ s₃

variable {Pid : Type*} [DecidableEq Pid]

-- projection of an execution trace onto a process
def ProjectTrace {pn : Label → Finset Pid} (lst : List Label) (p : Pid) : List Label :=
  lst.filter (fun l => decide (p ∈ pn l))

-- in a Smurf LTS, a label l can commute past an unrelated trace t
private lemma smurf_commute_trace
  {pn : Label → Finset Pid}
  {lts : LTS State Label}
  {I : Independence Label}
  {B : Branching Label}
  (h : Smurf lts I B)
  (hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → (pn l₁) = (pn l₂))
  {s s₁ s₂ : State}
  {l₁ : Label}
  {u : List Label}
  {p : Pid}
  (hp : p ∈ pn l₁)
  (ht₁ : lts.Tr s l₁ s₁)
  (hu : lts.MTr s u s₂)
  (hproj : ProjectTrace (pn := pn) u p = []) :
  ∃ s₃, lts.MTr s₁ u s₃ ∧ lts.Tr s₂ l₁ s₃ := by
  induction hu generalizing s₁ l₁ with
  | refl => exact ⟨s₁, .refl, ht₁⟩
  | @stepL s a sm v se ha hv ih =>
      have hpa : p ∉ pn a := by
        intro hmem
        simp [ProjectTrace, hmem] at hproj
      have hvproj : ProjectTrace (pn := pn) v p = [] := by
        simpa [ProjectTrace, hpa] using hproj
      have hind : I.independent l₁ a := by
        rcases h.u s s₁ sm l₁ a ⟨ht₁, ha⟩ with hi | hm
        · exact hi
        · have heq := hpn₂ l₁ a hm
          exact False.elim (hpa (heq ▸ hp))
      obtain ⟨sx, hs₁x, hsmx⟩ :=
        h.f s s₁ sm l₁ a ⟨hind, ht₁, ha⟩
      obtain ⟨s₃, hxs₃, hes₃⟩ := ih (l₁ := l₁) (s₁ := sx) (hp := hp) (ht₁ := hsmx) (hproj := hvproj)
      exact ⟨s₃, .stepL hs₁x hxs₃, hes₃⟩


theorem ifSmurfThenTraces {pn : Label → Finset Pid} {lts : LTS State Label} {I : Independence Label} {B : Branching Label} {hpn₁ : ∀ l₁ l₂, I.independent l₁ l₂ → Disjoint (pn l₁) (pn l₂)} {hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → (pn l₁) = (pn l₂)} (h : Smurf lts I B) :
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
  intro s t₁ t₂ p
  induction hn : t₁.length + t₂.length using Nat.strong_induction_on generalizing s t₁ t₂ p with
  | _ n ih =>
    intro ⟨ht₁, ht₂⟩
    match t₁, t₂ with
    | [], [] =>
      -- both projections empty, so trivially prefixes of one another
      exact Or.inl (by simp [ProjectTrace])
    | [], l₂ :: t₂ =>
      -- l₁ projection empty, so trivially prefix of the other
      exact Or.inl (by simp [ProjectTrace])
    | l₁ :: t₁, [] =>
      -- l₂ projection empty, so trivially prefix of the other
      exact Or.inr (Or.inl (by simp [ProjectTrace]))
    | [l₁], [l₂] =>
      rw [Cslib.LTS.mem_traces_singleton_iff] at ht₁
      obtain ⟨s₁, htr₁⟩ := ht₁
      rw [Cslib.LTS.mem_traces_singleton_iff] at ht₂
      obtain ⟨s₂, htr₂⟩ := ht₂
      -- two singleton transitions from the initial state are either:
      rcases h.u s s₁ s₂ l₁ l₂ ⟨htr₁, htr₂⟩ with hind | hm
      · -- 1) independent, in which case the projections are disjoint and one of the two is empty;
        have hd : Disjoint (pn l₁) (pn l₂) := hpn₁ l₁ l₂ hind
        by_cases hp : p ∈ pn l₁
        · have hp₂ : p ∉ pn l₂ := fun hc => (Finset.disjoint_left.mp hd) hp hc
          exact Or.inr (Or.inl (by simp [ProjectTrace, hp, hp₂]))
        · exact Or.inl (by simp [ProjectTrace, hp])
      · -- or 2) matching
        exact Or.inr (Or.inr ⟨p, [], [], l₁, l₂, by simp, by simp, hm, by simp⟩)
    | [l₁], l₂ :: l₂' :: t₂' =>
      -- one singleton trace, one longer
      rw [Cslib.LTS.mem_traces_singleton_iff] at ht₁
      obtain ⟨s₁, htr₁⟩ := ht₁
      -- rewrite l₂ :: l₂' :: t₂' as u ++ [l]
      obtain ⟨u, l, hu⟩ := (List.eq_nil_or_concat (l₂ :: l₂' :: t₂')).resolve_left (by simp)
      rw [hu] at ht₂ ⊢
      simp only [List.concat_eq_append] at ht₂ ⊢

      -- u is also a trace of lts
      have htu : u ∈ lts.traces s := by
        obtain ⟨s₂, htr₂⟩ := ht₂
        obtain ⟨sm, hum, _⟩ := htr₂.split
        exact ⟨sm, hum⟩

      have hlt : [l₁].length + u.length < n := by
        rw [← hn]
        simp [hu]

      have hsingleton : [l₁] ∈ lts.traces s := by
        exact ⟨s₁, .stepL htr₁ .refl⟩

      have hres := ih
        ([l₁].length + u.length)
        hlt
        (s := s)
        (t₁ := [l₁])
        (t₂ := u)
        (p := p)
        rfl
        ⟨hsingleton, htu⟩

      -- apply the induction hypothesis to l₁ and u
      rcases hres with hprefix | hprefix | hdiv
      -- this gives one of three possible results:

      -- 1) ProjectTrace l₁ p <+: ProjectTrace u p
      --    then ProjectTrace l₁ p <+: ProjectTrace u p <+: ProjectTrace (u ++ [l]) p
      · apply Or.inl
        apply hprefix.trans
        rw [ProjectTrace, ProjectTrace, List.filter_append]
        exact List.prefix_append _ _

      -- 2) ProjectTrace u p <+: ProjectTrace l₁ p
      · by_cases hrev : ProjectTrace (pn := pn) [l₁] p <+: ProjectTrace (pn := pn) u p
        --    then, if also ProjectTrace l₁ p <+: ProjectTrace u p, refer to the previous case
        · apply Or.inl
          apply hrev.trans
          rw [ProjectTrace, ProjectTrace, List.filter_append]
          exact List.prefix_append _ _
        --    otherwise, ProjectTrace u p = [] and ProjectTrace l₁ p = l₁
        · have hp : p ∈ pn l₁ := by
            by_contra hnot
            have hempty : ProjectTrace (pn := pn) [l₁] p = [] := by
              simp [ProjectTrace, hnot]
            grind

          have hs : ProjectTrace (pn := pn) u p <+: [l₁] := by
            simpa [ProjectTrace, hp] using hprefix

          have huempty : ProjectTrace (pn := pn) u p = [] := by
            obtain ⟨suffix, heq⟩ := hs
            have hlen : (ProjectTrace (pn := pn) u p).length <= 1 := by
              have h := congrArg List.length heq
              simp at h
              omega
            cases hlist : ProjectTrace (pn := pn) u p with
            | nil => rfl
            | cons a as =>
                have has : as = [] := by
                  cases as with
                  | nil => rfl
                  | cons b bs => simp [hlist] at hlen
                subst as
                have he : [a] = [l₁] := by
                  cases suffix with
                  | nil => simpa [hlist] using heq
                  | cons b bs => simp [hlist] at heq
                exfalso
                apply hrev
                rw [hlist, he]
                simp [ProjectTrace, hp]

          obtain ⟨se, hfull⟩ := ht₂
          obtain ⟨sm, hum, hlast⟩ := hfull.split

          have hlast' : lts.Tr sm l se := by
            cases hlast with | stepL ha hb =>
              cases hb
              exact ha

          obtain ⟨sx, _, hcomm⟩ :=
            smurf_commute_trace h hpn₂ hp htr₁ hum huempty

          rcases h.u sm sx se l₁ l ⟨hcomm, hlast'⟩ with hind | hm
          · have hd := hpn₁ l₁ l hind
            have hpl : p ∉ pn l := by
              intro hmem
              exact (Finset.disjoint_left.mp hd) hp hmem
            apply Or.inr
            apply Or.inl
            have hempty : ProjectTrace (pn := pn) (u ++ [l]) p = [] := by
              simp only [ProjectTrace, List.filter_append]
              have huempty' : List.filter (fun a => decide (p ∈ pn a)) u = [] := by
                exact huempty
              rw [huempty']
              simp [hpl]
            rw [hempty]
            exact List.nil_prefix
          · apply Or.inr
            apply Or.inr
            refine ⟨p, [], u, l₁, l, ?_, ?_, hm, ?_⟩
            · simp
            · rfl
            · simpa [ProjectTrace] using huempty.symm

      --    it follows from hpn₂ that l₁ and the head of u are disjoint
      --    commute l₁ along u in the LTS repeatedly using the same argument
      --    apply the fourth base case to l₁ and l in the resulting state

      -- 3) l₁ and u have a point of divergence
      --    this witness is also valid for l₁ and (u ++ [l])
      · rcases hdiv with ⟨q, t₁', t₂', a₁, a₂, hp₁, hp₂, hm, heq⟩
        apply Or.inr
        apply Or.inr
        refine ⟨q, t₁', t₂', a₁, a₂, hp₁, ?_, hm, heq⟩
        exact hp₂.trans (List.prefix_append u [l])

    | l₁ :: l₁' :: t₁', [l₂] =>
      sorry
    | l₁ :: l₁' :: t₁', l₂ :: l₂' :: t₂' =>
      sorry

end Cslib.Concurrency
