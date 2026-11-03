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
  [irrefl : Std.Irrefl matching]

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
  -- distinct pairs of outgoing transitions are either independent or part of a matching set
  u : ∀ s s₁ s₂ l₁ l₂, l₁ ≠ l₂ → lts.Tr s l₁ s₁ ∧ lts.Tr s l₂ s₂ →
    I l₁ l₂ ∨ B.matching l₁ l₂
  -- backward concurrency
  r : ∀ s s₁ l₁ l₂, I l₁ l₂ ∧ lts.MTr s [l₁, l₂] s₁ →
    ∃ s₂, lts.Tr s l₂ s₂
  -- forward concurrency (diamond)
  f : ∀ s s₁ s₂ l₁ l₂, I l₁ l₂ ∧ lts.Tr s l₁ s₁ ∧ lts.Tr s l₂ s₂ →
    ∃ s₃, lts.Tr s₁ l₂ s₃ ∧ lts.Tr s₂ l₁ s₃
  -- the LTS is deterministic
  d : ∀ s s₁ s₂ l, lts.Tr s l s₁ → lts.Tr s l s₂ → s₁ = s₂

variable {Pid : Type*} [DecidableEq Pid]

-- projection of an execution trace onto a process
def ProjectTrace {pn : Label → Finset Pid} (lst : List Label) (p : Pid) : List Label :=
  lst.filter (fun l => decide (p ∈ pn l))

section Helpers

variable {pn : Label → Finset Pid} {lts : LTS State Label}
  {I : Label → Label → Prop} [Independence I] {B : Branching Label}
  {hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂)}
  {hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → pn l₁ = pn l₂}

/-- If `p` does not observe any label of `u`, then `u` projects to the empty trace. -/
private lemma projectTrace_eq_nil {u : List Label} {p : Pid}
    (h : ∀ l ∈ u, p ∉ pn l) : ProjectTrace (pn := pn) u p = [] := by
  induction u with
  | nil => rfl
  | cons a t ih =>
    have ha : p ∉ pn a := h a (by simp)
    have ht : ProjectTrace (pn := pn) t p = [] :=
      ih (fun l hl => h l (by simp [hl]))
    rw [ProjectTrace, List.filter_cons, decide_eq_false ha]
    exact ht

/-- An enabled action either matches a label of an unobserved trace, or commutes
past all of it. The caller supplies `hne : ∀ b, a = b → False` because
irreflexivity of `matching` rules out the degenerate `matching a a` witness. -/
private lemma commute_or_matching
    (h : Smurf lts I B) {s s₁ s₂ : State} {a : Label} {u : List Label} {p : Pid}
    (ha : lts.Tr s a s₁) (hu : lts.MTr s u s₂)
    (hne : ∀ b, a = b → False) (hproj : ProjectTrace (pn := pn) u p = []) :
    (∃ v b, v ++ [b] <+: u ∧ B.matching a b) ∨
      ∃ s₃, lts.MTr s₁ u s₃ ∧ lts.Tr s₂ a s₃ := by
  induction hu generalizing s₁ with
  | refl => exact Or.inr ⟨s₁, .refl, ha⟩
  | @stepL s b sm v se hb hv ih =>
    have hpb : p ∉ pn b := by
      intro hp
      simp [ProjectTrace, hp] at hproj
    have hvproj : ProjectTrace (pn := pn) v p = [] := by
      simpa [ProjectTrace, hpb] using hproj
    have hne' : a ≠ b := hne b
    rcases h.u s s₁ sm a b hne' ⟨ha, hb⟩ with hind | hm
    · obtain ⟨sx, hs₁x, hsmx⟩ := h.f s s₁ sm a b ⟨hind, ha, hb⟩
      rcases ih hsmx hvproj with ⟨w, c, hw, hm⟩ | ⟨s₃, hx₃, he₃⟩
      · refine Or.inl ⟨b :: w, c, ?_, hm⟩
        obtain ⟨suffix, hsuffix⟩ := hw
        exact ⟨suffix, congrArg (b :: ·) hsuffix⟩
      · exact Or.inr ⟨s₃, .stepL hs₁x hx₃, he₃⟩
    · exact Or.inl ⟨[], b, ⟨v, rfl⟩, hm⟩

/-- The projection of `t ++ [l]` when `p` does not observe `l`. -/
private lemma projectTrace_concat_notMem (t : List Label) (l : Label) (p : Pid)
    (h : p ∉ pn l) :
    ProjectTrace (pn := pn) (t ++ [l]) p = ProjectTrace (pn := pn) t p := by
  unfold ProjectTrace
  rw [List.filter_append, List.filter_cons, List.filter_nil, decide_eq_false h]
  simp

/-- The projection of `t ++ [l]` when `p` observes `l`. -/
private lemma projectTrace_concat_mem (t : List Label) (l : Label) (p : Pid)
    (h : p ∈ pn l) :
    ProjectTrace (pn := pn) (t ++ [l]) p = ProjectTrace (pn := pn) t p ++ [l] := by
  unfold ProjectTrace
  rw [List.filter_append, List.filter_cons, List.filter_nil, decide_eq_true h]
  simp


/-- Split a trace at its last step; the prefix still starts at the original state. -/
private lemma mtr_split_last {s s' : State} {l : List Label} {a : Label}
    (h : lts.MTr s (l ++ [a]) s') : ∃ sm, lts.MTr s l sm ∧ lts.Tr sm a s' := by
  obtain ⟨sm, h1, h2⟩ := LTS.MTr.split h
  exact ⟨sm, h1, LTS.MTr.single_invert lts _ _ _ h2⟩

/-- Cancel a common prefix on the left of a prefix relation. -/
private lemma prefix_cancel_left {C X Y : List Label} (h : C ++ X <+: C ++ Y) :
    X <+: Y := by
  obtain ⟨W, hW⟩ := h
  rw [List.append_assoc] at hW
  exact ⟨W, List.append_cancel_left hW⟩

/-- A nonempty list that is a prefix of a singleton is that singleton. -/
private lemma eq_of_prefix_singleton {R : List Label} {x : Label}
    (hne : R ≠ []) (h : R <+: [x]) : R = [x] := by
  obtain ⟨W, hW⟩ := h
  have hlen : R.length + W.length = 1 := by
    simpa using congrArg List.length hW
  have hR1 : R.length = 1 := by
    cases R with
    | nil => exact absurd rfl hne
    | cons r R' =>
      cases R' with
      | nil => simp
      | cons r' R'' => simp at hlen; omega
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp hR1
  have hWnil : W = [] := by
    cases W with
    | nil => rfl
    | cons w W' => simp at hlen; omega
  subst hy
  have h2 : [y] ++ W = [x] := by simpa using hW
  rw [hWnil, List.append_nil] at h2
  simpa using h2

/-- The projection on `p` is monotone under appending a single label. -/
private lemma projectTrace_prefix_concat (t : List Label) (l : Label) (p : Pid) :
    ProjectTrace (pn := pn) t p <+: ProjectTrace (pn := pn) (t ++ [l]) p := by
  by_cases hl : p ∈ pn l
  · rw [projectTrace_concat_mem t l p hl]
    exact List.prefix_append _ _
  · rw [projectTrace_concat_notMem t l p hl]

/-- Branching case: two traces with equal projections that end in distinct
labels observed by `p`.  When the traces diverge, the only axiom that can apply to
the two distinct enabled labels is that they are a matching pair, so there must be
a matching witness at aligned prefixes.

This is the point where the two executions genuinely branch; proving it requires
aligning the two executions step by step (commuting independent labels with
`Smurf.f` and using `Smurf.u` at every state where two distinct labels are both
enabled). -/
private lemma core_branch {s u₁ u₂ s₁ s₂ : State} {t₁' t₂' : List Label}
    {l₁ l₂ : Label} {p : Pid}
    (h : Smurf lts I B)
    (hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂))
    (hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → pn l₁ = pn l₂)
    (ht₁' : lts.MTr s t₁' u₁) (ht₂' : lts.MTr s t₂' u₂)
    (hlast₁ : lts.Tr u₁ l₁ s₁) (hlast₂ : lts.Tr u₂ l₂ s₂)
    (hEq : ProjectTrace (pn := pn) t₁' p = ProjectTrace (pn := pn) t₂' p)
    (hl₁ : p ∈ pn l₁) (hl₂ : p ∈ pn l₂) (hll : l₁ ≠ l₂) :
    ∃ (q : Pid) (x₁ x₂ : List Label) (m₁ m₂ : Label),
      x₁ ++ [m₁] <+: t₁' ++ [l₁] ∧ x₂ ++ [m₂] <+: t₂' ++ [l₂] ∧
      B.matching m₁ m₂ ∧
        ProjectTrace (pn := pn) x₁ q = ProjectTrace (pn := pn) x₂ q := by
  sorry

/-- Two traces out of the same state satisfy the trichotomy.

The induction splits both traces at their **last** label (`t = t' ++ [l]`), not at
their head. This keeps both prefixes `t₁'` and `t₂'` anchored at the same state `s`,
so the induction hypothesis applies directly to them.

If the prefix projections differ, the induction hypothesis is applied to the
smaller pair `(t₁, t₂')` (resp. `(t₁', t₂)`): the extra observed label has to be
the last element of the difference, which yields a prefix relation.  Only the case
of equal prefix projections with distinct observed final labels remains; it is the
branching point of the two traces. -/
private lemma core {s : State} {t₁ t₂ : List Label} {p : Pid}
    (h : Smurf lts I B)
    (hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂))
    (hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → pn l₁ = pn l₂)
    {s₁ s₂ : State} (ht₁ : lts.MTr s t₁ s₁) (ht₂ : lts.MTr s t₂ s₂) :
    ProjectTrace (pn := pn) t₁ p <+: ProjectTrace (pn := pn) t₂ p ∨
    ProjectTrace (pn := pn) t₂ p <+: ProjectTrace (pn := pn) t₁ p ∨
    (∃ (q : Pid) (t₁' t₂' : List Label) (l₁ l₂ : Label),
        t₁' ++ [l₁] <+: t₁ ∧ t₂' ++ [l₂] <+: t₂ ∧ B.matching l₁ l₂ ∧
        ProjectTrace (pn := pn) t₁' q = ProjectTrace (pn := pn) t₂' q) := by
  classical
  induction hn : t₁.length + t₂.length using Nat.strong_induction_on generalizing
      s t₁ t₂ s₁ s₂ with
  | _ n ihp =>
    -- Handle the trivial cases first.
    rcases List.eq_nil_or_concat t₁ with rfl | ⟨t₁', l₁, rfl⟩
    · exact Or.inl (by simp [ProjectTrace])
    · rcases List.eq_nil_or_concat t₂ with rfl | ⟨t₂', l₂, rfl⟩
      · exact Or.inr (Or.inl (by simp [ProjectTrace]))
      · -- both traces are nonempty: split the last step off each
        obtain ⟨u₁, ht₁', hlast₁⟩ := mtr_split_last
          (l := t₁') (a := l₁) (by simpa using ht₁)
        obtain ⟨u₂, ht₂', hlast₂⟩ := mtr_split_last
          (l := t₂') (a := l₂) (by simpa using ht₂)
        simp only [List.concat_eq_append] at ht₁ ht₂ hn ⊢
        -- induction hypothesis on the prefixes, both still starting at `s`
        have hlen : t₁'.length + t₂'.length < n := by
          simp only [List.length_append, List.length_singleton] at hn ⊢
          omega
        rcases ihp (t₁'.length + t₂'.length) hlen
          (s := s) (s₁ := u₁) (s₂ := u₂) ht₁' ht₂' rfl with h1 | h2 | h3
        · -- `ProjectTrace t₁' p <+: ProjectTrace t₂' p`
          by_cases hEq : ProjectTrace (pn := pn) t₁' p
              = ProjectTrace (pn := pn) t₂' p
          · -- Equal prefix projections: the final labels decide.
            by_cases hl₁ : p ∈ pn l₁
            · by_cases hl₂ : p ∈ pn l₂
              · by_cases hll : l₁ = l₂
                · subst hll
                  refine Or.inl ?_
                  rw [projectTrace_concat_mem t₁' l₁ p hl₁,
                    projectTrace_concat_mem t₂' l₁ p hl₂, hEq]
                · exact Or.inr (Or.inr (core_branch h hpn₁ hpn₂ ht₁' ht₂'
                    hlast₁ hlast₂ hEq hl₁ hl₂ hll))
              · refine Or.inr (Or.inl ?_)
                rw [projectTrace_concat_mem t₁' l₁ p hl₁,
                  projectTrace_concat_notMem t₂' l₂ p hl₂, hEq]
                exact List.prefix_append _ _
            · refine Or.inl ?_
              by_cases hl₂ : p ∈ pn l₂
              · rw [projectTrace_concat_notMem t₁' l₁ p hl₁,
                  projectTrace_concat_mem t₂' l₂ p hl₂, hEq]
                exact List.prefix_append _ _
              · rw [projectTrace_concat_notMem t₁' l₁ p hl₁,
                  projectTrace_concat_notMem t₂' l₂ p hl₂, hEq]
          · -- `P(t₂')` properly extends `P(t₁')`: compare `t₁` with `t₂'`.
            obtain ⟨R, hR⟩ := h1
            have hRne : R ≠ [] := by
              intro h0
              exact hEq (by rw [← hR, h0, List.append_nil])
            have hlt : (t₁' ++ [l₁]).length + t₂'.length < n := by
              simp only [List.length_append, List.length_singleton] at hn ⊢
              omega
            rcases ihp ((t₁' ++ [l₁]).length + t₂'.length) hlt
              (s := s) (s₁ := s₁) (s₂ := u₂) ht₁ ht₂' rfl
              with hres | hres | hres
            · exact Or.inl (hres.trans (projectTrace_prefix_concat t₂' l₂ p))
            · -- `P(t₂') <+: P(t₁)`: then `R = [l₁]`.
              by_cases hl₁ : p ∈ pn l₁
              · rw [projectTrace_concat_mem t₁' l₁ p hl₁] at hres
                rw [← hR] at hres
                have hRle : R <+: [l₁] := prefix_cancel_left hres
                have hReq : R = [l₁] := eq_of_prefix_singleton hRne hRle
                refine Or.inl ?_
                rw [projectTrace_concat_mem t₁' l₁ p hl₁]
                by_cases hl₂ : p ∈ pn l₂
                · rw [projectTrace_concat_mem t₂' l₂ p hl₂, ← hR, hReq]
                  exact List.prefix_append _ _
                · rw [projectTrace_concat_notMem t₂' l₂ p hl₂, ← hR, hReq]
              · rw [projectTrace_concat_notMem t₁' l₁ p hl₁] at hres
                have hE : ProjectTrace (pn := pn) t₁' p
                    = ProjectTrace (pn := pn) t₂' p :=
                  List.IsPrefix.eq_of_length ⟨R, hR⟩ (by
                    have h1len := List.IsPrefix.length_le
                      (⟨R, hR⟩ :
                        ProjectTrace (pn := pn) t₁' p <+: ProjectTrace (pn := pn) t₂' p)
                    have h2len := hres.length_le
                    omega)
                refine Or.inl ?_
                rw [projectTrace_concat_notMem t₁' l₁ p hl₁]
                by_cases hl₂ : p ∈ pn l₂
                · rw [projectTrace_concat_mem t₂' l₂ p hl₂, ← hE]
                  exact List.prefix_append _ _
                · rw [projectTrace_concat_notMem t₂' l₂ p hl₂, ← hE]
            · -- the witness already works for the full traces
              obtain ⟨q, x₁, x₂, m₁, m₂, hx₁, hx₂, hm, hproj⟩ := hres
              refine Or.inr (Or.inr ⟨q, x₁, x₂, m₁, m₂, hx₁, ?_, hm, hproj⟩)
              exact hx₂.trans (List.prefix_append t₂' [l₂])
        · -- `ProjectTrace t₂' p <+: ProjectTrace t₁' p` (symmetric)
          by_cases hEq : ProjectTrace (pn := pn) t₁' p
              = ProjectTrace (pn := pn) t₂' p
          · -- Equal prefix projections: the final labels decide.
            by_cases hl₁ : p ∈ pn l₁
            · by_cases hl₂ : p ∈ pn l₂
              · by_cases hll : l₁ = l₂
                · subst hll
                  refine Or.inl ?_
                  rw [projectTrace_concat_mem t₁' l₁ p hl₁,
                    projectTrace_concat_mem t₂' l₁ p hl₂, hEq]
                · exact Or.inr (Or.inr (core_branch h hpn₁ hpn₂ ht₁' ht₂'
                    hlast₁ hlast₂ hEq hl₁ hl₂ hll))
              · refine Or.inr (Or.inl ?_)
                rw [projectTrace_concat_mem t₁' l₁ p hl₁,
                  projectTrace_concat_notMem t₂' l₂ p hl₂, hEq]
                exact List.prefix_append _ _
            · refine Or.inl ?_
              by_cases hl₂ : p ∈ pn l₂
              · rw [projectTrace_concat_notMem t₁' l₁ p hl₁,
                  projectTrace_concat_mem t₂' l₂ p hl₂, hEq]
                exact List.prefix_append _ _
              · rw [projectTrace_concat_notMem t₁' l₁ p hl₁,
                  projectTrace_concat_notMem t₂' l₂ p hl₂, hEq]
          · -- `P(t₁')` properly extends `P(t₂')`: compare `t₁'` with `t₂`.
            obtain ⟨R, hR⟩ := h2
            have hRne : R ≠ [] := by
              intro h0
              exact hEq (by rw [← hR, h0, List.append_nil])
            have hlt : t₁'.length + (t₂' ++ [l₂]).length < n := by
              simp only [List.length_append, List.length_singleton] at hn ⊢
              omega
            rcases ihp (t₁'.length + (t₂' ++ [l₂]).length) hlt
              (s := s) (s₁ := u₁) (s₂ := s₂) ht₁' ht₂ rfl
              with hres | hres | hres
            · -- `P(t₁') <+: P(t₂)`: then `R = [l₂]`.
              by_cases hl₂ : p ∈ pn l₂
              · rw [projectTrace_concat_mem t₂' l₂ p hl₂] at hres
                rw [← hR] at hres
                have hRle : R <+: [l₂] := prefix_cancel_left hres
                have hReq : R = [l₂] := eq_of_prefix_singleton hRne hRle
                refine Or.inr (Or.inl ?_)
                rw [projectTrace_concat_mem t₂' l₂ p hl₂]
                by_cases hl₁ : p ∈ pn l₁
                · rw [projectTrace_concat_mem t₁' l₁ p hl₁, ← hR, hReq]
                  exact List.prefix_append _ _
                · rw [projectTrace_concat_notMem t₁' l₁ p hl₁, ← hR, hReq]
              · rw [projectTrace_concat_notMem t₂' l₂ p hl₂] at hres
                rw [← hR] at hres
                exfalso
                exact hRne (List.eq_nil_of_prefix_nil (prefix_cancel_left (by simpa using hres)))
            · -- `P(t₂) <+: P(t₁')`, hence also a prefix of `P(t₁)`
              refine Or.inr (Or.inl (hres.trans ?_))
              by_cases hl₁ : p ∈ pn l₁
              · rw [projectTrace_concat_mem t₁' l₁ p hl₁]
                exact List.prefix_append _ _
              · rw [projectTrace_concat_notMem t₁' l₁ p hl₁]
            · -- the witness already works for the full traces
              obtain ⟨q, x₁, x₂, m₁, m₂, hx₁, hx₂, hm, hproj⟩ := hres
              refine Or.inr (Or.inr ⟨q, x₁, x₂, m₁, m₂,
                hx₁.trans (List.prefix_append t₁' [l₁]), hx₂, hm, hproj⟩)
        · -- the witness already works for the full traces
          obtain ⟨q, x₁, x₂, m₁, m₂, hx₁, hx₂, hm, hproj⟩ := h3
          exact Or.inr (Or.inr ⟨q, x₁, x₂, m₁, m₂,
            hx₁.trans (List.prefix_append t₁' [l₁]),
            hx₂.trans (List.prefix_append t₂' [l₂]), hm, hproj⟩)

omit [DecidableEq Pid] in
/-- Two distinct labels enabled at the same state and both observed by `p` must be a
matching pair: independence would force disjoint process sets, yet both contain `p`. -/
private theorem obs_match
    (h : Smurf lts I B) (hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂))
    {s s₁ s₂ : State} {a b : Label} (hab : a ≠ b)
    (ha : p ∈ pn a) (hb : p ∈ pn b)
    (hta : lts.Tr s a s₁) (htb : lts.Tr s b s₂) : B.matching a b := by
  rcases h.u s s₁ s₂ a b hab ⟨hta, htb⟩ with hind | hm
  · exact absurd hb (Finset.disjoint_left.mp (hpn₁ a b hind) ha)
  · exact hm

/-- In a deterministic LTS the end state of a trace is determined by its labels. -/
private lemma mtr_det (hd : ∀ s s₁ s₂ l, lts.Tr s l s₁ → lts.Tr s l s₂ → s₁ = s₂)
    {s s₁ s₂ : State} {u : List Label} (h1 : lts.MTr s u s₁) (h2 : lts.MTr s u s₂) :
    s₁ = s₂ := by
  induction u generalizing s with
  | nil => exact (LTS.MTr.nil_eq lts h1).symm.trans (LTS.MTr.nil_eq lts h2)
  | cons a t ih =>
    obtain ⟨sa1, hta1, ht1⟩ := LTS.MTr.cons_iff.mp h1
    obtain ⟨sa2, hta2, ht2⟩ := LTS.MTr.cons_iff.mp h2
    rw [hd s sa1 sa2 a hta1 hta2] at ht1
    exact ih ht1 ht2

end Helpers

theorem ifSmurfThenTraces {pn : Label → Finset Pid} {lts : LTS State Label}
    {I : Label → Label → Prop} [Independence I] {B : Branching Label}
    {hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂)}
    {hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → (pn l₁) = (pn l₂)}
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
  -- See scripts/SmurfProofSketch.md for the full proof sketch.
  intro s t₁ t₂ p ht
  obtain ⟨h₁, h₂⟩ := ht
  obtain ⟨s₁, hm₁⟩ := h₁
  obtain ⟨s₂, hm₂⟩ := h₂
  exact core h hpn₁ hpn₂ hm₁ hm₂

end Cslib.Concurrency
