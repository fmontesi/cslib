import Cslib.Foundations.Concurrency.Smurf

/-! Luc's playground
  With help from DeepSeek-V4.1-Flash-1017.
-/

namespace Cslib.Concurrency

variable {State Label : Type*} {B : Branching Label} {I : Label → Label → Prop}
  {Pid : Type*} [DecidableEq Pid]

-- lts is linear
def IsLinear (lts : LTS State Label) :=
  -- if transitions, either a non-conditional or a matching pair
  (∀ s μ₁ s₁, lts.Tr s μ₁ s₁ → (¬ B.conditional μ₁ ∨ (∃ μ₂ s₂, lts.Tr s μ₂ s₂ ∧ B.matching μ₁ μ₂)))
  -- only pairs are matching conditionals
  ∧ (∀ s μ₁ μ₂ s₁ s₂, (lts.Tr s μ₁ s₁ ∧ lts.Tr s μ₂ s₂ ∧ μ₁ ≠ μ₂) → B.matching μ₁ μ₂)

theorem isLinear_partner_unique {lts : LTS State Label} (hlin : IsLinear (B := B) lts) :
    ∀ s μ s', lts.Tr s μ s' → B.conditional μ →
      ∃ μ₂, B.matching μ μ₂ ∧ ∃ s₂, lts.Tr s μ₂ s₂
  := by
    intro s μ s' htr hcond
    -- linearity at a conditional transition yields a matching partner
    rcases hlin.1 s μ s' htr with hnc | ⟨μ₂, s₂, htr₂, hmatch⟩
    · exact absurd hcond hnc
    · exact ⟨μ₂, hmatch, s₂, htr₂⟩

theorem isLinear_unique_of_not_conditional {lts : LTS State Label} (hlin : IsLinear (B := B) lts) :
    ∀ s μ s' ν t, lts.Tr s μ s' → ¬ B.conditional μ → lts.Tr s ν t →
      ν = μ
  := by
    intro s μ s' ν t htr hnc htr'
    -- distinct labels enabled at a common state would have to match, hence be conditional
    by_contra hne
    exact hnc (B.matchcond μ ν (hlin.2 s μ ν s' t ⟨htr, htr', fun h => hne h.symm⟩)).1

-- lts₁ is a linearisation of lts₂ from states s₁/s₂ through mapping φ
def IsLinearisation [Independence I]
    (lts₁ lts₂ : LTS State Label) (s₁ s₂ : State) (φ : State → State) :=
  -- lts₁ is linear
  IsLinear (B := B) lts₁
  -- TODO: if lts₂ finite then lts₁ also finite?
  -- there exists a corresponding state for s₂ in lts₁
  ∧ φ s₁ = s₂
  -- all lts₁ transitions can be mapped onto lts₂
  ∧ (∀ s μ s', lts₁.Tr s μ s' → lts₂.Tr (φ s) μ (φ s'))
  -- a state in lts₁ is only terminal if its mapping in lts₂ is
  ∧ (∀ s, lts₁.IsTerminal s → lts₂.IsTerminal (φ s))
  -- for any non-empty cycle in lts₁, any transition from the same state in lts₂ cannot be
  -- fully independent
  -- note: the cycle must be non-empty, otherwise the quantifier below is unsatisfiable
  -- (every state reaches itself with the empty trace); if μ ∈ μs, then this is covered by
  -- the irreflexivity of I
  ∧ (∀ s μs, μs ≠ [] → lts₁.MTr s μs s →
      (∀ μ s', lts₂.Tr (φ s) μ s' → (∃ μ' ∈ μs, ¬ I μ μ')))

section Helpers

-- any LTS lts₂ can simulate its linearisation lts₁
private lemma orig_sim_lin
    [Independence I]
    (lts₁ lts₂ : LTS State Label)
    (s₁ s₂ : State)
    (φ : State → State)
  : IsLinearisation (B := B) (I := I) lts₁ lts₂ s₁ s₂ φ →
      (∀ w s₁', lts₁.MTr s₁ w s₁' → lts₂.MTr s₂ w (φ s₁'))
  := by
    -- simple extension of the mapping conjunct of linearisation
    intro ⟨hlinear, hinit, hmap, hterm, hcycle⟩
    -- if `lts₁` can take `w` from `s` to `s'`, so can `lts₂` from `φ s` to `φ s'`
    have key : ∀ (s : State) (w : List Label) (s' : State),
        lts₁.MTr s w s' → lts₂.MTr (φ s) w (φ s') := by
      intro s w s' hw
      induction w generalizing s s' with
      | nil =>
        rw [LTS.MTr.nil_eq lts₁ hw]
        exact LTS.MTr.refl
      | cons a w ih =>
        obtain ⟨s'', htr, hmtr⟩ := LTS.MTr.cons_iff.mp hw
        exact LTS.MTr.stepL (hmap s a s'' htr) (ih s'' s' hmtr)
    intro w s₁' hw
    rw [← hinit]
    exact key s₁ w s₁' hw

-- trace `v` is a `conditional prefix` of `w` if, for every process `p`,
-- `w` contains the same conditionals in the same order
-- def CondPrefix {pn : Label → Finset Pid} [DecidablePred B.conditional]
--     (v w : List Label) : Prop :=
--   ∀ (p : Pid), ∃ (w' : List Label), w' <+: w ∧
--     v.filter (fun l => decide (p ∈ pn l ∧ B.conditional l)) =
--       w'.filter (fun l => decide (p ∈ pn l ∧ B.conditional l))

-- `List.PermUpTo I`-equivalent traces have the same projection onto any process,
-- since independent labels are observed by disjoint sets of processes
private lemma permupto_projectTrace
    [Independence I]
    {pn : Label → Finset Pid}
    (hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂))
    {t₁ t₂ : List Label} (p : Pid) (hp : List.PermUpTo I t₁ t₂) :
    ProjectTrace (pn := pn) t₁ p = ProjectTrace (pn := pn) t₂ p := by
  induction hp with
  | nil => rfl
  | cons a _ ih =>
    simp only [ProjectTrace, List.filter_cons] at ih ⊢
    rw [ih]
  | swap a b w₀ hind =>
    have hind' : I a b :=
      hind.elim id fun h => Std.Symm.symm (r := I) (a := b) (b := a) h
    simp only [ProjectTrace, List.filter_cons]
    by_cases ha : p ∈ pn a
    · have hb : p ∉ pn b :=
        fun hb => Finset.disjoint_left.mp (hpn₁ a b hind') ha hb
      simp [ha, hb]
    · by_cases hb : p ∈ pn b <;> simp [ha, hb]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

-- if `Smurf` `lts₂` contains a trace `w`, then its linearisation `lts₁` contains a trace `v` s.t.
-- `List.PermUpTo I (w ++ u) v` for some `u`
-- which should imply that `w` is a prefix of `v` when projected on any `p`
private lemma lin_copy_trace
    [Independence I]
    [DecidableEq Label]
    [DecidablePred B.conditional]
    {pn : Label → Finset Pid}
    {hpn₀ : ∀ l, (pn l).Nonempty}
    {hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂)}
    {hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → (pn l₁) = (pn l₂)}
    (lts₁ lts₂ : LTS State Label)
    (hsmurf : Smurf lts₂ I B)
    (s₁ s₂ : State)
    (φ : State → State)
  : IsLinearisation (B := B) (I := I) lts₁ lts₂ s₁ s₂ φ → ∀ w s₂', lts₂.MTr s₂ w s₂' →
      ∃ v s₁', (lts₁.MTr s₁ v s₁' ∧ s₂ = φ s₁
      -- CondPrefix (B := B) (pn := pn) w v ∧
        -- ∧ (∀ p, ProjectTrace (pn := pn) w p <+: ProjectTrace (pn := pn) v p)
        ∧ ∃ u, List.PermUpTo I (w ++ u) v)
  := by
    intro ⟨hlinear, hinit, hmap, hterm, hcycle⟩ w s₂' hw
    induction hn : w.length using Nat.strong_induction_on generalizing w s₂' with
    | _ n ih =>
      rcases List.eq_nil_or_concat w with rfl | ⟨w', x, heq⟩
      · -- if w is empty, then witness [], s₁
        refine ⟨[], s₁, ?_, ?_, ?_⟩
        · simp only [LTS.MTr.nil_iff]
        · grind only
        -- · intro p
          -- simp only [List.prefix_rfl]
        · exists []
          simp
          grind only [List.PermUpTo.nil, List.PermUpTo]
      -- else, apply induction hypothesis on w' ++ x
      have ⟨sw', hsw'⟩ : ∃ sw', lts₂.MTr s₂ w' sw' := by
        have hwx : lts₂.MTr s₂ (w' ++ [x]) s₂' := by
          rw [← List.concat_eq_append, ← heq]
          exact hw
        obtain ⟨sw', hsw', _⟩ := LTS.MTr.split hwx
        exact ⟨sw', hsw'⟩
      -- obtain matching trace v for w'
      obtain ⟨v, s₁', hv₁, _, hperm⟩ := ih w'.length (by grind) w' sw' hsw' rfl
      have hpref : ∀ p, ProjectTrace (pn := pn) w' p <+: ProjectTrace (pn := pn) v p := by
        intro p
        obtain ⟨u, hu⟩ := hperm
        have hprefix : ProjectTrace (pn := pn) w' p <+:
            ProjectTrace (pn := pn) (w' ++ u) p := by
          simp only [ProjectTrace, List.filter_append]
          exact List.prefix_append _ _
        rw [permupto_projectTrace hpn₁ p hu] at hprefix
        exact hprefix
      -- experimental
      -- `lts₂` also has a trace `v`
      obtain hv₂ := orig_sim_lin (B := B) (I := I) lts₁ lts₂ s₁ s₂ φ (by sorry) v s₁' hv₁
      -- then `lts₂` has traces `v` and `w' ++ [x]`, and `if_smurf_then_traces` applies
      have htraces₂ : v ∈ lts₂.traces s₂ ∧ (w' ++ [x]) ∈ lts₂.traces s₂ := by
        sorry
      -- apply `if_smurf_then_traces` to traces `v` and `w' ++ [x]`, in `lts₂` from state `s₂`
      sorry

end Helpers

-- if lts₁ is a linearisation of lts₂, then the traces of lts₁ are representative of those of lts₂
-- note: requires both LTSs to be finite-state
theorem linearisation_is_representative
    [Independence I]
    [Finite State]
    {pn : Label → Finset Pid}
    {hpn₀ : ∀ l, (pn l).Nonempty}
    {hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂)}
    {hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → (pn l₁) = (pn l₂)}
    (lts₁ lts₂ : LTS State Label)
    (hsmurf : Smurf lts₂ I B)
    (s₁ s₂ : State)
    (φ : State → State)
  : IsLinearisation (B := B) (I := I) lts₁ lts₂ s₁ s₂ φ →
    IsRepresentative I (lts₁.traces s₁) (lts₂.traces s₂)
  := by
    intro ⟨hlinear, hinit, hmap, hterm, hcycle⟩
    simp only [IsRepresentative]
    intro w hw
    rw [LTS.mem_traces_iff] at hw
    obtain ⟨s', hs'⟩ := hw

    -- step 1: there exists a trace `u` in lts₁ that contains all labels in lts₂ (in quantity)
    -- lemma: if lts₂ can do a step, then lts₁ can do this after a finite number of independent steps
    -- lemma: extend the above to traces

    -- step 2: there exists a `v` s.t. `List.PermUpTo I (w ++ v) u`
    sorry

end Cslib.Concurrency
