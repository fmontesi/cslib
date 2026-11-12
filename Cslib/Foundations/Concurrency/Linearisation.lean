import Cslib.Foundations.Concurrency.Smurf

/-! Luc's playground
  With help from DeepSeek-V4.1-Flash-1017.
-/

namespace Cslib.Concurrency

variable {State Label : Type*} {B : Branching Label} {I : Label → Label → Prop}
         {Pid : Type*} [DecidableEq Pid]

-- lts is linear
def IsLinear (lts : LTS State Label) :=
  ∀ s μ₁ μ₂ s₁ s₂, (lts.Tr s μ₁ s₁ ∧ lts.Tr s μ₂ s₂) →
    ((μ₁ = μ₂ ∧ ¬ B.conditional μ₁) ∨ B.matching μ₁ μ₂)

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
  -- for any cycle in lts₁, any transition from the same state in lts₂ cannot be fully independent
  -- note: if μ ∈ μs, then this is covered by the irreflevity of I
  ∧ (∀ s μs, lts₁.MTr s μs s → (∀ μ s', lts₂.Tr (φ s) μ s' → (∃ μ' ∈ μs, ¬ I μ μ')))

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

-- if `Smurf` `lts₂` contains a trace `w`, then its linearisation `lts₁` contains a trace `v` s.t.
-- all symbols in `w` occur in equal or greater amounts in `v`; and
-- `w` is a conditional prefix of `v`
private lemma lin_copy_trace_condprefix
    [Independence I]
    [DecidableEq Label]
    [DecidablePred B.conditional]
    {pn : Label → Finset Pid}
    (lts₁ lts₂ : LTS State Label)
    (hsmurf : Smurf lts₂ I B)
    (s₁ s₂ : State)
    (φ : State → State)
  : IsLinearisation (B := B) (I := I) lts₁ lts₂ s₁ s₂ φ → ∀ w s₂', lts₂.MTr s₂ w s₂' →
      ∃ v s₁', (lts₁.MTr s₁ v s₁' ∧ s₂ = φ s₁ ∧
      -- CondPrefix (B := B) (pn := pn) w v ∧
        ∀ p, ProjectTrace (pn := pn) w p <+: ProjectTrace (pn := pn) v p)
  := by
    intro ⟨hlinear, hinit, hmap, hterm, hcycle⟩ w s₂' hw
    induction hn : w.length using Nat.strong_induction_on generalizing w s₂' with
    | _ n ih =>
      rcases List.eq_nil_or_concat w with rfl | ⟨w', x, heq⟩
      · -- if w is empty, then witness [], s₁
        refine ⟨[], s₁, ?_, ?_, ?_⟩
        · simp only [LTS.MTr.nil_iff]
        · grind only
        · intro p
          simp
      -- else, apply induction hypothesis on w' ++ x
      have ⟨sw', hsw'⟩ : ∃ sw', lts₂.MTr s₂ w' sw' := by
        sorry
      -- obtain matching trace v for w'
      obtain ⟨v, s₁', _, _, hpref⟩ := ih w'.length (by grind) w' sw' hsw' rfl
      sorry

end Helpers

-- if lts₁ is a linearisation of lts₂, then the traces of lts₁ are representative of those of lts₂
-- note: requires both LTSs to be finite-state
theorem linearisation_is_representative
    [Independence I]
    [Finite State]
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
