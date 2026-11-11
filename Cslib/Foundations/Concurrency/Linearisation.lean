import Cslib.Foundations.Concurrency.Smurf

/-! Luc's playground
  With help from DeepSeek-V4.1-Flash-1017.
-/

namespace Cslib.Concurrency

variable {State Label : Type*} {B : Branching Label} {I : Label → Label → Prop}

-- lts is linear
def IsLinear (lts : LTS State Label) :=
  ∀ s μ₁ μ₂ s₁ s₂, (lts.Tr s μ₁ s₁ ∧ lts.Tr s μ₂ s₂) →
    ((μ₁ = μ₂ ∧ ¬ B.conditional μ₁) ∨ B.matching μ₁ μ₂)

-- lts₁ is a linearisation of lts₂ through mapping φ
def IsLinearisation [Independence I]
    (lts₁ lts₂ : LTS State Label) (φ : State → State) :=
  -- lts₁ is linear
  IsLinear (B := B) lts₁
  -- correspondence between initial states? seems tricky with the current def
  -- of LTSs, so perhaps move to proofs (if actually needed)
  -- all lts₁ transitions can be mapped onto lts₂
  ∧ (∀ s μ s', lts₁.Tr s μ s' → lts₂.Tr (φ s) μ (φ s'))
  -- a state in lts₁ is only terminal if its mapping in lts₂ is
  ∧ (∀ s, lts₁.IsTerminal s → lts₂.IsTerminal (φ s))
  -- for any cycle in lts₁, any transition from the same state in lts₂ cannot be fully independent
  -- note: if μ ∈ μs, then this is covered by the irreflevity of I
  ∧ (∀ s μs, lts₁.MTr s μs s → (∀ μ s', lts₂.Tr (φ s) μ s' → (∃ μ' ∈ μs, ¬ I μ μ')))

section Helpers

-- any LTS lts₂ can simulate its linearisation lts₁
private lemma sim_linearisation
    [Independence I]
    (lts₁ lts₂ : LTS State Label)
    (φ : State → State)
  : IsLinearisation (B := B) (I := I) lts₁ lts₂ φ →
      (∀ s w s', lts₁.MTr s w s' → lts₂.MTr (φ s) w (φ s'))
  := by
    -- simple extension of the second conjunct of linearisation
    intro hlin s w s' hw
    induction w generalizing s s' with
    | nil =>
      simp
      have heq : s = s' := by
        simpa using hw
      grind only
    | cons a w ih =>
      obtain ⟨s'', htr, hmtr⟩ := LTS.MTr.cons_iff.mp hw
      exact LTS.MTr.stepL (hlin.2.1 s _ _ htr) (ih s'' s' hmtr)

end Helpers

-- if lts₁ is a linearisation of lts₂, then the traces of lts₁ are representative of those of lts₂
theorem linearisation_is_representative
    [Independence I]
    (lts₁ lts₂ : LTS State Label)
    (φ : State → State)
  : IsLinearisation (B := B) (I := I) lts₁ lts₂ φ →
    ∀ s, IsRepresentative I (lts₁.traces s) (lts₂.traces (φ s))
  := by
    intro ⟨hlinear, hmap, hterm, hcycle⟩ s
    simp only [IsRepresentative]
    intro w hw
    rw [LTS.mem_traces_iff] at hw
    obtain ⟨s', hs'⟩ := hw

    -- step 1: there exists a trace `u` in lts₁ that contains all labels in lts₂ (in quantity)
    -- lemma: if the trace in lts₂ can do a step, then lts₁ can do so after some number of independent steps
    -- lemma: extend the above to traces

    -- step 2: there exists a `v` s.t. `List.PermUpTo I (w ++ v) u`
    sorry

end Cslib.Concurrency
