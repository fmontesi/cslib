/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Mathlib.Basic.Finite.Sum
public import Cslib.Foundations.Data.Fin.Tuple

/-!
# Concatenating the outputs of two machines on the same input

`concatenate tm₁ tm₂` runs the machines on disjoint groups of work tapes, rewinding the input
between them. The second machine starts on its own fresh, blank work tapes and appends to the
first machine's output. Neither machine needs to clear its tapes or reset its heads before halting.
-/

public section

namespace Turing.MultiTapeTM

variable {k₁ k₂ : ℕ} {Symbol State₁ State₂ : Type*}

/-- Run two machines on the same input, concatenating their outputs and using disjoint
work tapes. -/
noncomputable def concatenate (tm₁ : MultiTapeTM k₁ Symbol State₁)
    (tm₂ : MultiTapeTM k₂ Symbol State₂) :
    MultiTapeTM (k₁ + k₂) Symbol ((State₁ ⊕ RewindState) ⊕ State₂) :=
  ((tm₁.extendTapes (Fin.castAddEmb k₂)).seq
    ((rewindInput Symbol).extendTapes (noTapes (k₁ + k₂)))).seq
      (tm₂.extendTapes (Fin.natAddEmb k₁))

namespace Concatenate

variable {input : List Symbol}

/-- First phase: the first machine runs on the first `k₁` tapes, the other tapes stay blank. -/
private theorem first_phase {tm : MultiTapeTM k₁ Symbol State₁} {p : tm.RunPath input}
    (hh : p.head = tm.initCfg input) :
    ∃ q : (tm.extendTapes (Fin.castAddEmb k₂)).RunPath input,
      q.head = (tm.extendTapes (Fin.castAddEmb k₂)).initCfg input ∧
      q.last = embed (Fin.castAddEmb k₂) p.last (fun _ _ => none) (fun _ => 0) ∧
      q.length = p.length ∧ q.space ≤ p.space + k₂ := by
  simpa [Cfg.prependOutput] using exists_runPath_extendTapes (Fin.castAddEmb k₂) hh []
    (tapes := fun _ _ => none) (heads := fun _ => 0) (fun _ => rfl) fun _ => rfl

/-- Third phase: the second machine runs on the last `k₂` tapes, which the first phase left blank,
and appends to the output `c.output` of the first phase. -/
private theorem third_phase {tm : MultiTapeTM k₂ Symbol State₂} {p : tm.RunPath input}
    (hh : p.head = tm.initCfg input) (c : Cfg k₁ Symbol State₁ input) :
    let c' := embed (Fin.castAddEmb k₂) c (fun _ _ => none) (fun _ => 0)
    ∃ q : (tm.extendTapes (Fin.natAddEmb k₁)).RunPath input,
      q.head = ⟨some tm.q₀, 1, c'.workTapes, c'.workTapePos, c.output⟩ ∧
      q.last =
        embed (Fin.natAddEmb k₁) (p.last.prependOutput c.output) c'.workTapes c'.workTapePos ∧
      q.length = p.length ∧ q.space ≤ p.space + k₁ := by
  have h (j : Fin k₂) : Fin.natAddEmb k₁ j ∉ Set.range (Fin.castAddEmb k₂) := by
    simp [Fin.castAdd_ne_natAdd]
  simpa using exists_runPath_extendTapes (Fin.natAddEmb k₁) hh c.output
    (fun j => embed_workTapes_of_notMem_range _ c _ _ (h j))
    fun j => embed_workTapePos_of_notMem_range _ c _ _ (h j)

end Concatenate

/-- Concatenating two computations preserves additive space bounds. Rewinding costs at most the
first computation's time plus two steps. The space estimate adds the bounds for running the
first machine, rewinding the input, and running the second machine. This counts some work-tape
cells more than once. -/
theorem ComputesInTimeAndSpace.concatenate {tm₁ : MultiTapeTM k₁ Symbol State₁}
    {tm₂ : MultiTapeTM k₂ Symbol State₂} {input out₁ out₂ : List Symbol} {t₁ t₂ s₁ s₂ : ℕ}
    (h₁ : tm₁.ComputesInTimeAndSpace input out₁ t₁ s₁)
    (h₂ : tm₂.ComputesInTimeAndSpace input out₂ t₂ s₂) :
    (tm₁.concatenate tm₂).ComputesInTimeAndSpace input (out₁ ++ out₂)
      (2 * t₁ + t₂ + 2) (s₁ + s₂ + 2 * (k₁ + k₂)) := by
  obtain ⟨p₁, hh₁, halt₁, rfl, ht₁, hs₁⟩ := computesInTimeAndSpace_iff_exists_runPath.mp h₁
  obtain ⟨p₂, hh₂, halt₂, rfl, ht₂, hs₂⟩ := computesInTimeAndSpace_iff_exists_runPath.mp h₂
  -- the three phases: run `tm₁`, rewind the input, run `tm₂`
  obtain ⟨pa, hha, hla, hta, hsa⟩ := Concatenate.first_phase (k₂ := k₂) hh₁
  obtain ⟨pr, hhr, hlr, htr, hsr⟩ := exists_runPath_rewindInput pa.last
  obtain ⟨pb, hhb, hlb, htb, hsb⟩ := Concatenate.third_phase hh₂ p₁.last
  -- their paths compose
  obtain ⟨par, hhar, hlar, htar, hsar, -⟩ :=
    exists_runPath_seq (p₁ := pr) (by simpa [hla, Cfg.Halted] using halt₁) hhr
  obtain ⟨p, hh, hl, ht, hs, -⟩ := exists_runPath_seq (p₀ := par) (p₁ := pb)
    (by rw [hlar, hlr]; rfl) (by rw [hhb, hlar, hlr, hla]; rfl)
  have hin : p₁.last.inputPos.val ≤ 1 + p₁.length := by
    simpa [hh₁, add_comm] using inputPos_last_runPath_le p₁
  simp only [hla, embed_inputPos] at htr
  rw [MultiTapeTM.concatenate, computesInTimeAndSpace_iff_exists_runPath]
  -- time: `t₁ + (t₁ + 2) + t₂`, space: `(s₁ + k₂) + (k₁ + k₂) + (s₂ + k₁)`
  exact ⟨p, by rw [hh, hhar, hha]; rfl, by simpa [hl, hlb, Cfg.Halted] using halt₂,
    by simp [hl, hlb], by grind, by grind⟩

/-- Compute a function whose encoded output is the concatenation of two computed outputs.
The input encoding is shared; the output types and encodings may differ. -/
theorem ComputesFunInTimeAndSpace.concatenate {tm₁ : MultiTapeTM k₁ Symbol State₁}
    {tm₂ : MultiTapeTM k₂ Symbol State₂} {α β γ δ : Type*} {f₁ : α → β} {f₂ : α → γ} {f : α → δ}
    {encIn : α ↪ List Symbol} {enc₁ : β ↪ List Symbol} {enc₂ : γ ↪ List Symbol}
    {encOut : δ ↪ List Symbol}
    {t₁ t₂ s₁ s₂ : α → ℕ}
    (h₁ : tm₁.ComputesFunInTimeAndSpace encIn enc₁ f₁ t₁ s₁)
    (h₂ : tm₂.ComputesFunInTimeAndSpace encIn enc₂ f₂ t₂ s₂)
    (henc : ∀ x, encOut (f x) = enc₁ (f₁ x) ++ enc₂ (f₂ x)) :
    (tm₁.concatenate tm₂).ComputesFunInTimeAndSpace encIn encOut f
      (fun x => 2 * t₁ x + t₂ x + 2) (fun x => s₁ x + s₂ x + 2 * (k₁ + k₂)) :=
  fun x => henc x ▸ (h₁ x).concatenate (h₂ x)

/-- A function whose encoding concatenates two computed outputs is computable in time
`2 * t₁ + t₂ + 2` and space `3 * (s₁ + s₂)`. The result function and encoding are specified by
`henc`. -/
theorem ComputableInTimeAndSpace.concatenate {α β γ δ : Type*} {f₁ : α → β} {f₂ : α → γ} {f : α → δ}
    {encIn : α ↪ List Bool} {enc₁ : β ↪ List Bool} {enc₂ : γ ↪ List Bool}
    {encOut : δ ↪ List Bool}
    {t₁ t₂ s₁ s₂ : α → ℕ}
    (h₁ : ComputableInTimeAndSpace f₁ encIn enc₁ t₁ s₁)
    (h₂ : ComputableInTimeAndSpace f₂ encIn enc₂ t₂ s₂)
    (henc : ∀ x, encOut (f x) = enc₁ (f₁ x) ++ enc₂ (f₂ x)) :
    ComputableInTimeAndSpace f encIn encOut (fun x => 2 * t₁ x + t₂ x + 2)
      (fun x => 3 * (s₁ x + s₂ x)) := by
  obtain ⟨k₁, State₁, _, tm₁, hm₁⟩ := h₁
  obtain ⟨k₂, State₂, _, tm₂, hm₂⟩ := h₂
  exact ⟨k₁ + k₂, _, inferInstance, tm₁.concatenate tm₂,
    (hm₁.concatenate hm₂ henc).mono (fun _ => le_rfl) fun x => by
      grind [(hm₁ x).2.2.numTapes_le, (hm₂ x).2.2.numTapes_le]⟩

end Turing.MultiTapeTM
