/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Redirecting the output to a work tape

`outputToTape tm` behaves like `tm`, except that whatever `tm` would append to the write-only
output tape is written on a fresh work tape instead, whose head always stands at the write
frontier.

Since the output is append-only, the frontier position is a *function of the configuration* —
the length of the output so far — so the redirected machine mirrors the original through the
configuration map `outCfg`, a homomorphism of step relations (`outCfgHom`), so each run path of `tm`
maps to a run path of the redirected machine.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- `tm`, with its output writes redirected onto a fresh last work tape, whose head always stands
at the write frontier. -/
@[expose] public noncomputable def outputToTape (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM (k + 1) Symbol State :=
  tm.adapt
    { read := fun heads => ⟨heads.inputSymbol, heads.workTapeSymbols ∘ Fin.castSucc⟩
      action := fun _ a =>
        { a with
          workTapes := Fin.lastCases
            (match a.output with
              | none => (none, 0)
              | some s => (some (some s), 1))
            a.workTapes
          output := none } }

/-- A configuration of `tm`, as the redirected machine sees it: the output so far sits on the
last work tape with the head at its end, and the real output is empty. -/
@[expose] public def outCfg (c : Cfg k Symbol State input) :
    Cfg (k + 1) Symbol State input :=
  ⟨c.state, c.inputPos,
    Fin.lastCases (tapeOfList c.output) (fun j => c.workTapes j),
    Fin.lastCases (c.output.length : ℤ) (fun j => c.workTapePos j),
    []⟩

@[simp]
public lemma outCfg_workTapes_last (c : Cfg k Symbol State input) :
    (outCfg c).workTapes (Fin.last k) = tapeOfList c.output := by
  simp [outCfg]

@[simp]
public lemma outCfg_workTapes_castSucc (c : Cfg k Symbol State input) (j : Fin k) :
    (outCfg c).workTapes j.castSucc = c.workTapes j := by
  simp [outCfg]

@[simp]
public lemma outCfg_workTapePos_last (c : Cfg k Symbol State input) :
    (outCfg c).workTapePos (Fin.last k) = (c.output.length : ℤ) := by
  simp [outCfg]

@[simp]
public lemma outCfg_workTapePos_castSucc (c : Cfg k Symbol State input) (j : Fin k) :
    (outCfg c).workTapePos j.castSucc = c.workTapePos j := by
  simp [outCfg]

@[simp]
public lemma outCfg_workTapeSymbols_castSucc (c : Cfg k Symbol State input) (j : Fin k) :
    (outCfg c).workTapeSymbols j.castSucc = c.workTapeSymbols j := by
  simp [Cfg.workTapeSymbols]

/-- The redirection preserves steps, so it maps run paths of `tm` to run paths of the redirected
machine. -/
@[expose, simps! apply] public noncomputable def outCfgHom (tm : MultiTapeTM k Symbol State) :
    (tm.stepRel input).Hom (tm.outputToTape.stepRel input) :=
  follows_adapt.stepHom outCfg (fun _ => Option.map_id_apply)
    (fun c => HeadSymbols.ext rfl (funext (outCfg_workTapeSymbols_castSucc c))) fun c a => by
      refine Cfg.ext rfl rfl (funext fun l => ?_) (funext fun l => ?_) rfl <;>
        induction l using Fin.lastCases with
        | last =>
          cases h : a.output <;> simp [h, Action.apply, tapeOfList_append_single, SignType.cast]
        | cast j => simp [Action.apply]

/-- The initial configuration of the redirected machine is the original's through `outCfg`. -/
public lemma initCfg_outputToTape (tm : MultiTapeTM k Symbol State) (input : List Symbol) :
    tm.outputToTape.initCfg input = outCfg (tm.initCfg input) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
    simp [MultiTapeNTM.initCfg, Cfg.init]

/-- **Space of the output-redirected path.** The `k` inner tapes visit exactly what the original
path visits, and the frontier head only walks up to the final length of the output, so the
redirection costs at most the final output length plus one. -/
public lemma space_map_outCfgHom_le (tm : MultiTapeTM k Symbol State) (p : tm.RunPath input) :
    (p.map (outCfgHom tm)).space ≤ p.space + (p.last.output.length + 1) := by
  simpa [Finset.card_compl] using p.space_map_le _ Fin.castSuccEmb
    (fun _ => .Icc 0 (p.last.output.length : ℤ)) (fun c _ => outCfg_workTapePos_castSucc c)
    fun c ⟨n, hn⟩ l hl => by
      induction l using Fin.lastCases with
      | last =>
        have : c.output.length ≤ p.last.output.length := hn ▸ p.length_output_mono (Fin.le_last n)
        simpa using this
      | cast j => exact absurd ⟨j, rfl⟩ hl

end Turing.MultiTapeTM
