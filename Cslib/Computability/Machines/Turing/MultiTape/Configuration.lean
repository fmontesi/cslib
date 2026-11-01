/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, Aviv Bar Natan
-/

module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Sign.Defs
public import Mathlib.Data.Fin.Basic
public import Cslib.Init

/-!
# Configurations of Multi-Tape Turing Machines

Configurations of a multi-tape Turing machine with a read-only input tape, `k` work tapes and one
write-only output tape, together with what a single transition does to a configuration.

The configurations are used by both deterministic and nondeterministic multi-tape Turing machines
and give instantaneous descriptions of their state. An `Action` describes how one configuration
transitions to the next. It records which way the input head moves, what is written and where the
work heads move, which symbol is emitted and which state follows. `Action.apply` carries out the
action on a configuration.

## Design

Configurations and actions are defined independently of a machine.

The output tape is part of the configuration, so the string emitted along a run can be read off
the configuration the run ends in. An action can optionally output one symbol, which models the
write-only output tape.

The input head can move freely on the input, but any move attempt beyond one cell outside the input
results in no movement. Restricting the movement of the input head is not essential, but useful
because it allows us to easily bound the number of possible configurations of a space-bounded
machine. Most textbooks have this restriction.

This definition is adapted from the one in [Papadimitriou94], chapter 2.3 including
the sub-linear space modifications from chapter 2.5 with the following changes:

- We allow Turing machines to choose to not write on a tape. This is equivalent to
  writing the read symbol again but makes it easier to reason about the semantics.
- Our tapes are infinite in both directions instead of just to the right. This definition is
  equivalent (see [AroraBarak09], Claim 1.4). It saves us from having to add a "start marker" to
  the alphabet.
- We only have a single halting state. The different ways to halt (accepting, rejecting, etc) can
  be distinguished based on the output.
- The input-head restriction is enforced by `Action.apply`, rather than by restricting the
  transition relation. The two definitions are equivalent, but allowing all actions makes it
  easier to define a universal machine.

## Important Declarations

* `Cfg`: the configuration: the internal state, the tape contents and head positions, and the
    output tape
* `Action`: what a machine does in one step
* `Action.apply`: the effect of one action on a configuration
* `HeadSymbols`, `Cfg.headSymbols`: the symbols under the heads, which a transition reads
* `Cfg.Halted`, `Cfg.init`: halting, and the configuration a machine starts in

## References

* [C. Papadimitriou, *Computational Complexity*][Papadimitriou94]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

/-- What a machine does in one step. -/
structure Action (k : ℕ) (Symbol State : Type*) where
  /-- The movement (attempt) of the input head. -/
  inputTape : SignType
  /-- Actions on the work tapes: optionally a symbol to write and the head movement. -/
  workTapes : Fin k → (Option (Option Symbol)) × SignType
  /-- An optional symbol to output. -/
  output : Option Symbol
  /-- The successor state or none to halt. -/
  state : Option State

/--
The configurations of a Turing machine is relative to the input of the machine and consist of:
- an `Option`al state (or none for the halting state),
- the position of the input head (shifted by one),
- the contents of the work tape,
- the positions of the work tape heads,
- the contents of the write-only output tape
-/
@[ext]
structure Cfg (k : ℕ) (Symbol State : Type*) (input : List Symbol) where
  /-- the state of the TM (or none for the halting state) -/
  state : Option State
  /-- the position of the input head, shifted by one -/
  inputPos : Fin (input.length + 2)
  /-- the work tapes -/
  workTapes : Fin k → ℤ → Option Symbol
  /-- the positions of the heads on the work tapes -/
  workTapePos : Fin k → ℤ
  /-- the contents of the write-only output tape -/
  output : List Symbol
deriving Inhabited

/-- Two configurations with no work tapes are equal when their state, input head and output
agree. -/
lemma Cfg.ext_zero_tapes {Symbol State : Type*} {input : List Symbol}
    {cfg₁ cfg₂ : Cfg 0 Symbol State input} (state : cfg₁.state = cfg₂.state)
    (inputPos : cfg₁.inputPos = cfg₂.inputPos) (output : cfg₁.output = cfg₂.output) :
    cfg₁ = cfg₂ :=
  Cfg.ext state inputPos (funext fun i => i.elim0) (funext fun i => i.elim0) output

/-- Attempt to move the input tape head.
The machine can only read one empty cell outside of the input,
any attempted movement beyond that results in no movement.

The addition is performed in `ℤ` before clamping. Performing it in `Fin (n + 2)` would wrap an
outward boundary move to the opposite end of the input. -/
@[scoped grind =]
def moveInputPos {n : ℕ} (pos : Fin (n + 2)) (m : SignType) : Fin (n + 2) :=
  let p := ((pos.val : ℤ) + (m.cast : ℤ)).toNat
  if h : p < n + 2 then ⟨p, h⟩ else ⟨n + 1, by omega⟩

@[simp]
lemma moveInputPos_zero {n : ℕ} (pos : Fin (n + 2)) :
    moveInputPos pos 0 = pos := by
  apply Fin.ext
  simp [moveInputPos, pos.isLt]

@[simp]
lemma moveInputPos_leftBoundary {n : ℕ} :
    moveInputPos (0 : Fin (n + 2)) (-1) = 0 := by
  apply Fin.ext
  simp [moveInputPos]

@[simp]
lemma moveInputPos_rightBoundary {n : ℕ} :
    moveInputPos (⟨n + 1, by omega⟩ : Fin (n + 2)) 1 = ⟨n + 1, by omega⟩ := by
  unfold moveInputPos
  rw [dite_eq_right (by simp; omega)]

/-- A left move away from the left input boundary decrements the native input position. -/
lemma moveInputPos_neg_of_ne_left {n : ℕ} (p : Fin (n + 2)) (h : p ≠ 0) :
    moveInputPos p .neg = ⟨p.val - 1, by have := p.isLt; omega⟩ := by
  have hp : 0 < p.val := Nat.pos_of_ne_zero (fun hz => h (Fin.ext hz))
  unfold moveInputPos
  apply Fin.ext
  rw [dite_eq_left] <;> simp <;> omega

/-- A right move away from the right input boundary increments the native input position. -/
lemma moveInputPos_pos_of_ne_right {n : ℕ} (p : Fin (n + 2)) (h : p.val ≠ n + 1) :
    moveInputPos p .pos = ⟨p.val + 1, by have := p.isLt; omega⟩ := by
  unfold moveInputPos
  rw [dite_eq_left]
  · apply Fin.ext
    simp
  · simp
    omega

/-- The value of the input head after a move, as a clamped integer. `omega`-friendly. -/
lemma val_moveInputPos_eq {n : ℕ} (pos : Fin (n + 2)) (m : SignType) :
    ((moveInputPos pos m).val : ℤ) = min ((n : ℤ) + 1) (max 0 ((pos.val : ℤ) + (m.cast : ℤ))) := by
  grind

/-- The input head moves by at most one position. -/
lemma val_moveInputPos_le {n : ℕ} (pos : Fin (n + 2)) (m : SignType) :
    (moveInputPos pos m).val ≤ pos.val + 1 := by
  have h := val_moveInputPos_eq pos m
  have hmc : (m.cast : ℤ) = -1 ∨ (m.cast : ℤ) = 0 ∨ (m.cast : ℤ) = 1 := by
    rcases m with _ | _ | _ <;> simp [SignType.cast]
  omega

/-- The symbol currently under the input tape head. -/
def Cfg.inputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  if h₁ : cfg.inputPos = 0 then none
  else if h₂ : cfg.inputPos = input.length + 1 then none
  else input[cfg.inputPos.val - 1]'(by grind)

/-- At either boundary of the input, the head reads a blank. -/
lemma inputSymbol_eq_none_of_boundary {cfg : Cfg k Symbol State input}
    (h : cfg.inputPos.val = 0 ∨ cfg.inputPos.val = input.length + 1) :
    cfg.inputSymbol = none := by
  grind [Cfg.inputSymbol]

@[simp]
lemma inputSymbolInner {cfg : Cfg k Symbol State input} (p : ℕ)
    (h₁ : cfg.inputPos.val = 1 + p)
    (h₂ : p < input.length) :
    cfg.inputSymbol = some input[p] := by
  grind [Cfg.inputSymbol]

/-- The symbol read by work tape `i`. -/
def Cfg.workTapeSymbols (cfg : Cfg k Symbol State input) (i : Fin k) : Option Symbol :=
  cfg.workTapes i (cfg.workTapePos i)

/-- The symbols under the heads of a machine with `k` work tapes, which its transitions read. -/
@[ext]
structure HeadSymbols (k : ℕ) (Symbol : Type*) where
  /-- the symbol under the input head -/
  inputSymbol : Option Symbol
  /-- the symbols under the work-tape heads -/
  workTapeSymbols : Fin k → Option Symbol

/-- The symbols under the heads of a configuration. -/
@[simps]
def Cfg.headSymbols (cfg : Cfg k Symbol State input) : HeadSymbols k Symbol :=
  ⟨cfg.inputSymbol, cfg.workTapeSymbols⟩

/-- A configuration is halted when it has no state to continue from. -/
abbrev Cfg.Halted (cfg : Cfg k Symbol State input) : Prop := cfg.state = none

/-- The same configuration with a word prepended to the output tape. A machine never reads its
output, so prepending to it preserves steps: cf. `Turing.MultiTapeNTM.prependOutputHom`. -/
@[simps] def Cfg.prependOutput (c : Cfg k Symbol State input) (pre : List Symbol) :
    Cfg k Symbol State input :=
  ⟨c.state, c.inputPos, c.workTapes, c.workTapePos, pre ++ c.output⟩

/-- The same configuration in a different control state, possibly of a different state type. -/
@[simps] def Cfg.withState (cfg : Cfg k Symbol State input)
    {State' : Type*} (q : Option State') : Cfg k Symbol State' input :=
  ⟨q, cfg.inputPos, cfg.workTapes, cfg.workTapePos, cfg.output⟩

/-- Remap the (optional) state of a configuration through `φ`, leaving the input head, the work
tapes, the work-tape heads and the output alone. Control-flow combinators such as `seq` embed a
sub-machine's configurations into the combined machine by exactly such a state remap. -/
@[simps] def Cfg.mapState {State' : Type*} (φ : Option State → Option State')
    (c : Cfg k Symbol State input) : Cfg k Symbol State' input :=
  ⟨φ c.state, c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- The initial configuration for a starting state and an input string. -/
@[simp]
def Cfg.init (q₀ : State) (input : List Symbol) : Cfg k Symbol State input :=
  ⟨some q₀, 1, fun _ _ => none, fun _ => 0, []⟩

/--
The effect of an action on a configuration: move the input head, write and move on the work tapes,
append the emitted symbol to the output tape, and go to the successor state. This is the part of a
step that does not depend on how the action was chosen.
-/
@[simps -fullyApplied]
def Action.apply (action : Action k Symbol State) (cfg : Cfg k Symbol State input) :
    Cfg k Symbol State input where
  state := action.state
  inputPos := moveInputPos cfg.inputPos action.inputTape
  workTapes i := match (action.workTapes i).1 with
    | none => cfg.workTapes i
    | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
  workTapePos i := cfg.workTapePos i + (action.workTapes i).2
  output := cfg.output ++ action.output.toList

/-- A work tape head moves by at most one cell when an action is applied. -/
lemma workTapePos_apply_le (action : Action k Symbol State)
    (cfg : Cfg k Symbol State input) (i : Fin k) :
    |(action.apply cfg).workTapePos i - cfg.workTapePos i| ≤ 1 := by
  simp only [Action.apply, add_sub_cancel_left, abs_le, SignType.cast]
  grind

end Turing
