/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, Aviv Bar Natan
-/

module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Sign.Defs
public import Cslib.Computability.Machines.Turing.MultiTape.Space

/-!
# Deterministic Multi-Tape Turing Machines

A deterministic Turing machine is a nondeterministic machine whose transition relation has exactly
one action for every combination of state and symbols read. From the transition relation it derives
a transition function `tr` and a function `step` which maps each configuration to its unique
successor configuration (a halted configuration maps to itself).

The design choices for configurations and actions are documented in
`Cslib.Computability.Machines.Turing.MultiTape.Configuration`.

## Important Declarations

We define a number of structures and concepts related to multi-tape Turing machine computation:

* `MultiTapeNTM.IsDeterministic`: the transition relation relates every state and tuple of read
    symbols to exactly one action
* `MultiTapeTM`: the TM itself
* `tr`, `ofTr`: the derived transition function and construction from a function
* `adapt`: the machine run through an adapter
* `combine`: two machines on the same tapes combined into one
* `step`, `runFrom`: the successor configuration and iteration of this function
* `MultiTapeNTM.RunPath.ofDeterministic`, `MultiTapeNTM.ComputationPath.ofDeterministic`:
    paths of a given length from an arbitrary or initial configuration
* `Computes`: the machine halts with the given output on an input
* `ComputesInTimeAndSpace`: the machine produces an output within the shared resource bounds
* `ComputesFunInTimeAndSpace`: function computation with the shared time and space bounds
* `ComputableInTimeAndSpace`: such a machine exists with binary alphabet and finitely many states.
* `ComputableInTimeAndSpaceOfLength`: the specialization to bounds on encoded input length.
* `DecidableInTimeAndSpace`: a proof that a TM decides a language within a certain time
    and space bound.

-/

@[expose] public section

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/-- Every state and tuple of read symbols is related to exactly one action by `ntm`'s transition
relation. -/
def MultiTapeNTM.IsDeterministic (ntm : MultiTapeNTM k Symbol State) : Prop :=
  ∀ (q : State) (input : Option Symbol) (work : Fin k → Option Symbol),
    ∃! action, ntm.Tr q input work action

/--
A multi-tape Turing machine with `k` work tapes over the alphabet of `Option Symbol` (where `none`
is the blank tape symbol). Note that it is not required that `Symbol` or `State` are finite
to keep the definition more general. The restriction will be introduced once we start talking about
computability by Turing machines in general.
-/
structure MultiTapeTM (k : ℕ) (Symbol State : Type*)
    extends MultiTapeNTM k Symbol State where
  /-- Every state and tuple of read symbols is related to exactly one action by the transition
  relation. -/
  deterministic : toMultiTapeNTM.IsDeterministic

instance : CoeOut (MultiTapeTM k Symbol State) (MultiTapeNTM k Symbol State) :=
  ⟨MultiTapeTM.toMultiTapeNTM⟩

namespace MultiTapeTM

variable {tm : MultiTapeTM k Symbol State}

/-- The unique action related to the given state and read symbols by `Tr`. -/
noncomputable def tr (tm : MultiTapeTM k Symbol State) (q : State) (input : Option Symbol)
    (work : Fin k → Option Symbol) : Action k Symbol State :=
  (tm.deterministic q input work).choose

/-- `Tr` relates a state and read symbols to an action exactly when `tr` returns that action. -/
@[simp, scoped grind =]
lemma tr_iff {q : State} {input : Option Symbol} {work : Fin k → Option Symbol}
    {action : Action k Symbol State} : tm.Tr q input work action ↔ tm.tr q input work = action :=
  ⟨fun h => ((tm.deterministic q input work).choose_spec.2 action h).symm,
    fun h => h ▸ (tm.deterministic q input work).choose_spec.1⟩

/-- Construct a deterministic machine from an initial state and transition function. -/
def ofTr (q₀ : State)
    (tr : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State) :
    MultiTapeTM k Symbol State where
  q₀ := q₀
  Tr q input work action := tr q input work = action
  deterministic _ _ _ := by simp

/-- The initial state of `ofTr` is the supplied one. -/
@[simp]
lemma q₀_ofTr (q₀ : State)
    (tr : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State) :
    (ofTr q₀ tr).q₀ = q₀ :=
  rfl

/-- Extracting the transition of `ofTr` recovers the supplied function. -/
@[simp]
lemma tr_ofTr (q₀ : State)
    (tr : State → Option Symbol → (Fin k → Option Symbol) → Action k Symbol State)
    (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    (ofTr q₀ tr).tr q input work = tr q input work :=
  tr_iff.mp rfl

/-- The transitions of `tm` performed through `adapter`: it reads what `tm` reads through `adapter`
and performs the adaptation of the action of `tm`. -/
noncomputable def adaptedTr {k' : ℕ} {State' : Type*} (tm : MultiTapeTM k Symbol State)
    (adapter : MultiTapeNTM.Adapter k k' Symbol State State') (q : State) (inp : Option Symbol)
    (work : Fin k' → Option Symbol) : Action k' Symbol State' :=
  adapter.action ⟨inp, work⟩ (tm.tr q (adapter.read ⟨inp, work⟩).inputSymbol
    (adapter.read ⟨inp, work⟩).workTapeSymbols)

/-- `tm` run through `adapter`, a `MultiTapeNTM.Adapter`: the adapter computes what `tm` reads
from the symbols under the heads of the new machine, and gives the action of the new machine
performing each action of `tm`. In state `q`, `tm.adapt adapter` performs the adaptation of the
action of `tm` in `q` on what the adapter reads. -/
noncomputable def adapt {k' : ℕ} (tm : MultiTapeTM k Symbol State)
    (adapter : MultiTapeNTM.Adapter k k' Symbol State State) : MultiTapeTM k' Symbol State :=
  ofTr tm.q₀ (tm.adaptedTr adapter)

/-- `tm.adapt adapter` follows `tm`. -/
lemma follows_adapt {k' : ℕ} {adapter : MultiTapeNTM.Adapter k k' Symbol State State} :
    (tm.adapt adapter).Follows tm id adapter :=
  fun _ _ _ h => tr_iff.mp h ▸ rfl

/-- `tm₀` and `tm₁` combined into one machine on their shared tapes, which starts in `q₀`: in a
state `inl q` it performs the transition of `tm₀` in `q`, and in `inr q` that of `tm₁`. The maps
`next₀` and `next₁` say where the steps of each machine lead: within the same machine, to the other
machine, or to halting. -/
noncomputable def combine {State₀ State₁ : Type*} (tm₀ : MultiTapeTM k Symbol State₀)
    (tm₁ : MultiTapeTM k Symbol State₁) (next₀ : Option State₀ → Option (State₀ ⊕ State₁))
    (next₁ : Option State₁ → Option (State₀ ⊕ State₁)) (q₀ : State₀ ⊕ State₁) :
    MultiTapeTM k Symbol (State₀ ⊕ State₁) :=
  ofTr q₀ fun q => q.elim (tm₀.adaptedTr (.mapState next₀)) (tm₁.adaptedTr (.mapState next₁))

/-- Where the steps of a first machine lead when it runs in its own states: halting hands over to
the second machine in its state `q₁`. -/
def handOver {State₀ State₁ : Type*} (q₁ : State₁) (state : Option State₀) :
    Option (State₀ ⊕ State₁) :=
  some (state.elim (.inr q₁) .inl)

@[simp] lemma handOver_some {State₀ State₁ : Type*} (q₁ : State₁) (q : State₀) :
    handOver q₁ (some q) = some (.inl q) := rfl

@[simp] lemma handOver_none {State₀ State₁ : Type*} (q₁ : State₁) :
    handOver (State₀ := State₀) q₁ none = some (.inr q₁) := rfl

section combine

variable {State₀ State₁ : Type*} {tm₀ : MultiTapeTM k Symbol State₀}
  {tm₁ : MultiTapeTM k Symbol State₁} {next₀ : Option State₀ → Option (State₀ ⊕ State₁)}
  {next₁ : Option State₁ → Option (State₀ ⊕ State₁)} {q₀ : State₀ ⊕ State₁}

/-- In its states `inl q`, the combined machine follows `tm₀`, its steps leading along `next₀`. -/
lemma follows_combine_left : (combine tm₀ tm₁ next₀ next₁ q₀).Follows tm₀ .inl (.mapState next₀) :=
  fun _ _ _ h => tr_iff.mp h ▸ rfl

/-- In its states `inr q`, the combined machine follows `tm₁`, its steps leading along `next₁`. -/
lemma follows_combine_right : (combine tm₀ tm₁ next₀ next₁ q₀).Follows tm₁ .inr (.mapState next₁) :=
  fun _ _ _ h => tr_iff.mp h ▸ rfl

/-- If `next₀` keeps the live states of `tm₀` in `tm₀`, the combined machine mirrors the running
steps of `tm₀`, its states relabeled along `next₀`. -/
@[simps! apply]
noncomputable def combineLeftHom {input : List Symbol} (h : ∀ q, next₀ (some q) = some (.inl q)) :
    (tm₀.runningStepRel input).Hom ((combine tm₀ tm₁ next₀ next₁ q₀).stepRel input) :=
  follows_combine_left.runningStepHom (Cfg.mapState next₀) (fun _ _ hq => by simp [hq, h])
    (fun _ => rfl) fun _ _ => rfl

/-- If the steps of `tm₁` stay in `tm₁`, the combined machine mirrors them. -/
@[simps! apply]
noncomputable def combineRightHom {input : List Symbol} :
    (tm₁.stepRel input).Hom ((combine tm₀ tm₁ next₀ (Option.map .inr) q₀).stepRel input) :=
  follows_combine_right.stepHom (Cfg.mapState (Option.map .inr)) (fun _ => rfl) (fun _ => rfl)
    fun _ _ => rfl

end combine

/-!
## Stepping a Turing Machine

The step function lets the machine transition from one configuration to the next, and `runFrom`
gives the configuration reached after a number of steps. Configurations themselves are defined in
`Cslib.Computability.Machines.Turing.MultiTape.Configuration`.
-/

private lemma existsUnique_step (cfg : Cfg k Symbol State input) :
    ∃! cfg', tm.Step cfg cfg' := by
  unfold MultiTapeNTM.Step
  cases cfg.state <;> simp

/-- The unique successor configuration related to `cfg` by the inherited step relation. -/
noncomputable def step (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  (show ∃! cfg', tm.Step cfg cfg' from by exact existsUnique_step cfg).choose

/-- `Step` relates `c` to `c'` exactly when `step c = c'`. -/
@[simp, scoped grind =]
lemma step_iff {c c' : Cfg k Symbol State input} : tm.Step c c' ↔ tm.step c = c' := by
  unfold step
  exact (ExistsUnique.choose_eq_iff _).symm

/-- A running configuration takes the action selected by the transition function. -/
lemma step_of_state {cfg : Cfg k Symbol State input} {q : State} (h : cfg.state = some q) :
    tm.step cfg = (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg := by
  apply step_iff.mp
  simp [MultiTapeNTM.Step, h]

/-- The input head after a live step. -/
public lemma step_inputPos_of_state {cfg : Cfg k Symbol State input} {q : State}
    (h : cfg.state = some q) :
    (tm.step cfg).inputPos =
      moveInputPos cfg.inputPos (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).inputTape := by
  rw [step_of_state h, Action.apply_inputPos]

/-- A work tape after a live step. -/
public lemma step_workTapes_of_state {cfg : Cfg k Symbol State input} {q : State}
    (h : cfg.state = some q) (i : Fin k) :
    (tm.step cfg).workTapes i =
      match (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workTapes i |>.1 with
      | none => cfg.workTapes i
      | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s := by
  rw [step_of_state h]
  rfl

/-- A work tape head after a live step. -/
public lemma step_workTapePos_of_state {cfg : Cfg k Symbol State input} {q : State}
    (h : cfg.state = some q) (i : Fin k) :
    (tm.step cfg).workTapePos i =
      cfg.workTapePos i + ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workTapes i).2 := by
  rw [step_of_state h]
  rfl

@[simp]
lemma step_of_halt {cfg : Cfg k Symbol State input} (h : cfg.state = none) :
    tm.step cfg = cfg :=
  step_iff.mp ((MultiTapeNTM.step_of_halt h).mpr rfl)

end MultiTapeTM

namespace MultiTapeNTM

variable {tm : MultiTapeTM k Symbol State} {input : List Symbol}

/-- The path of the first `t` steps from `cfg`. -/
noncomputable def RunPath.ofDeterministic (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (t : ℕ) : tm.RunPath input where
  length := t
  toFun n := tm.step^[n.val] cfg
  step n := by simp [MultiTapeTM.step_iff, Function.iterate_succ_apply']

/-- Every deterministic run path is the canonical path from its head for its duration. -/
lemma RunPath.eq_ofDeterministic (p : tm.RunPath input) :
    p = .ofDeterministic tm p.head p.time := by
  refine RelSeries.ext rfl ?_
  change p.toFun = fun i ↦ tm.step^[i.val] p.head
  refine funext (Fin.induction rfl fun i ih ↦ ?_)
  simpa [Function.iterate_succ_apply'] using
    (MultiTapeTM.step_iff.mp (p.step i)).symm.trans (congrArg tm.step ih)

/-- The path of the first `t` steps on `input`, starting at the initial configuration. -/
noncomputable def ComputationPath.ofDeterministic (tm : MultiTapeTM k Symbol State)
    (input : List Symbol) (t : ℕ) : tm.ComputationPath input :=
  ⟨RunPath.ofDeterministic tm (tm.initCfg input) t, rfl⟩

/-- Every deterministic computation path is the canonical path for its duration. -/
lemma ComputationPath.eq_ofDeterministic (p : tm.ComputationPath input) :
    p = .ofDeterministic tm input p.time := by
  rcases p with ⟨p, hp⟩
  congr 1
  exact (RunPath.eq_ofDeterministic p).trans (by rw [hp]; rfl)

/-- Deterministic run paths from the same configuration are prefixes of one another: the shorter one
is the longer one, cut at its length. -/
lemma RunPath.eq_take {p q : tm.RunPath input} (hhead : p.head = q.head) (h : p.length ≤ q.length) :
    p = q.take ⟨p.length, Nat.lt_succ_of_le h⟩ := by
  refine p.eq_ofDeterministic.trans ((eq_ofDeterministic (q.take _)).trans ?_).symm
  rw [RelSeries.head_take, hhead]
  rfl

/-- The computation paths of a deterministic machine are prefixes of one another, so a path visiting
at most as many cells as another visits at most as many on each tape. -/
lemma ComputationPath.spaceUsedByTape_le_of_space_le (p : tm.ComputationPath input)
    {q : tm.ComputationPath input} (h : p.space ≤ q.space) :
    p.spaceUsedByTape ≤ q.spaceUsedByTape := by
  -- a shorter path is a prefix of a longer one, so it visits fewer cells on each tape
  have hmono {p q : tm.ComputationPath input} (h : p.time ≤ q.time) :
      p.spaceUsedByTape ≤ q.spaceUsedByTape := fun i => by
    change RunPath.spaceUsedByTape p.toRunPath i ≤ RunPath.spaceUsedByTape q.toRunPath i
    rw [RunPath.eq_take (by rw [p.head_eq, q.head_eq]) h]
    exact Finset.card_le_card (RunPath.visitedByTapeHead_take_subset _ _ i)
  rcases le_total p.time q.time with hpq | hqp
  · exact hmono hpq
  -- a longer `p` visits no more cells than `q`, so it visits exactly those of `q`
  have h : ∑ j, p.spaceUsedByTape j ≤ ∑ j, q.spaceUsedByTape j := h
  exact fun i => ((Finset.sum_eq_sum_iff_of_le fun j _ => hmono hqp j).mp
    (le_antisymm (Finset.sum_le_sum fun j _ => hmono hqp j) h) i (Finset.mem_univ i)).ge

/-- A step-preserving map sends the path of `t` steps from `cfg` to the path of `t` steps from the
image of `cfg`. -/
lemma RunPath.map_ofDeterministic {k' : ℕ} {State' : Type*} {input' : List Symbol}
    {tm' : MultiTapeTM k' Symbol State'} (f : (tm.stepRel input).Hom (tm'.stepRel input'))
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    (RunPath.ofDeterministic tm cfg t).map f = .ofDeterministic tm' (f cfg) t :=
  ((RunPath.ofDeterministic tm cfg t).map f).eq_ofDeterministic

end MultiTapeNTM

namespace MultiTapeTM

variable {tm : MultiTapeTM k Symbol State}

/-- The configuration reached by running the Turing machine for `t` steps from `cfg`.
If the Turing machine halts, it will stay at the halting configuration. -/
noncomputable def runFrom (cfg : Cfg k Symbol State input) (t : ℕ) : Cfg k Symbol State input :=
  tm.step^[t] cfg

/-- Every path of a deterministic machine follows its iterated step function. -/
lemma runPath_apply_eq_runFrom (p : tm.RunPath input) (i : Fin (p.length + 1)) :
    p i = tm.runFrom p.head i := by
  revert i
  rw [p.eq_ofDeterministic]
  exact fun _ ↦ rfl

/-- A deterministic computation ends at the corresponding iterate. -/
lemma computationPath_last_eq_runFrom (p : tm.ComputationPath input) :
    p.last = tm.runFrom (tm.initCfg input) p.time := by
  rw [p.eq_ofDeterministic]
  rfl

/-- Running from the image of a configuration under a step-preserving map reaches the image of the
original run. -/
lemma runFrom_map {k' : ℕ} {State' : Type*} {input' : List Symbol}
    {tm' : MultiTapeTM k' Symbol State'} (f : (tm.stepRel input).Hom (tm'.stepRel input'))
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm'.runFrom (f cfg) t = f (tm.runFrom cfg t) :=
  congrArg RelSeries.last (MultiTapeNTM.RunPath.map_ofDeterministic f cfg t).symm

/-- Nothing changes after the machine has halted. -/
lemma runFrom_eq_of_halt
    (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) {τ t : ℕ} (hle : τ ≤ t)
    (hhalt : (tm.runFrom cfg τ).state = none) :
    tm.runFrom cfg t = tm.runFrom cfg τ :=
  (MultiTapeNTM.RunPath.ofDeterministic tm cfg t).last_eq_of_halted
    ⟨τ, Nat.lt_succ_of_le hle⟩ hhalt

/-- A deterministic machine halted after `t` steps satisfies the shared time bound. -/
lemma runsInTime_of_halted {input : List Symbol} {t : ℕ}
    (h : (tm.runFrom (tm.initCfg input) t).Halted) : tm.RunsInTime input t := by
  intro p hp
  rw [computationPath_last_eq_runFrom p, runFrom_eq_of_halt _ _ hp h]
  exact h

/-- In `t` steps the input head moves at most `t` positions to the right. -/
lemma inputPos_runFrom_le (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    ((tm.runFrom cfg t).inputPos : ℕ) ≤ (cfg.inputPos : ℕ) + t := by
  induction t with
  | zero => simp [runFrom]
  | succ t ih =>
    rw [runFrom, Function.iterate_succ_apply', ← runFrom]
    by_cases hq : (tm.runFrom cfg t).state = none
    · rw [step_of_halt hq]
      omega
    · obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hq
      have h : ((tm.step (tm.runFrom cfg t)).inputPos : ℕ) ≤
          ((tm.runFrom cfg t).inputPos : ℕ) + 1 := by
        rw [step_inputPos_of_state hq]
        exact val_moveInputPos_le _ _
      omega

/-- The machine eventually halts on `input` with the given `output`. -/
def Computes (tm : MultiTapeTM k Symbol State) (input output : List Symbol) : Prop :=
  ∃ u, (tm.runFrom (tm.initCfg input) u).Halted ∧
    (tm.runFrom (tm.initCfg input) u).output = output

/-- The machine computes `output` from `input` within the shared time and space bounds. -/
def ComputesInTimeAndSpace (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol) (t s : ℕ) : Prop :=
  tm.Computes input output ∧ tm.RunsInTime input t ∧ tm.RunsInSpace input s

/-- The machine computes `f` relative to given encodings within the given time and space bounds. -/
def ComputesFunInTimeAndSpace {α β : Type*} (tm : MultiTapeTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol) (f : α → β) (t s : α → ℕ) : Prop :=
  ∀ a, tm.ComputesInTimeAndSpace (encIn a) (encOut (f a)) (t a) (s a)

/-- Resource bounds can be weakened independently on every input. -/
theorem ComputesFunInTimeAndSpace.mono {α β : Type*}
    {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol} {f : α → β} {t s t' s' : α → ℕ}
    (h : tm.ComputesFunInTimeAndSpace encIn encOut f t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    tm.ComputesFunInTimeAndSpace encIn encOut f t' s' :=
  fun a ↦ ⟨(h a).1, (h a).2.1.mono (ht a), (h a).2.2.mono (hs a)⟩

/-- Computability by a deterministic machine with a binary tape alphabet and finitely many states,
within the supplied input-indexed bounds. -/
def ComputableInTimeAndSpace {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    tm.ComputesFunInTimeAndSpace encIn encOut f t s

/-- There exists a binary Turing machine with finitely many states that, for every input `a`,
computes `encOut (f a)` from `encIn a` in at most `t (encIn a).length` steps,
using at most `s (encIn a).length` work-tape cells. -/
abbrev ComputableInTimeAndSpaceOfLength {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : ℕ → ℕ) : Prop :=
  ComputableInTimeAndSpace f encIn encOut
    (fun a => t (encIn a).length) (fun a => s (encIn a).length)

/-- Computability is monotone in the resource bounds. -/
theorem ComputableInTimeAndSpace.mono {α β : Type*}
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s t' s' : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputableInTimeAndSpace f encIn encOut t' s' := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  exact ⟨k, State, hfinite, tm, htm.mono ht hs⟩

open scoped Classical in
/-- The Boolean indicator function of a set. -/
noncomputable def indicator {α : Type*} (L : Set α) : α → Bool :=
  fun x => if x ∈ L then true else false

/-- A set is decidable within the given input-indexed bounds when its Boolean indicator is
computable in those bounds. -/
def DecidableInTimeAndSpace {α : Type*} (L : Set α) (enc : α ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ComputableInTimeAndSpace (indicator L) enc ⟨fun b ↦ [b], by intro a b h; simpa using h⟩ t s

/-- If a deterministic machine repeats a non-halting configuration, it never halts,
because the sequence between the two configurations will loop forever.
Note that this can be applied to two arbitrary and different time steps `t` and `t + Δ`
using `Function.iterate_add_apply`. -/
lemma not_halts_of_repeat_nonhalt
    (cfg : Cfg k Symbol State input)
    (h_not_halt : cfg.state ≠ none)
    (t : ℕ)
    (heq : tm.runFrom cfg (t + 1) = cfg) :
    ∀ t', (tm.runFrom cfg t').state ≠ none := by
  intro t'
  -- The configuration will repeat every `t + 1` steps.
  have hloop : ∀ n, tm.runFrom cfg (n * (t + 1)) = cfg := by
    intro n
    unfold runFrom
    rw [Nat.mul_comm, Function.iterate_mul]
    exact Function.iterate_fixed heq n
  by_contra hnh
  -- Assuming the machine halts at step `t'`, it is also halted at step `t' * (t + 1)`
  have h₁ : (tm.runFrom cfg (t' * (t + 1))).state = none := by
    have hle : t' ≤ t' * (t + 1) := by grind
    rwa [tm.runFrom_eq_of_halt cfg hle hnh]
  simp [hloop t', h_not_halt] at h₁

end MultiTapeTM

end Turing
