/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module

public import Mathlib.Order.RelSeries
public import Cslib.Computability.Machines.Turing.MultiTape.Configuration

/-!
# Nondeterministic Multi-Tape Turing Machines

Defines nondeterministic Turing machines with a read-only input tape, `k` work tapes and one
write-only output tape, their computation paths, and time bounds.

## Design

The design choices for configurations and actions are documented in
`Cslib.Computability.Machines.Turing.MultiTape.Configuration`.

Following [Papadimitriou94], chapter 2.7, a nondeterministic machine is a Turing machine whose
transition function is replaced by a transition relation: `Tr q input work action` holds when `Tr`
relates the state `q` and the read symbols `input` and `work` to `action`.

A halted configuration steps to itself, so once a machine has halted it has a run of every length.
A time bound is therefore an upper bound, with no separate account of the step at which it halted.

The transition relation may be empty at a running configuration. Such a configuration has no
successor configuration and is called stuck.

Time bounds apply to every computation path, regardless of its outcome. `RunsInTime input t`
requires every path of at least `t` steps to end in a halted configuration.

## Important Declarations

* `MultiTapeNTM`: the machine, an initial state and a transition relation
* `Step`: the one-step relation on configurations
* `RunPath`: finite relation series of steps
* `ComputationPath`: a run path starting at the initial configuration
* `Adapter`, `Follows`: a machine follows another when it performs each of its transitions,
  reading and acting through an adapter
* `Follows.step`, `Follows.runningStepHom`, `Follows.stepHom`: a configuration map that agrees with
  the adapter maps steps to steps, so it is a homomorphism of step relations and maps run paths
* `RunsInTime`: every computation path of at least the given length ends in a halted
  configuration

## References

* [C. Papadimitriou, *Computational Complexity*][Papadimitriou94]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace RelSeries

variable {α β : Type*} {r : SetRel α α} {s : SetRel β β}

/-- A member of a mapped series is the image of a member. -/
lemma exists_of_mem_map {p : RelSeries r} {f : r.Hom s} {b : β} (hb : b ∈ p.map f) :
    ∃ a ∈ p, f a = b :=
  let ⟨i, hi⟩ := hb
  ⟨p i, ⟨i, rfl⟩, hi⟩

/-- A member of two joined series lies on one of them. -/
lemma mem_or_mem_of_mem_smash {p q : RelSeries r} {h : p.last = q.head} {a : α}
    (ha : a ∈ p.smash q h) : a ∈ p ∨ a ∈ q := by
  obtain ⟨j, rfl⟩ := ha
  refine Fin.addCases (m := p.length) (n := q.length + 1) (fun j => .inl ⟨j.castSucc, ?_⟩)
    (fun j => .inr ⟨j, ?_⟩) j <;> simp [smash]

end RelSeries

namespace Turing

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

/--
A nondeterministic multi-tape Turing machine with `k` work tapes over the alphabet of
`Option Symbol` (where `none` is the blank symbol). Neither `Symbol` nor `State` is required to be
finite.
-/
structure MultiTapeNTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- transition relation: which combinations of state, current input symbol, tuple of work head
  symbols and resulting actions are valid transitions -/
  Tr (q : State) (input : Option Symbol) (work : Fin k → Option Symbol)
    (action : Action k Symbol State) : Prop

namespace MultiTapeNTM

variable {ntm : MultiTapeNTM k Symbol State}

/-- The one-step relation on configurations. A halted configuration steps only to itself. A running
configuration steps by applying any action related to its state and read symbols by `Tr`. -/
@[scoped grind =]
def Step (ntm : MultiTapeNTM k Symbol State) (c₁ c₂ : Cfg k Symbol State input) : Prop :=
  match c₁.state with
  | none => c₂ = c₁
  | some q =>
    ∃ action, ntm.Tr q c₁.inputSymbol c₁.workTapeSymbols action ∧ c₂ = action.apply c₁

/-- A halted configuration steps only to itself. -/
lemma step_of_halt {c c' : Cfg k Symbol State input} (h : c.Halted) :
    ntm.Step c c' ↔ c' = c := by
  simp [Step, h]

/-- The initial configuration corresponding to an input string. -/
@[simp]
def initCfg (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) :
    Cfg k Symbol State input :=
  Cfg.init ntm.q₀ input

/-- The one-step relation on configurations for `input`, as a set of pairs. -/
abbrev stepRel (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) :
    SetRel (Cfg k Symbol State input) (Cfg k Symbol State input) :=
  {(c, c') | ntm.Step c c'}

/-- The steps of `ntm` from running configurations: the steps within a run until it halts. -/
abbrev runningStepRel (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) :
    SetRel (Cfg k Symbol State input) (Cfg k Symbol State input) :=
  {(c, c') | ¬c.Halted ∧ ntm.Step c c'}

/-- A nonempty list of configurations joined by steps of `ntm`. -/
abbrev RunPath (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) :=
  RelSeries (ntm.stepRel input)

namespace RunPath

/-- A run path mapped along a step-preserving map of configurations: `RelSeries.map`, typed as a
run path of the target machine. -/
abbrev map {k' : ℕ} {State' : Type*} {input' : List Symbol} {ntm' : MultiTapeNTM k' Symbol State'}
    (p : ntm.RunPath input) (f : (ntm.stepRel input).Hom (ntm'.stepRel input')) :
    ntm'.RunPath input' :=
  RelSeries.map p f

/-- The output only grows along a run path. -/
lemma length_output_mono (p : ntm.RunPath input) :
    Monotone fun i ↦ (p i).output.length := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  have : ntm.Step (p i.castSucc) (p i.succ) := p.step i
  grind [Step, Action.apply_output]

/-- Once a run path is halted, its configuration stays unchanged. -/
lemma last_eq_of_head_halted (p : ntm.RunPath input) (h : p.head.Halted) : p.last = p.head := by
  induction p using RelSeries.inductionOn' with
  | singleton c => rfl
  | snoc p c hc ih =>
    have hp : p.last = p.head := ih (by simpa using h)
    have hh : p.last.Halted := hp ▸ (show p.head.Halted by simpa using h)
    simpa using ((step_of_halt hh).mp hc).trans hp

/-- The last configuration equals any earlier halted configuration. -/
lemma last_eq_of_halted (p : ntm.RunPath input) (i : Fin (p.length + 1))
    (h : (p i).Halted) : p.last = p i := by
  simpa using last_eq_of_head_halted (p.drop i) (by simpa using h)

/-- The number of steps taken by a run path. -/
def time (p : ntm.RunPath input) : ℕ := p.length

/-- A path that ends halted runs from its head to its last configuration in running steps, up to
its first halted configuration. -/
lemma exists_running (p : ntm.RunPath input) (h : p.last.Halted) :
    ∃ q : RelSeries (ntm.runningStepRel input), q.head = p.head ∧ q.last = p.last ∧
      q.length ≤ p.length ∧ ∀ c ∈ q, c ∈ p := by
  classical
  -- cut the path at its first halted configuration
  have hex : ∃ n, ∃ hn : n < p.length + 1, (p ⟨n, hn⟩).Halted := ⟨p.length, by lia, h⟩
  obtain ⟨hn, hhalt⟩ := Nat.find_spec hex
  refine ⟨⟨Nat.find hex, fun i => p ⟨i, by lia⟩, fun i =>
    ⟨fun hi => Nat.find_min hex i.isLt ⟨_, hi⟩, p.step ⟨i, by lia⟩⟩⟩, rfl,
    (p.last_eq_of_halted _ hhalt).symm, Nat.lt_succ_iff.mp hn, fun _ ⟨i, hi⟩ => ⟨_, hi⟩⟩

end RunPath

/-- A run path starting at the initial configuration for `input`. -/
structure ComputationPath (ntm : MultiTapeNTM k Symbol State) (input : List Symbol)
    extends toRunPath : ntm.RunPath input where
  /-- the path starts at the initial configuration -/
  head_eq : toRunPath.head = ntm.initCfg input

namespace ComputationPath

/-- The number of steps taken by a computation path. -/
def time (p : ntm.ComputationPath input) : ℕ := RunPath.time p.toRunPath

end ComputationPath

/-- Every computation path on `input` of at least `t` steps ends in a halted configuration.
A path ending in a stuck configuration must have fewer than `t` steps. -/
def RunsInTime (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) (t : ℕ) : Prop :=
  ∀ p : ntm.ComputationPath input, t ≤ p.time → p.last.Halted

/-- A time bound can be increased. -/
lemma RunsInTime.mono {input : List Symbol} {t t' : ℕ}
    (h : ntm.RunsInTime input t) (ht : t ≤ t') : ntm.RunsInTime input t' :=
  fun p hp ↦ h p (ht.trans hp)

/-! ### Following a machine -/

/-- How a machine with `k'` work tapes and states `State'` performs the transitions of a machine
with `k` work tapes and states `State`. A transition turns the symbols under the heads into an
action, so the outer machine translates both ends: `read` computes the symbols the inner machine
reads from those under the outer heads, and `action` turns the inner action into an outer one,
which may also depend on the outer symbols. -/
structure Adapter (k k' : ℕ) (Symbol State State' : Type*) where
  /-- the symbols the inner machine reads -/
  read : HeadSymbols k' Symbol → HeadSymbols k Symbol
  /-- the outer action performing an inner action -/
  action : HeadSymbols k' Symbol → Action k Symbol State → Action k' Symbol State'

/-- The adapter that relabels the states through `φ` and reads and acts on the same tapes. -/
@[simps]
def Adapter.mapState {State' : Type*} (φ : Option State → Option State') :
    Adapter k k Symbol State State' :=
  ⟨id, fun _ a => { a with state := φ a.state }⟩

/-- `ntm'` follows `ntm` through `adapter`, in state `state q` while `ntm` is in state `q`: whatever
`ntm` may do in `q` on what `adapter` reads, `ntm'` may do the adapted action in `state q`. -/
def Follows {k' : ℕ} {State' : Type*} (ntm' : MultiTapeNTM k' Symbol State')
    (ntm : MultiTapeNTM k Symbol State) (state : State → State')
    (adapter : Adapter k k' Symbol State State') : Prop :=
  ∀ q heads action,
    ntm.Tr q (adapter.read heads).inputSymbol (adapter.read heads).workTapeSymbols action →
      ntm'.Tr (state q) heads.inputSymbol heads.workTapeSymbols (adapter.action heads action)

namespace Follows

variable {k' : ℕ} {State' : Type*} {input' : List Symbol} {ntm' : MultiTapeNTM k' Symbol State'}
  {state : State → State'} {adapter : Adapter k k' Symbol State State'}

/-- **A follower mirrors a step.** If `ntm'` follows `ntm`, and the map `f` relabels the state of
`c` through `state`, reads through `adapter` what `c` reads, and carries the action of a step from
`c` to its adaptation, then `f` maps the step to a step of `ntm'`. -/
lemma step (h : ntm'.Follows ntm state adapter)
    (f : Cfg k Symbol State input → Cfg k' Symbol State' input') {c c' : Cfg k Symbol State input}
    (hstep : ntm.Step c c') (hstate : c.state.map state = (f c).state)
    (hread : adapter.read (f c).headSymbols = c.headSymbols)
    (haction : ∀ action, action.apply c = c' →
      (adapter.action (f c).headSymbols action).apply (f c) = f c') :
    ntm'.Step (f c) (f c') := by
  rcases hq : c.state with _ | q
  · rw [(step_of_halt hq).mp hstep]
    exact (step_of_halt (show (f c).state = none by rw [← hstate, hq]; rfl)).mpr rfl
  · simp only [Step, hq, Option.map_some] at hstep hstate
    obtain ⟨action, hTr, rfl⟩ := hstep
    rw [Step, ← hstate]
    exact ⟨_, h q _ action (by rwa [hread]), (haction action rfl).symm⟩

/-- **A follower mirrors the running steps.** If `ntm'` follows `ntm`, and `f` sends a configuration
in state `q` to one in state `state q`, from which `adapter` reads what the configuration reads and
on which each adapted action acts as the action acts on the configuration, then `f` maps each
running step of `ntm` to a step of `ntm'`. -/
def runningStepHom (h : ntm'.Follows ntm state adapter)
    (f : Cfg k Symbol State input → Cfg k' Symbol State' input')
    (hstate : ∀ c q, c.state = some q → (f c).state = some (state q))
    (hread : ∀ c, adapter.read (f c).headSymbols = c.headSymbols)
    (haction : ∀ c action,
      (adapter.action (f c).headSymbols action).apply (f c) = f (action.apply c)) :
    (ntm.runningStepRel input).Hom (ntm'.stepRel input') :=
  ⟨f, fun {c _} ⟨hrunning, hstep⟩ ↦ (Option.ne_none_iff_exists'.mp hrunning).elim fun q hq ↦
    h.step f hstep (by rw [hq, hstate c q hq]; rfl) (hread c) fun action h ↦ h ▸ haction c action⟩

/-- **A follower mirrors the steps.** As `runningStepHom`, for an `f` that relabels every state
through `state`, so that it also keeps halted configurations halted. -/
def stepHom (h : ntm'.Follows ntm state adapter)
    (f : Cfg k Symbol State input → Cfg k' Symbol State' input')
    (hstate : ∀ c, c.state.map state = (f c).state)
    (hread : ∀ c, adapter.read (f c).headSymbols = c.headSymbols)
    (haction : ∀ c action,
      (adapter.action (f c).headSymbols action).apply (f c) = f (action.apply c)) :
    (ntm.stepRel input).Hom (ntm'.stepRel input') :=
  ⟨f, fun hstep ↦ h.step f hstep (hstate _) (hread _) fun action h ↦ h ▸ haction _ action⟩

end Follows

/-- A machine never reads its output tape, so prepending a word to the output preserves steps. -/
@[simps! apply]
def prependOutputHom (ntm : MultiTapeNTM k Symbol State) (pre : List Symbol) :
    (ntm.stepRel input).Hom (ntm.stepRel input) :=
  Follows.stepHom (state := id) (adapter := .mapState id) (fun _ _ _ h => h) (·.prependOutput pre)
    (fun _ => Option.map_id_apply) (fun _ => rfl) fun _ _ =>
      Cfg.ext rfl rfl rfl rfl (by simp [Action.apply])

end MultiTapeNTM

end Turing
