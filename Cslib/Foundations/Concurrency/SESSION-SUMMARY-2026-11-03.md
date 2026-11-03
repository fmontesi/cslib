# Session summary — `Smurf.lean`

**Timestamp:** 2026-11-03 (updated)
**File under work:** `Cslib/Foundations/Concurrency/Smurf.lean`
**Status:** compiles with **0 errors**, **1 `sorry`** remaining.

---

## Update: `ifSmurfThenTraces` is now proved

`ifSmurfThenTraces` is proved by applying the helper `core`.  The `core` proof was
restructured so that all cases are closed except one isolated lemma,
`core_branch` (the only remaining `sorry`).

Key reductions in `core`:

- Split both traces at their last label and apply the induction hypothesis to
  the prefixes.
- If the prefix projections differ, apply the induction hypothesis to the
  smaller pair `(t₁, t₂')` (resp. `(t₁', t₂)`).  The extra observed label must be
  the last element of the difference, which yields a prefix relation.  List
  helpers: `prefix_cancel_left`, `eq_of_prefix_singleton`,
  `projectTrace_prefix_concat`.
- The remaining case is `core_branch`: equal prefix projections with distinct
  observed final labels.

**Important:** the earlier conjecture that this case forces
`B.matching l₁ l₂` is **false**.  Countermodel: `s -x-> M -a->` and
`s -y-> N -b->` with `matching x y` (both unobserved) and `a, b` observed and
distinct.  Then `P(t₁) = [a]`, `P(t₂) = [b]`, but only `x` and `y` match; the
witness is at the empty prefixes.  The correct statement is the existential
witness isolated in `core_branch`.

A randomized model search (3–4 states, 5 labels, 500k trials) found no
counterexample to the theorem.

## Changes made to the definitions (as requested)

- `Branching` now carries `[irrefl : Std.Irrefl matching]`.
- `Smurf.u` now applies only to distinct labels:
  `l₁ ≠ l₂ → Tr s l₁ s₁ ∧ Tr s l₂ s₂ → I l₁ l₂ ∨ B.matching l₁ l₂`.
- `Smurf.d` added: the LTS is deterministic
  (`∀ s s₁ s₂ l, Tr s l s₁ → Tr s l s₂ → s₁ = s₂`).

## Lemmas proved

Projection bookkeeping:

- `projectTrace_eq_nil` — a trace with no `p`-observed label projects to `[]`.
- `projectTrace_concat_notMem` — projection of `t ++ [l]` when `p ∉ pn l`.
- `projectTrace_concat_mem` — projection of `t ++ [l]` when `p ∈ pn l`.

Commuting / alignment:

- `commute_or_matching` — an enabled action either matches a label of a
  `p`-unobserved trace, or commutes past all of it.
- `align_heads` — two distinct enabled transitions either match or have a diamond.
- `obs_match` — **distinct labels enabled at the same state and both observed by
  `p` must match** (follows from `u` together with `hpn₁`).
- `mtr_det` — determinism makes the end state a function of the label list.
- `mtr_split_last` — split a trace at its last step, keeping the prefix anchored
  at the original state.

Partial:

- `core` — the trichotomy for two traces from a common state. The last-element
  split, the induction hypothesis, and all sub-cases are done **except** the one
  described below.

## Two findings, both machine-checked

1. **The theorem was false before `d` was added.** `/tmp/cex.lean` holds a 5-state
   LTS satisfying every *old* `Smurf` axiom whose traces `[a, c]` and `[a, d]`
   violate the conclusion. Root cause: once `u` was restricted to `l₁ ≠ l₂`, the
   axioms no longer force the degenerate `matching a a` that the original proof
   relied on, so strictly more models were admitted. Determinism excludes this
   counterexample.
2. **`hpn₁` does a lot of the work.** An attempted product/grid counterexample
   fails precisely because two independent, both-observed labels at a common
   state contradict `hpn₁` (independence forces disjoint process sets, yet both
   contain `p`).

## The single remaining gap

Isolated to one shape:

> `l₁` is enabled at `u₁`, `l₂` at `u₂`, both observed by `p`, `l₁ ≠ l₂`, where
> `u₁`, `u₂` are reached from the common state `s` by traces with **equal
> projections**. Need: `B.matching l₁ l₂`.

`obs_match` does not apply directly — it requires both labels enabled at the
*same* state, and `u₁ ≠ u₂` is possible (they may differ by unobserved labels).
Determinism does not help either, since the labels differ.

Why the statement is nevertheless believed true: in the concrete instance
`s -c-> M -l₁-> A` and `s -d-> N -l₂-> B` with `c`, `d` unobserved, either
`matching c d` gives a witness at the prefix level, or `I c d` and the diamond
places `d` at `M` and `c` at `N`; `matching l₁ d` is then impossible (it would
force `pn l₁ = pn d = ∅` while `p ∈ pn l₁`), so `I l₁ d` and `I l₂ c`, and their
diamonds produce a common state where `l₁` and `l₂` are both enabled and both
observed — `obs_match` then yields `matching l₁ l₂`.

So the next concrete step is a single lemma: *align an observed action enabled
after an unobserved prefix, then apply `obs_match`*.

## Accompanying files

- `scripts/SmurfProofSketch.md` — the original proof sketch, plus a note on why
  the pre-irreflexivity argument no longer applies.
