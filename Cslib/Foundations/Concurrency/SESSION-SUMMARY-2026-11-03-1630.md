# Session summary — `Smurf.lean` (2026-11-03 16:30:51 CET)

**File under work:** `Cslib/Foundations/Concurrency/Smurf.lean`
**Status:** compiles with **0 errors**, **1 `sorry`** remaining (down from 6).
**Axioms/definitions:** unchanged this session.

---

## Result

`ifSmurfThenTraces` is now **fully proved** (no `sorry` in the theorem).
Its proof applies the helper `core`:

```lean
intro s t₁ t₂ p ht
obtain ⟨h₁, h₂⟩ := ht
obtain ⟨s₁, hm₁⟩ := h₁
obtain ⟨s₂, hm₂⟩ := h₂
exact core h hpn₁ hpn₂ hm₁ hm₂
```

`core` itself is proved except for one isolated lemma, `core_branch`
(the only remaining `sorry`, around line 169).

## Proof restructuring in `core`

The proof splits both traces at their last label and inducts on the combined
length (as before), but the case analysis was reorganised:

1. **Prefix projections differ.** Instead of trying to align states, apply the
   induction hypothesis to the smaller pair `(t₁, t₂')` (resp. `(t₁', t₂)`).
   The extra observed label must be the last element of the projection
   difference, so the result is always a prefix relation or a lifting witness.
   This removed the old `R = x :: …` and `R = _ :: _ :: _` gaps.
2. **Prefix projections equal.** Split on whether the final labels were observed
   by `p`:
   - equal final labels → projections equal (`Or.inl`);
   - an unobserved final label → one projection is a prefix of the other;
   - both final labels observed and distinct → the isolated branching case
     `core_branch`.

## New helper lemmas (all proved)

- `prefix_cancel_left`: `C ++ X <+: C ++ Y → X <+: Y`.
- `eq_of_prefix_singleton`: a nonempty prefix of `[x]` is `[x]`.
- `projectTrace_prefix_concat`: `P(t) <+: P(t ++ [l])`.
- `omit [DecidableEq Pid] in` added on `obs_match` to silence the unused
  section variable linter warning.

## The remaining gap: `core_branch`

Statement: given `MTr s t₁' u₁`, `MTr s t₂' u₂` with
`P(t₁') = P(t₂')`, and distinct final labels `l₁`, `l₂` observed by `p`
(`Tr u₁ l₁ s₁`, `Tr u₂ l₂ s₂`), there is a matching witness with equal
`q`-projections of prefixes in `t₁' ++ [l₁]` and `t₂' ++ [l₂]`.

**Warning:** the earlier conjecture that this forces `B.matching l₁ l₂` is
**false**. Countermodel: `s -x-> M -a->` and `s -y-> N -b->` with `matching x y`
(both unobserved by `p`) and `a`, `b` observed and distinct. Then
`P(t₁) = [a]`, `P(t₂) = [b]`, but only `x`/`y` match; the witness is at the
empty prefixes. The correct conclusion is the existential witness now stated in
`core_branch`.

**Proof idea for the next session.** A grid/alignment induction: at each step
the two next labels enabled at a common state are (by `Smurf.u`) either
matching (witness) or independent. Independent pairs have disjoint participant
sets (`hpn₁`), so at most one is `p`-observed; observed labels commute past
unobserved ones (matching would violate `hpn₂`), and equal labels advance both
traces by determinism. This needs a state-based induction carrying the two
executions and their consumed prefixes. The unused `commute_or_matching` lemma
is close to the needed tool, but its `hne : ∀ b, a = b → False` hypothesis is
too strong; it only needs `a ≠` the head of the remaining trace (derivable from
`p ∈ pn a` and the empty projection).

A randomized model search (Python, 3–4 states, up to 5 labels, 500k trials)
found no counterexample to the theorem.

## Build / validation

- `lake env lean Cslib/Foundations/Concurrency/Smurf.lean` — succeeds.
- `lake build Cslib.Foundations.Concurrency.Smurf` — succeeds, with the single
  `sorry` warning for `core_branch`.
- `lake build --wfail --iofail` will fail until `core_branch` is finished.
- No new files were added under `Cslib/`, so `lake exe mk_all` is not needed.
