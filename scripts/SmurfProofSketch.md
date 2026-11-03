# Proof sketch for `ifSmurfThenTraces`

Preserved from the in-file comments in `Cslib/Foundations/Concurrency/Smurf.lean`,
kept here for posterity before the theorem body was worked on.

The statement: for two traces `t₁`, `t₂` from the same state `s` and any process
`p`, either the projection of `t₁` on `p` is a prefix of that of `t₂`, or vice
versa, or the two traces diverge and there is a matching pair of labels witnessed
after prefixes whose projections on some process `q` agree.

## Original sketch

- proof by induction on combined length of `t₁` and `t₂`
- if either projection of the traces is empty, it is trivially a prefix of the
  other
- if both `t₁` and `t₂` are singletons, and neither of their projections is a
  prefix of the other, then they must be a matching pair (`Smurf.u`)
- otherwise, split the traces into a prefix trace and a final label
  (`t₁ = t₁' ++ l₁`, `t₂ = t₂' ++ l₂`); this is less convenient in Lean than
  splitting into head and suffix, but the induction hypothesis needs the prefix
  since it must apply to state `s` of the LTS
- apply the induction hypothesis to `t₁'` and `t₂'` to obtain one of three
  results:
  1. the projection of `t₁'` on `p` is a prefix of that of `t₂'`
  2. the projection of `t₂'` on `p` is a prefix of that of `t₁'`
  3. the two diverge and there is a witness
- in case 3) the witness also works for `t₁` and `t₂`, and the proof is done
- case 2) is symmetric to case 1), so it would make sense to extract both to a
  helper lemma
- the remainder covers case 1)
- if `p ∉ pn l₁` then the projection of `t₁` is equal to the projection of `t₁'`,
  which is a prefix of that of `t₂'`, which is a prefix of that of `t₂`, and we
  are done
- otherwise, find the longest common prefix `t₀` of `t₁` and `t₂`:
  `t₁ = t₀ ++ a₁ ++ a₂ ++ ... ++ aₙ ++ l₁` and
  `t₂ = t₀ ++ b₁ ++ b₂ ++ ... ++ bₘ ++ l₂`
- `a₁` and `b₁` are enabled in the same state, so from `Smurf.u` they are either
  independent or matching; in the latter case, we have found a witness that
  completes the proof
- if `a₁` and `b₁` are independent, then they can commute, and we can repeat the
  argument for `a₁` and `b₂`, ..., `a₁` and `l₂`, `a₂` and `b₁`, ...,
  `l₁` and `bₘ`
- either this process will at some point return a matching pair `aᵢ`, `bⱼ` that
  provides a witness, or all the `a`'s and `b`'s commute past `l₁` and `l₂`
- in the latter case, we can compare `l₁` and `l₂`: either they are independent
  --- and recall that `p ∈ pn l₁` --- in which case the projection of `t₂` on `p`
  is that of `t₀`, and is therefore a prefix of that of `t₁`, or `l₁` and `l₂`
  are a matching pair, which yields a witness with process `p`

## Note on irreflexivity

An earlier version of the proof exploited the fact that, with a permissive
`Branching`, the `Smurf.u` field could return `matching a a` for two occurrences
of the same label, which supplied a witness at degenerate positions. That is no
longer available: `Branching` now carries `[irrefl : Std.Irrefl matching]`, and
`Smurf.u` only applies to distinct labels `l₁ ≠ l₂`. Any revived argument must
therefore treat the "same label on both sides" situation by commuting past it
rather than by producing a matching witness.
