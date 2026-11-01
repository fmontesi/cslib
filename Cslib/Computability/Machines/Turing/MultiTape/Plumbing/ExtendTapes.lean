/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Data.Fintype.Inv
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# Extending a machine with additional work tapes

`extendTapes tm e`, for an embedding `e : Fin k ↪ Fin k'`, runs `tm` inside a machine with more
work tapes. The tapes selected by `e` are used by `tm`: target tape `e j` plays the role of source
tape `j`. The remaining tapes are left unchanged.

The configuration map `embed e cfg extraTapes extraPos` places `cfg` on the selected tapes and
initialises the remaining tapes from `extraTapes` and `extraPos`.

The configuration map is a homomorphism of step relations (`embedHom`), so each run path of `tm`
maps to a run path of the larger machine.

## Main definitions

* `Turing.MultiTapeTM.partialInv`: the partial inverse of the tape embedding.
* `Turing.MultiTapeTM.extendTapes`: the machine with reindexed work tapes.
* `Turing.MultiTapeTM.embed`: the corresponding configuration map.
* `Turing.MultiTapeTM.embedHom`: the configuration map as a step-preserving map, which maps run
  paths.
* `Turing.MultiTapeTM.tapeEmb`: the embedding placing the only tape of a one-tape machine on
  tape `i`, and `Turing.MultiTapeTM.noTapes`: the embedding of a machine without work tapes.

## Main results

* `Turing.MultiTapeTM.space_map_embedHom_le`: the space bound for a mapped path.
* `Turing.MultiTapeTM.oneTapeCfg`: the one-tape view of a configuration.
* `Turing.MultiTapeTM.runFrom_tapeEmb`: the run of a one-tape machine placed on work tape `i`.
* `Turing.MultiTapeTM.TransformsTapes.tapeEmb`: a one-tape specification, read on tape `i`.
* `Turing.MultiTapeTM.runFrom_noTapes`: the run of a machine without work tapes, placed in a machine
  with `k` of them.
-/

namespace Turing.MultiTapeTM

variable {k k' : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The computable analogue of `Function.partialInv` for an embedding `e`: `partialInv e l = some j`
when `e j = l` (such `j` is unique by injectivity), and `none` when `l` lies outside the range of
`e`. -/
@[expose] public def partialInv (e : Fin k ↪ Fin k') (l : Fin k') : Option (Fin k) :=
  if h : l ∈ Set.range e then some (e.invOfMemRange ⟨l, h⟩) else none

/-- `partialInv e` is a partial inverse of `e`. -/
public lemma partialInv_isPartialInv (e : Fin k ↪ Fin k') :
    Function.IsPartialInv e (partialInv e) := fun j l => by
  grind [partialInv, Function.Embedding.left_inv_of_invOfMemRange,
    Function.Embedding.right_inv_of_invOfMemRange]

/-- `tm` run on the tapes selected by the embedding `e`, leaving other tapes untouched: work tape
`e j` plays the role of `tm`'s tape `j`, and any tape outside `range e` is never written and never
moves. -/
@[expose] public noncomputable def extendTapes (tm : MultiTapeTM k Symbol State)
    (e : Fin k ↪ Fin k') : MultiTapeTM k' Symbol State :=
  tm.adapt
    { read := fun heads => ⟨heads.inputSymbol, heads.workTapeSymbols ∘ e⟩
      action := fun _ a =>
        { a with workTapes := fun l => match partialInv e l with
            | some j => a.workTapes j
            | none => (none, 0) } }

@[simp]
public lemma extendTapes_q₀ (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k') :
    (tm.extendTapes e).q₀ = tm.q₀ := rfl

/-- A configuration of `tm`, embedded: tape `j` goes to tape `e j`, the tapes outside `range e`
carry the given `extraTapes` contents and `extraPos` head positions. -/
@[expose] public def embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) :
    Cfg k' Symbol State input :=
  ⟨cfg.state, cfg.inputPos,
    fun l => match partialInv e l with
      | some j => cfg.workTapes j
      | none => extraTapes l,
    fun l => match partialInv e l with
      | some j => cfg.workTapePos j
      | none => extraPos l,
    cfg.output⟩

/-- The partial inverse recovers the source tape of an embedded tape. -/
@[simp]
public lemma partialInv_embed (e : Fin k ↪ Fin k') (j : Fin k) : partialInv e (e j) = some j :=
  (partialInv_isPartialInv e).eq j

/-- Outside the range of `e`, the partial inverse is undefined. -/
public lemma partialInv_eq_none (e : Fin k ↪ Fin k') {l : Fin k'} (hl : l ∉ Set.range e) :
    partialInv e l = none :=
  dite_eq_right hl

/-- If the partial inverse is `some j`, then `e j = l`. -/
public lemma partialInv_eq_some (e : Fin k ↪ Fin k') {l : Fin k'} {j : Fin k}
    (h : partialInv e l = some j) : e j = l :=
  (partialInv_isPartialInv e j l).mp h

@[simp]
public lemma embed_workTapes_embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) (j : Fin k) :
    (embed e cfg extraTapes extraPos).workTapes (e j) = cfg.workTapes j := by
  simp [embed]

@[simp]
public lemma embed_workTapePos_embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) (j : Fin k) :
    (embed e cfg extraTapes extraPos).workTapePos (e j) = cfg.workTapePos j := by
  simp [embed]

@[simp]
public lemma embed_workTapeSymbols_embed (e : Fin k ↪ Fin k') (cfg : Cfg k Symbol State input)
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) (j : Fin k) :
    (embed e cfg extraTapes extraPos).workTapeSymbols (e j) = cfg.workTapeSymbols j := by
  simp [Cfg.workTapeSymbols]

/-- `embed` as a homomorphism of step relations: each step `c → c'` of `tm` becomes the step
`embed c → embed c'` of the reindexed machine, so a run path of `tm` maps to a run path of the
reindexed machine, with the extra tapes held fixed. `Follows.stepHom` builds it, since `embed`
agrees with the adapter defining `extendTapes`. -/
@[expose, simps! apply] public noncomputable def embedHom (tm : MultiTapeTM k Symbol State)
    (e : Fin k ↪ Fin k') (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) :
    (tm.stepRel input).Hom ((tm.extendTapes e).stepRel input) :=
  follows_adapt.stepHom (embed e · extraTapes extraPos) (fun _ => Option.map_id_apply)
    (fun c => HeadSymbols.ext rfl (funext (embed_workTapeSymbols_embed e c extraTapes extraPos)))
    fun c a => by
      refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> simp only [Action.apply, embed] <;>
        cases partialInv e l <;> simp

section Space

/-- **Space bound for a reindexed path.** The embedded tapes visit what the original path visits,
while each of the remaining `k' - k` tapes never moves and contributes one cell. -/
public lemma space_map_embedHom_le (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (extraTapes : Fin k' → ℤ → Option Symbol) (extraPos : Fin k' → ℤ) (p : tm.RunPath input) :
    (p.map (embedHom tm e extraTapes extraPos)).space ≤ p.space + (k' - k) := by
  simpa [Finset.card_compl] using p.space_map_le _ e (fun l => {extraPos l})
    (fun c _ => embed_workTapePos_embed e c extraTapes extraPos)
    fun c _ l hl => by simp [embed, partialInv_eq_none e hl]

end Space

/-! ### Placing a one-tape machine on a single work tape -/

section OneTape

variable {k : ℕ}

/-- The embedding that places the only work tape of a one-tape machine on tape `i`. -/
@[expose] public def tapeEmb (i : Fin k) : Fin 1 ↪ Fin k :=
  ⟨fun _ => i, fun a b _ => Subsingleton.elim a b⟩

@[simp]
public lemma tapeEmb_apply (i : Fin k) (j : Fin 1) : tapeEmb i j = i := rfl

@[simp]
public lemma range_tapeEmb (i : Fin k) : Set.range (tapeEmb i) = {i} := by
  ext l
  simp [eq_comm]

/-- Tape `i` is the image of the only tape of a one-tape machine, and no other tape is. -/
@[simp]
public lemma partialInv_tapeEmb (i l : Fin k) :
    partialInv (tapeEmb i) l = if l = i then some 0 else none := by
  split_ifs with h
  · exact h ▸ partialInv_embed (tapeEmb i) 0
  · exact partialInv_eq_none _ (by simp [h])

/-- A one-tape configuration placed on tape `i` leaves every other tape as it was. -/
public lemma embed_tapeEmb (i : Fin k) (cfg : Cfg 1 Symbol State input)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ) :
    embed (tapeEmb i) cfg tapes heads =
      ⟨cfg.state, cfg.inputPos, Function.update tapes i (cfg.workTapes 0),
        Function.update heads i (cfg.workTapePos 0), cfg.output⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> by_cases hl : l = i <;> simp [embed, hl]

/-- The one-tape view of a configuration of a machine with `k` work tapes: the tape and head of
tape `i`, with everything else as it is. -/
@[expose] public def oneTapeCfg (i : Fin k) (cfg : Cfg k Symbol State input) :
    Cfg 1 Symbol State input :=
  ⟨cfg.state, cfg.inputPos, fun _ => cfg.workTapes i, fun _ => cfg.workTapePos i, cfg.output⟩

/-- A configuration is its own one-tape view on tape `i`, placed back on tape `i`. -/
public lemma embed_oneTapeCfg (i : Fin k) (cfg : Cfg k Symbol State input) :
    embed (tapeEmb i) (oneTapeCfg i cfg) cfg.workTapes cfg.workTapePos = cfg := by
  rw [embed_tapeEmb]
  simp [oneTapeCfg]

/-- **Running a one-tape machine on work tape `i`.** The run is the run on the one-tape view of the
configuration, placed back on tape `i`; every other tape and head keeps its starting value. Combine
with `embed_tapeEmb` to read off the resulting configuration. -/
public lemma runFrom_tapeEmb (tm : MultiTapeTM 1 Symbol State) (i : Fin k)
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    (tm.extendTapes (tapeEmb i)).runFrom cfg n =
      embed (tapeEmb i) (tm.runFrom (oneTapeCfg i cfg) n) cfg.workTapes cfg.workTapePos := by
  rw [← embedHom_apply tm, ← runFrom_map, embedHom_apply, embed_oneTapeCfg]

/-- **A one-tape specification on tape `i`.** A one-tape machine placed on tape `i` transforms the
word on that tape as it did on its own tape and leaves every other word alone; each remaining tape
costs one cell. -/
public theorem TransformsTapes.tapeEmb {tm : MultiTapeTM 1 Symbol State}
    {P : (input : List Symbol) → (Fin 1 → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin 1 → List Symbol) → (Fin 1 → List Symbol) →
      List Symbol → Prop} {t s : ℕ}
    (h : TransformsTapes tm P Q t s) (i : Fin k) :
    TransformsTapes (tm.extendTapes (MultiTapeTM.tapeEmb i))
      (fun input ws => P input fun _ => ws i)
      (fun input ws ws' emitted =>
        ∃ v, Q input (fun _ => ws i) v emitted ∧ ws' = Function.update ws i (v 0))
      t (s + (k - 1)) := by
  intro input ws out hP
  obtain ⟨v, emitted, hQ, p, hhead, hlast, htime, hspace⟩ := h input (fun _ => ws i) out hP
  -- the path of the placed machine is the one-tape path, placed on tape `i`
  have hplace (q : Option State) (v : Fin 1 → List Symbol) (o : List Symbol) :
      embed (MultiTapeTM.tapeEmb i) (wordsCfg input q v o) (fun l => tapeOfList (ws l))
        (fun _ => 0) = wordsCfg input q (Function.update ws i (v 0)) o := by
    rw [embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> by_cases hl : l = i <;> simp [hl, wordsCfg]
  exact ⟨Function.update ws i (v 0), emitted, ⟨v, hQ, rfl⟩,
    p.map (embedHom tm (MultiTapeTM.tapeEmb i) (fun l => tapeOfList (ws l)) fun _ => 0),
    by simp [hhead, hplace], by simp [hlast, hplace], htime,
    (space_map_embedHom_le ..).trans (Nat.add_le_add_right hspace _)⟩

end OneTape

section NoTapes

variable {k : ℕ}

/-- The embedding of a machine without work tapes into a machine with `k` of them. -/
@[expose] public def noTapes (k : ℕ) : Fin 0 ↪ Fin k := ⟨Fin.elim0, fun a => a.elim0⟩

/-- No tape is in the range of `noTapes`. -/
@[simp]
public lemma partialInv_noTapes (l : Fin k) : partialInv (noTapes k) l = none :=
  partialInv_eq_none _ (by simp)

/-- The view of a configuration as a configuration of a machine without work tapes. -/
@[expose] public def noTapesCfg (cfg : Cfg k Symbol State input) : Cfg 0 Symbol State input :=
  ⟨cfg.state, cfg.inputPos, nofun, nofun, cfg.output⟩

/-- A configuration without work tapes, placed in a machine with `k` of them, only contributes its
state, its input head and its output. -/
public lemma embed_noTapes (cfg : Cfg 0 Symbol State input)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ) :
    embed (noTapes k) cfg tapes heads = ⟨cfg.state, cfg.inputPos, tapes, heads, cfg.output⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> simp [embed]

/-- A configuration is its tapeless view, placed back on its tapes. -/
public lemma embed_noTapesCfg (cfg : Cfg k Symbol State input) :
    embed (noTapes k) (noTapesCfg cfg) cfg.workTapes cfg.workTapePos = cfg := by
  rw [embed_noTapes]
  rfl

/-- **Running a machine without work tapes inside a machine with `k` of them.** Only the state, the
input head and the output change; every work tape and work head keeps its starting value. -/
public lemma runFrom_noTapes (tm : MultiTapeTM 0 Symbol State) (cfg : Cfg k Symbol State input)
    (n : ℕ) :
    (tm.extendTapes (noTapes k)).runFrom cfg n =
      ⟨(tm.runFrom (noTapesCfg cfg) n).state, (tm.runFrom (noTapesCfg cfg) n).inputPos,
        cfg.workTapes, cfg.workTapePos, (tm.runFrom (noTapesCfg cfg) n).output⟩ := by
  rw [← embed_noTapes, ← embedHom_apply tm, ← runFrom_map, embedHom_apply, embed_noTapesCfg]

end NoTapes

end Turing.MultiTapeTM
