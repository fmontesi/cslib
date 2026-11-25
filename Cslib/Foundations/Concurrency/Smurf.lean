/-
Copyright (c) 2026 Luc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luc
-/

module

public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Foundations.Concurrency.Basic
import Cslib.Foundations.Relation.Confluence
import Mathlib.Data.List.Basic

/-! Luc's playground
  With help from DeepSeek-V4.1-Flash-1017.
-/

@[expose] public section

namespace Cslib.Concurrency

/-- Placeholder for the alphabet sanity condition. Currently every label type satisfies it. -/
def SaneAlphabet (_ : Type*) : Prop :=
  true

/-- Conditional labels and the symmetric relation pairing alternative branches. -/
structure Branching (α : Type*) where
  /-- Whether a label denotes a conditional branch. -/
  conditional : α → Prop
  /-- Whether two labels denote alternative branches of the same conditional. -/
  matching : α → α → Prop
  [symm : Std.Symm matching]
  [irrefl : Std.Irrefl matching]
  [functional : ∀ a b c, matching a b → matching a c → b = c]
  [matchcond : ∀ a b, matching a b → conditional a ∧ conditional b]

attribute [instance] Branching.symm

variable {State Label : Type*}

/-- A deterministic LTS with paired conditional branches, where independent steps commute
and distinct enabled labels are independent or matching. -/
structure Smurf (lts : LTS State Label) (I : Label → Label → Prop) [Independence I]
    (B : Branching Label) where
  -- labelling alphabet should be sane
  s : SaneAlphabet Label
  -- conditionals should come in matching sets
  m : ∀ s s₁ l₁, B.conditional l₁ ∧ lts.Tr s l₁ s₁ →
    ∃ l₂ s₂, B.matching l₁ l₂ ∧ lts.Tr s l₂ s₂
  -- no local concurrency
  -- distinct pairs of outgoing transitions are either independent or part of a matching set
  u : ∀ s s₁ s₂ l₁ l₂, l₁ ≠ l₂ → lts.Tr s l₁ s₁ ∧ lts.Tr s l₂ s₂ →
    I l₁ l₂ ∨ B.matching l₁ l₂
  -- backward concurrency
  r : ∀ s s₁ l₁ l₂, I l₁ l₂ ∧ lts.MTr s [l₁, l₂] s₁ →
    ∃ s₂, lts.Tr s l₂ s₂
  -- forward concurrency (diamond)
  f : ∀ s s₁ s₂ l₁ l₂, I l₁ l₂ ∧ lts.Tr s l₁ s₁ ∧ lts.Tr s l₂ s₂ →
    ∃ s₃, lts.Tr s₁ l₂ s₃ ∧ lts.Tr s₂ l₁ s₃
  -- the LTS is deterministic
  d : ∀ s s₁ s₂ l, lts.Tr s l s₁ → lts.Tr s l s₂ → s₁ = s₂

/-- `Smurf` is a `Prop`-valued structure, hence it is the conjunction of its six fields.  This
characterisation exposes the fields to type class search, which cannot look inside a structure,
and is what makes `Smurf.decidableSmurf` possible. -/
theorem Smurf_iff {lts : LTS State Label} {I : Label → Label → Prop} [Independence I]
    {B : Branching Label} :
    Smurf lts I B ↔
      SaneAlphabet Label ∧
      (∀ s s₁ l₁, B.conditional l₁ ∧ lts.Tr s l₁ s₁ →
        ∃ l₂ s₂, B.matching l₁ l₂ ∧ lts.Tr s l₂ s₂) ∧
      (∀ s s₁ s₂ l₁ l₂, l₁ ≠ l₂ → lts.Tr s l₁ s₁ ∧ lts.Tr s l₂ s₂ →
        I l₁ l₂ ∨ B.matching l₁ l₂) ∧
      (∀ s s₁ l₁ l₂, I l₁ l₂ ∧ lts.MTr s [l₁, l₂] s₁ →
        ∃ s₂, lts.Tr s l₂ s₂) ∧
      (∀ s s₁ s₂ l₁ l₂, I l₁ l₂ ∧ lts.Tr s l₁ s₁ ∧ lts.Tr s l₂ s₂ →
        ∃ s₃, lts.Tr s₁ l₂ s₃ ∧ lts.Tr s₂ l₁ s₃) ∧
      (∀ s s₁ s₂ l, lts.Tr s l s₁ → lts.Tr s l s₂ → s₁ = s₂) := by
  refine ⟨fun h => ⟨h.s, h.m, h.u, h.r, h.f, h.d⟩, ?_⟩
  rintro ⟨s, m, u, r, f, d⟩
  exact ⟨s, m, u, r, f, d⟩

/-- `SaneAlphabet` is a `def` for `True`, but instance search does not unfold it. -/
instance instDecidableSaneAlphabet : Decidable (SaneAlphabet Label) :=
  decidable_of_iff True (by simp [SaneAlphabet])

/-- Multistep transitions are decidable when states are finite and single steps are, since the
intermediate states of the existential in `LTS.MTr.cons_iff` can be enumerated.  This is also
useful beyond `Smurf`: it makes the fields about `LTS.MTr` decidable. -/
instance decidableMTr {lts : LTS State Label} [Fintype State] [DecidableEq State]
    [∀ (s : State) (l : Label) (s' : State), Decidable (lts.Tr s l s')] :
    ∀ (u : List Label) (s t : State), Decidable (lts.MTr s u t) := by
  intro u
  induction u with
  | nil =>
    exact fun s t => decidable_of_iff (s = t) (LTS.MTr.nil_iff (lts := lts) s t).symm
  | cons a u _ =>
    exact fun s t =>
      decidable_of_iff (∃ s', lts.Tr s a s' ∧ lts.MTr s' u t) LTS.MTr.cons_iff.symm

/-- Membership in `Smurf` is decidable, provided states and labels are finite and the transition
relation, `I`, `B.conditional`, and `B.matching` are decidable.

The `haveI` binders keep each field's instance search small: asking for all six fields at once
exceeds the default size limit of type class search, since the last fields need `DecidableEq` on
states and `Decidable` multistep transitions in their local context.

On a concrete system, `decide` then evaluates the membership question by computation. -/
instance decidableSmurf {lts : LTS State Label} {I : Label → Label → Prop} [Independence I]
    {B : Branching Label} [Fintype State] [DecidableEq State] [Fintype Label] [DecidableEq Label]
    [∀ (s : State) (l : Label) (s' : State), Decidable (lts.Tr s l s')]
    [DecidableRel I] [DecidablePred B.conditional] [DecidableRel B.matching] :
    Decidable (Smurf lts I B) := by
  haveI : Decidable (∀ s s₁ l₁, B.conditional l₁ ∧ lts.Tr s l₁ s₁ →
      ∃ l₂ s₂, B.matching l₁ l₂ ∧ lts.Tr s l₂ s₂) := inferInstance
  haveI : Decidable (∀ s s₁ s₂ l₁ l₂, l₁ ≠ l₂ → lts.Tr s l₁ s₁ ∧ lts.Tr s l₂ s₂ →
      I l₁ l₂ ∨ B.matching l₁ l₂) := inferInstance
  haveI : Decidable (∀ s s₁ l₁ l₂, I l₁ l₂ ∧ lts.MTr s [l₁, l₂] s₁ →
      ∃ s₂, lts.Tr s l₂ s₂) := inferInstance
  haveI : Decidable (∀ s s₁ s₂ l₁ l₂, I l₁ l₂ ∧ lts.Tr s l₁ s₁ ∧ lts.Tr s l₂ s₂ →
      ∃ s₃, lts.Tr s₁ l₂ s₃ ∧ lts.Tr s₂ l₁ s₃) := inferInstance
  haveI : Decidable (∀ s s₁ s₂ l, lts.Tr s l s₁ → lts.Tr s l s₂ → s₁ = s₂) := inferInstance
  exact decidable_of_iff' _ Smurf_iff

variable {Pid : Type*} [DecidableEq Pid]

/-- Project a trace onto process `p` by retaining, in order, the labels in which it participates. -/
def ProjectTrace {pn : Label → Finset Pid} (lst : List Label) (p : Pid) : List Label :=
  lst.filter (fun l => decide (p ∈ pn l))

/-- Split a trace at its last step; the prefix still starts at the original state. -/
lemma mtr_split_last
    {s s' : State}
    {l : List Label}
    {a : Label}
    {lts : LTS State Label}
    (h : lts.MTr s (l ++ [a]) s')
  : ∃ sm, lts.MTr s l sm ∧ lts.Tr sm a s'
  := by
    obtain ⟨sm, h1, h2⟩ := LTS.MTr.split h
    exact ⟨sm, h1, LTS.MTr.single_invert lts _ _ _ h2⟩

section Helpers

variable {pn : Label → Finset Pid} {lts : LTS State Label}
  {I : Label → Label → Prop} [Independence I] {B : Branching Label}
  {hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂)}
  {hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → pn l₁ = pn l₂}

/-- If `p` does not observe any label of `u`, then `u` projects to the empty trace. -/
private lemma projectTrace_eq_nil {u : List Label} {p : Pid}
    (h : ∀ l ∈ u, p ∉ pn l) : ProjectTrace (pn := pn) u p = [] := by
  induction u with
  | nil => rfl
  | cons a t ih =>
    have ha : p ∉ pn a := h a (by simp)
    have ht : ProjectTrace (pn := pn) t p = [] :=
      ih (fun l hl => h l (by simp [hl]))
    rw [ProjectTrace, List.filter_cons, decide_eq_false ha]
    exact ht

/-! ### Trace equivalence

Independent adjacent labels can be exchanged inside an execution, using backward
concurrency (`Smurf.r`) to bring the second one forward, forward concurrency
(`Smurf.f`) to compare the two orders, and determinism (`Smurf.d`) to identify the
targets.  Consequently an execution is determined by its *trace*, i.e. by its label
list up to `List.PermUpTo I`. -/

omit [DecidableEq Pid] in
/-- Adjacent independent labels can be exchanged inside an execution. -/
private lemma mtr_swap_indep (h : Smurf lts I B) {a b : Label} (hab : I a b)
    {α γ : List Label} {s t : State} (hm : lts.MTr s (α ++ a :: b :: γ) t) :
    lts.MTr s (α ++ b :: a :: γ) t := by
  obtain ⟨s₁, hα, hm'⟩ := LTS.MTr.split hm
  obtain ⟨s₂, htra, hm''⟩ := LTS.MTr.cons_iff.mp hm'
  obtain ⟨s₃, htrb, hγ⟩ := LTS.MTr.cons_iff.mp hm''
  -- `b` is available before `a`
  have h2 : lts.MTr s₁ [a, b] s₃ := .stepL htra (.stepL htrb .refl)
  obtain ⟨s₂', htrb'⟩ := h.r s₁ s₃ a b ⟨hab, h2⟩
  -- the forward diamond compares the two orders
  obtain ⟨s₃', hb, ha⟩ := h.f s₁ s₂ s₂' a b ⟨hab, htra, htrb'⟩
  have hEq : s₃' = s₃ := h.d s₂ s₃' s₃ b hb htrb
  subst hEq
  exact LTS.MTr.comp lts hα (.stepL htrb' (.stepL ha hγ))

omit [DecidableEq Pid] in
/-- Executions are determined by their trace: `List.PermUpTo I`-equivalent label lists
describe executions between the same two states. -/
lemma mtr_permUpTo (h : Smurf lts I B) {u v : List Label}
    (hp : List.PermUpTo I u v) :
    ∀ {s t : State}, lts.MTr s u t → lts.MTr s v t := by
  induction hp with
  | nil => exact fun hm => hm
  | cons a _ ih =>
    intro s t hm
    obtain ⟨s₁, htr, hm'⟩ := LTS.MTr.cons_iff.mp hm
    exact .stepL htr (ih hm')
  | swap a b w hI =>
    intro s t hm
    have hab : I a b := hI.elim id (fun hba => Std.Symm.symm (r := I) (a := b) (b := a) hba)
    exact mtr_swap_indep h hab (α := []) (γ := w) hm
  | trans _ _ ih₁ ih₂ => exact fun hm => ih₂ (ih₁ hm)

-- diamond extended to label and trace
-- l commutes past t
lemma diamond_label_trace
    {lts : LTS State Label}
    {I : Label → Label → Prop}
    [Independence I]
    {B : Branching Label}
    (h : Smurf lts I B)
    (l : Label)
    (t : List Label)
    (s sₗ sₜ : State)
    (hl : lts.Tr s l sₗ)
    (ht : lts.MTr s t sₜ)
    (hind : ∀ a ∈ t, I a l)
  : ∃ sₗₜ, lts.MTr sₗ t sₗₜ
  := by
    induction t generalizing s sₗ sₜ with
    | nil => exact ⟨sₗ, .refl⟩
    | cons a t' ih =>
      obtain ⟨s₁, ha, ht'⟩ := LTS.MTr.cons_iff.mp ht
      have ha_ind : I a l := hind a List.mem_cons_self
      obtain ⟨s₂, hl₁, ha₂⟩ := h.f s s₁ sₗ a l ⟨ha_ind, ha, hl⟩
      obtain ⟨sₗₜ, htail⟩ := ih s₁ s₂ sₜ hl₁ ht' fun m hm => hind m (List.mem_cons_of_mem a hm)
      exact ⟨sₗₜ, .stepL ha₂ htail⟩

/-- Move a label across an independent prefix while preserving the suffix. -/
lemma permUpTo_move_front {I : Label → Label → Prop} {a : Label} {u : List Label}
    (v : List Label) (hind : ∀ b ∈ u, I b a) :
    List.PermUpTo I (u ++ a :: v) (a :: (u ++ v)) := by
  induction u with
  | nil => exact .refl _
  | cons b u ih =>
    exact (List.PermUpTo.cons b (ih fun c hc => hind c (List.mem_cons_of_mem b hc))).trans
      (.swap b a _ (Or.inl (hind b List.mem_cons_self)))

/-- Swap two blocks of pairwise independent labels. -/
lemma permUpTo_append_comm {I : Label → Label → Prop} [Independence I] :
    ∀ u v : List Label,
      (∀ a ∈ u, ∀ b ∈ v, I a b) → List.PermUpTo I (u ++ v) (v ++ u) := by
  intro u v hind
  induction u with
  | nil => simp [List.PermUpTo.refl]
  | cons a u ih =>
    have tail := ih (fun b hb => hind b (List.mem_cons_of_mem a hb))
    have move := permUpTo_move_front u
      (fun b hb => Std.Symm.symm a b (hind a List.mem_cons_self b hb))
    exact (List.PermUpTo.cons a tail).trans move.symm

omit [DecidableEq Pid] in
/-- An enabled action either commutes with the whole target, or meets an equal or matching
label after a prefix independent of it. -/
lemma enabled_trace_cases (h : Smurf lts I B) {s sa t : State} {a : Label}
    -- `a` and `w` are both enabled at `s`
    {w : List Label} (ha : lts.Tr s a sa) (hw : lts.MTr s w t) :
    -- either `a` is independent of `w`, or `w` has an independent prefix with the next label
    -- being either equal to or matching with `a`
    (∀ b ∈ w, I a b) ∨ ∃ p b r, w = p ++ b :: r ∧
      (∀ c ∈ p, I a c) ∧ (a = b ∨ B.matching a b) := by
  classical
  -- by induction on `w`
  induction w generalizing s sa with
  -- empty `w` is trivial
  | nil => exact Or.inl (by simp)
  -- otherwise deconstruct `w` into `b :: w`
  | cons b w ih =>
    obtain ⟨sb, hb, hw⟩ := LTS.MTr.cons_iff.mp hw
    by_cases hab : I a b
    -- if `a` is independent of `b`
    · obtain ⟨sab, _, ha'⟩ := h.f s sa sb a b ⟨hab, ha, hb⟩
      -- commute by diamond, then apply induction hypothesis to `a` and tail `w`
      rcases ih ha' hw with hind | ⟨p, c, r, heq, hind, hlast⟩
      -- if these are independent, then so are `a` and `b :: w`
      · exact Or.inl (by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hab hind)
      -- else, it provides a witness that also holds for `b :: w`
      · refine Or.inr ⟨b :: p, c, r, ?_, ?_, hlast⟩
        · simp only [heq, List.cons_append]
        · simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hab hind
    -- if `a` and `b` are not independent, then they provide a witness immediately
    · refine Or.inr ⟨[], b, w, rfl, by simp, ?_⟩
      by_cases heq : a = b
      · exact Or.inl heq
      · exact Or.inr ((h.u s sa sb a b heq ⟨ha, hb⟩).resolve_left hab)

-- two traces from the same state will either fully commute, or result in a match or an equality
omit [DecidableEq Pid] in
private lemma commute_or_matcheq
    {lts : LTS State Label}
    {I : Label → Label → Prop}
    [Independence I]
    {B : Branching Label}
    (h : Smurf lts I B)
    -- plus a concrete state and two traces
    (s s₁ s₂ : State)
    (t₁ t₂ : List Label)
    (ht₁ : lts.MTr s t₁ s₁) (ht₂ : lts.MTr s t₂ s₂)
  :
  (∀ a ∈ t₁, ∀ b ∈ t₂, I a b)
  ∨ ∃ (u₁ u₂ : List Label) (a b : Label) (v₁ v₂ : List Label),
      t₁ = u₁ ++ a :: v₁
    ∧ t₂ = u₂ ++ b :: v₂
    ∧ (B.matching a b ∨ a = b)
    ∧ (∀ y ∈ u₂, I a y)
    ∧ (∀ x ∈ u₁, I x b)
  := by
    induction t₁ generalizing s s₂ with
    | nil => exact Or.inl (by simp)
    | cons a t₁ ih =>
      obtain ⟨sa, ha, ht₁⟩ := LTS.MTr.cons_iff.mp ht₁
      rcases enabled_trace_cases h ha ht₂ with hind | ⟨u, b, v, heq, hind, hm⟩
      · -- The whole second trace can still run after a, so compare it with the tail.
        obtain ⟨sa₂, ht₂'⟩ := diamond_label_trace h a t₂ s sa s₂ ha ht₂
          (fun b hb => Std.Symm.symm a b (hind b hb))
        rcases ih sa sa₂ ht₁ ht₂' with htail | ⟨u, u₂, x, y, v, v₂, rfl, rfl, hm, hl, hr⟩
        · exact Or.inl (by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hind htail)
        · refine Or.inr ⟨a :: u, u₂, x, y, v, v₂, rfl, rfl, hm, hl, ?_⟩
          simpa only [List.mem_cons, forall_eq_or_imp] using And.intro (hind y (by simp)) hr
      · exact Or.inr ⟨[], u, a, b, t₁, v, rfl, heq, hm.symm, hind, by simp⟩

-- PermUpTo preserves equivalence of projections
private lemma permupto_equiv_proj
    {pn : Label → Finset Pid}
    (I : Label → Label → Prop)
    [Independence I]
    (hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂))
  :
    ∀ (t₁ t₂ : List Label) (p : Pid),
    List.PermUpTo I t₁ t₂ → ProjectTrace (pn := pn) t₁ p = ProjectTrace (pn := pn) t₂ p
  := by
    intro t₁ t₂ p hp
    -- independence ensures that `p` observes at most one label of an independent pair,
    -- so swapping such a pair does not change the projection
    induction hp with
    | nil => rfl
    | cons a _ ih =>
      simp only [ProjectTrace, List.filter_cons] at ih ⊢
      rw [ih]
    | swap a b w hI =>
      have hind : I a b := hI.elim id fun h => Std.Symm.symm (r := I) (a := b) (b := a) h
      simp only [ProjectTrace, List.filter_cons]
      by_cases ha : p ∈ pn a
      · have hb : p ∉ pn b := fun hb => Finset.disjoint_left.mp (hpn₁ a b hind) ha hb
        simp [ha, hb]
      · by_cases hb : p ∈ pn b
        · simp [ha, hb]
        · simp [ha, hb]
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

-- helper lemma for the prefix case, using PermUpTo to shift equal labels to the front
private lemma prefix_or_projected_match
    {pn : Label → Finset Pid}
    {lts : LTS State Label}
    {I : Label → Label → Prop}
    [Independence I]
    {B : Branching Label}
    (hpn₀ : ∀ l, (pn l).Nonempty)
    (hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂))
    (hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → (pn l₁) = (pn l₂))
    (h : Smurf lts I B)
  : ∀ (s s₁ s₂ : State) (t₁ t₂ : List Label) (p : Pid),
  (lts.MTr s t₁ s₁ ∧ lts.MTr s t₂ s₂) →
  (
    ProjectTrace (pn := pn) t₁ p <+: ProjectTrace (pn := pn) t₂ p
    ∨
    ProjectTrace (pn := pn) t₂ p <+: ProjectTrace (pn := pn) t₁ p
    ∨
    (
      ∃ (q : Pid) (u : List Label) (a b : Label) (v₁ v₂ : List Label),
        ProjectTrace (pn := pn) t₁ q = u ++ a :: v₁ ∧
        ProjectTrace (pn := pn) t₂ q = u ++ b :: v₂ ∧ B.matching a b
    )
  )
  := by
    intro s s₁ s₂ t₁ t₂ p
    -- induction on combined length of t₁ and t₂
    induction hn : t₁.length + t₂.length using Nat.strong_induction_on generalizing
        s s₁ s₂ t₁ t₂ p with
    | _ n ih =>
      intro hm
      -- base case: both traces are empty, so both projections are empty
      rcases n with _ | n
      · obtain rfl : t₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
        obtain rfl : t₂ = [] := List.eq_nil_of_length_eq_zero (by omega)
        exact Or.inl (by simp [ProjectTrace])
      -- induction case
      -- apply commute_or_matcheq: either t₁ and t₂ commute, or they hit a match or equivalence
      rcases commute_or_matcheq h s s₁ s₂ t₁ t₂ hm.left hm.right with
        hcom | ⟨u₁, u₂, x₁, x₂, v₁, v₂, ht₁, ht₂, hmeq, hind₂, hind₃⟩
      -- if the two commute, then one of the two projections will be a prefix of the other
      · -- one of the two projections must be empty
        by_cases h₁ : ProjectTrace (pn := pn) t₁ p = []
        · rw [h₁]
          exact Or.inl List.nil_prefix
        · refine Or.inr (Or.inl ?_)
          -- some label of `t₁` is observed by `p`
          obtain ⟨a, ha, hap⟩ : ∃ a ∈ t₁, p ∈ pn a := by
            by_contra hcon
            exact h₁ (projectTrace_eq_nil fun l hl hpl => hcon ⟨l, hl, hpl⟩)
          -- full commutation makes every label of `t₂` unobserved by `p`
          have h₂ : ProjectTrace (pn := pn) t₂ p = [] :=
            projectTrace_eq_nil fun b hb hpb =>
              Finset.disjoint_left.mp (hpn₁ a b (hcom a ha b hb)) hap hpb
          rw [h₂]
          exact List.nil_prefix
      -- otherwise, distinguish between match and equality
      rcases hmeq with hmatch | heq
      -- if match, then this provides a witness: a process observing the
      -- matching labels observes neither prefix
      · obtain ⟨q, hq⟩ := hpn₀ x₁
        have hqx₂ : q ∈ pn x₂ := (hpn₂ x₁ x₂ hmatch) ▸ hq
        have hu₁nil : ProjectTrace (pn := pn) u₁ q = [] :=
          projectTrace_eq_nil fun x hx hqx =>
            Finset.disjoint_left.mp (hpn₁ x x₂ (hind₃ x hx)) hqx hqx₂
        have hu₂nil : ProjectTrace (pn := pn) u₂ q = [] :=
          projectTrace_eq_nil fun y hy hqy =>
            Finset.disjoint_left.mp (hpn₁ x₁ y (hind₂ y hy)) hq hqy
        refine Or.inr (Or.inr ⟨q, [], x₁, x₂, ProjectTrace (pn := pn) v₁ q,
          ProjectTrace (pn := pn) v₂ q, ?_, ?_, hmatch⟩)
        · simpa [ht₁, ProjectTrace, List.filter_append, hq] using
            congrArg (· ++ x₁ :: ProjectTrace (pn := pn) v₁ q) hu₁nil
        · simpa [ht₂, ProjectTrace, List.filter_append, hqx₂] using
            congrArg (· ++ x₂ :: ProjectTrace (pn := pn) v₂ q) hu₂nil
      subst x₂
      have hp₁ : List.PermUpTo I t₁ (x₁ :: (u₁ ++ v₁)) := ht₁ ▸ permUpTo_move_front v₁ hind₃
      have hp₂ : List.PermUpTo I t₂ (x₁ :: (u₂ ++ v₂)) :=
        ht₂ ▸ permUpTo_move_front v₂ (fun b hb => Std.Symm.symm _ _ (hind₂ b hb))
      have proj_cons (t u : List Label) (q : Pid) (hp : List.PermUpTo I t (x₁ :: u)) :
          ProjectTrace (pn := pn) t q = (if q ∈ pn x₁ then [x₁] else []) ++
            ProjectTrace (pn := pn) u q := by
        rw [permupto_equiv_proj I hpn₁ _ _ q hp]
        by_cases hx : q ∈ pn x₁ <;> simp [ProjectTrace, hx]
      -- move the shared label to the front of both traces
      have ⟨sₓ, hx, hx₁, hx₂⟩ : ∃ sₓ, lts.Tr s x₁ sₓ
          ∧ lts.MTr sₓ (u₁ ++ v₁) s₁ ∧ lts.MTr sₓ (u₂ ++ v₂) s₂ := by
        obtain ⟨sₓ, hx, hx₁⟩ := LTS.MTr.cons_iff.mp (mtr_permUpTo h hp₁ hm.left)
        obtain ⟨sₓ', hx', hx₂⟩ := LTS.MTr.cons_iff.mp (mtr_permUpTo h hp₂ hm.right)
        rw [← h.d s sₓ sₓ' x₁ hx hx'] at hx₂
        exact ⟨sₓ, hx, hx₁, hx₂⟩
      -- apply induction hypothesis to now shorter tails u₁ ++ v₁, u₂ ++ v₂
      have hlen : (u₁ ++ v₁).length + (u₂ ++ v₂).length < n + 1 := by
        simp only [ht₁, ht₂, List.length_cons, List.length_append] at hn ⊢
        omega
      rcases ih ((u₁ ++ v₁).length + (u₂ ++ v₂).length) hlen sₓ s₁ s₂
          (u₁ ++ v₁) (u₂ ++ v₂) p rfl ⟨hx₁, hx₂⟩ with
        hpre | hpre | ⟨q, u, a, b, r₁, r₂, h₁, h₂, hm⟩
      · obtain ⟨c, hc⟩ := hpre
        exact Or.inl ⟨c, by rw [proj_cons _ _ p hp₁, proj_cons _ _ p hp₂, List.append_assoc, hc]⟩
      · obtain ⟨c, hc⟩ := hpre
        exact Or.inr (Or.inl ⟨c, by
          rw [proj_cons _ _ p hp₂, proj_cons _ _ p hp₁, List.append_assoc, hc]⟩)
      · -- Both projections prepend the same observation, even when q cannot see x₁.
        exact Or.inr (Or.inr ⟨q, (if q ∈ pn x₁ then [x₁] else []) ++ u, a, b, r₁, r₂,
          by rw [proj_cons _ _ q hp₁, h₁, List.append_assoc],
          by rw [proj_cons _ _ q hp₂, h₂, List.append_assoc], hm⟩)

/-- Locate a projected action in the original trace, including any preceding invisible labels. -/
private lemma lift_projected_action {q : Pid} {t u v : List Label} {a : Label}
    (h : ProjectTrace (pn := pn) t q = u ++ a :: v) :
    ∃ pre, pre ++ [a] <+: t ∧ ProjectTrace (pn := pn) pre q = u := by
  obtain ⟨l, r, rfl, hl, hr⟩ := List.filter_eq_append_iff.mp h
  obtain ⟨skip, tail, rfl, hskip, _, _⟩ := List.filter_eq_cons_iff.mp hr
  refine ⟨l ++ skip, ⟨tail, by simp⟩, ?_⟩
  simp only [ProjectTrace, List.filter_append, hl, List.filter_eq_nil_iff.mpr hskip,
    List.append_nil]

end Helpers

theorem if_smurf_then_traces
    {pn : Label → Finset Pid}
    {lts : LTS State Label}
    {I : Label → Label → Prop}
    [Independence I]
    {B : Branching Label}
    {hpn₀ : ∀ l, (pn l).Nonempty}
    {hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂)}
    {hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → (pn l₁) = (pn l₂)}
    (h : Smurf lts I B) :
  ∀ {s : State} {t₁ t₂ : List Label} {p : Pid},
    t₁ ∈ lts.traces s ∧ t₂ ∈ lts.traces s →
    (
      ProjectTrace (pn := pn) t₁ p <+: ProjectTrace (pn := pn) t₂ p
      ∨
      ProjectTrace (pn := pn) t₂ p <+: ProjectTrace (pn := pn) t₁ p
      ∨
      (
        ∃ (q : Pid) (t₁' t₂' : List Label) (l₁ l₂ : Label),
          (
            t₁' ++ [l₁] <+: t₁
            ∧ t₂' ++ [l₂] <+: t₂
            ∧ B.matching l₁ l₂
            ∧ ProjectTrace (pn := pn) t₁' q = ProjectTrace (pn := pn) t₂' q
          )
      )
    )
  := by
    rintro s t₁ t₂ p ⟨⟨s₁, ht₁⟩, ⟨s₂, ht₂⟩⟩
    rcases prefix_or_projected_match hpn₀ hpn₁ hpn₂ h s s₁ s₂ t₁ t₂ p ⟨ht₁, ht₂⟩ with
      h₁ | h₂ | ⟨q, u, a, b, v₁, v₂, h₁, h₂, hm⟩
    · exact Or.inl h₁
    · exact Or.inr (Or.inl h₂)
    · obtain ⟨l, hl, hpl⟩ := lift_projected_action h₁
      obtain ⟨r, hr, hpr⟩ := lift_projected_action h₂
      exact Or.inr (Or.inr ⟨q, l, r, a, b, hl, hr, hm, hpl.trans hpr.symm⟩)

end Cslib.Concurrency
