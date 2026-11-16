/-
Copyright (c) 2026 Luc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luc
-/

module

public import Cslib.Foundations.Concurrency.Smurf
import Mathlib.Data.Fintype.Card

/-!
# Representative linearisations

A finite linearisation of a smurf LTS represents every trace of the original LTS, up to an
extra suffix and swaps of independent labels. The construction maintains an executable residual
target: independent waiting steps preserve it, and consuming steps shorten it. The cycle condition
rules out infinite waiting by finite well-founded induction.

Luc's development, with help from DeepSeek-V4.1-Flash-1017 and Codex.
-/

@[expose] public section

namespace Cslib.Concurrency

variable {State Label : Type*} {B : Branching Label} {I : Label → Label → Prop}
  {Pid : Type*} [DecidableEq Pid]

-- lts is linear
def IsLinear (lts : LTS State Label) :=
  -- if transitions, either a non-conditional or a matching pair
  (∀ s μ₁ s₁, lts.Tr s μ₁ s₁ → (¬ B.conditional μ₁ ∨ (∃ μ₂ s₂, lts.Tr s μ₂ s₂ ∧ B.matching μ₁ μ₂)))
  -- only pairs are matching conditionals
  ∧ (∀ s μ₁ μ₂ s₁ s₂, (lts.Tr s μ₁ s₁ ∧ lts.Tr s μ₂ s₂ ∧ μ₁ ≠ μ₂) → B.matching μ₁ μ₂)

theorem isLinear_partner_unique {lts : LTS State Label} (hlin : IsLinear (B := B) lts) :
    ∀ s μ s', lts.Tr s μ s' → B.conditional μ →
      ∃ μ₂, B.matching μ μ₂ ∧ ∃ s₂, lts.Tr s μ₂ s₂
  := by
    intro s μ s' htr hcond
    -- linearity at a conditional transition yields a matching partner
    rcases hlin.1 s μ s' htr with hnc | ⟨μ₂, s₂, htr₂, hmatch⟩
    · exact absurd hcond hnc
    · exact ⟨μ₂, hmatch, s₂, htr₂⟩

theorem isLinear_unique_of_not_conditional {lts : LTS State Label} (hlin : IsLinear (B := B) lts) :
    ∀ s μ s' ν t, lts.Tr s μ s' → ¬ B.conditional μ → lts.Tr s ν t →
      ν = μ
  := by
    intro s μ s' ν t htr hnc htr'
    -- distinct labels enabled at a common state would have to match, hence be conditional
    by_contra hne
    exact hnc (B.matchcond μ ν (hlin.2 s μ ν s' t ⟨htr, htr', fun h => hne h.symm⟩)).1

-- lts₁ is a linearisation of lts₂ from states s₁/s₂ through mapping φ
def IsLinearisation [Independence I]
    (lts₁ lts₂ : LTS State Label) (s₁ s₂ : State) (φ : State → State) :=
  -- lts₁ is linear
  IsLinear (B := B) lts₁
  -- TODO: if lts₂ finite then lts₁ also finite?
  -- there exists a corresponding state for s₂ in lts₁
  ∧ φ s₁ = s₂
  -- all lts₁ transitions can be mapped onto lts₂
  ∧ (∀ s μ s', lts₁.Tr s μ s' → lts₂.Tr (φ s) μ (φ s'))
  -- a state in lts₁ is only terminal if its mapping in lts₂ is
  ∧ (∀ s, lts₁.IsTerminal s → lts₂.IsTerminal (φ s))
  -- for any non-empty cycle in lts₁, any transition from the same state in lts₂ cannot be
  -- fully independent
  -- note: the cycle must be non-empty, otherwise the quantifier below is unsatisfiable
  -- (every state reaches itself with the empty trace); if μ ∈ μs, then this is covered by
  -- the irreflexivity of I
  ∧ (∀ s μs, μs ≠ [] → lts₁.MTr s μs s →
      (∀ μ s', lts₂.Tr (φ s) μ s' → (∃ μ' ∈ μs, ¬ I μ μ')))

-- trace `v` is a `conditional prefix` of `w` if, for every process `p`,
-- `w` contains the same conditionals in the same order
def CondPrefix {pn : Label → Finset Pid} [DecidablePred B.conditional]
    (v w : List Label) : Prop :=
  ∀ (p : Pid), v.filter (fun l => decide (p ∈ pn l ∧ B.conditional l)) <+:
               w.filter (fun l => decide (p ∈ pn l ∧ B.conditional l))

section Helpers

variable [Independence I] {R A : LTS State Label} {φ : State → State}

/-- An enabled action either commutes with the whole target, or meets an equal or matching
label after a prefix independent of it. -/
private lemma enabled_trace_cases (h : Smurf A I B) {s sa t : State} {a : Label}
    {w : List Label} (ha : A.Tr s a sa) (hw : A.MTr s w t) :
    (∀ b ∈ w, I a b) ∨ ∃ p b r, w = p ++ b :: r ∧
      (∀ c ∈ p, I a c) ∧ (a = b ∨ B.matching a b) := by
  classical
  induction w generalizing s sa with
  | nil => exact Or.inl (by simp)
  | cons b w ih =>
    obtain ⟨sb, hb, hw⟩ := LTS.MTr.cons_iff.mp hw
    by_cases hab : I a b
    · obtain ⟨sab, _, ha'⟩ := h.f s sa sb a b ⟨hab, ha, hb⟩
      rcases ih ha' hw with hind | ⟨p, c, r, heq, hind, hlast⟩
      · exact Or.inl (by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hab hind)
      · refine Or.inr ⟨b :: p, c, r, ?_, ?_, hlast⟩
        · simp only [heq, List.cons_append]
        · simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hab hind
    · refine Or.inr ⟨[], b, w, rfl, by simp, ?_⟩
      by_cases heq : a = b
      · exact Or.inl heq
      · exact Or.inr ((h.u s sa sb a b heq ⟨ha, hb⟩).resolve_left hab)

/-- A matching partner also commutes with an executable prefix independent of the original
branch, provided both branches are initially enabled. -/
private lemma matching_prefix_independent (h : Smurf A I B)
    (hno : ∀ a b, B.matching a b → ¬ I a b)
    {a b : Label} (hm : B.matching a b) {p : List Label} {s sa sb t : State}
    (ha : A.Tr s a sa) (hb : A.Tr s b sb) (hp : A.MTr s p t)
    (hind : ∀ c ∈ p, I a c) : ∀ c ∈ p, I b c := by
  induction p generalizing s sa sb with
  | nil => simp
  | cons c p ih =>
    obtain ⟨sc, hc, hp⟩ := LTS.MTr.cons_iff.mp hp
    have hac : I a c := hind c List.mem_cons_self
    have hbc : I b c := by
      have hne : b ≠ c := fun heq => hno a b hm (heq ▸ hac)
      rcases h.u s sb sc b c hne ⟨hb, hc⟩ with hi | hm'
      · exact hi
      · have heq : a = c :=
          B.functional b a c (Std.Symm.symm (r := B.matching) (a := a) (b := b) hm) hm'
        exact False.elim (Std.Irrefl.irrefl (r := I) c (heq ▸ hac))
    obtain ⟨sa', _, ha'⟩ := h.f s sa sc a c ⟨hac, ha, hc⟩
    obtain ⟨sb', _, hb'⟩ := h.f s sb sc b c ⟨hbc, hb, hc⟩
    have htail := ih ha' hb' hp (fun x hx => hind x (List.mem_cons_of_mem c hx))
    simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hbc htail

/-- Move an enabled occurrence to the front and retain an executable residual target. -/
private lemma consume_enabled (h : Smurf A I B)
    (hmap : ∀ q a q', R.Tr q a q' → A.Tr (φ q) a (φ q'))
    {q q' t : State} {a : Label} {p r : List Label}
    (ha : R.Tr q a q') (hw : A.MTr (φ q) (p ++ a :: r) t)
    (hind : ∀ b ∈ p, I a b) :
    List.PermUpTo I (p ++ a :: r) (a :: (p ++ r)) ∧
      p ++ r ∈ A.traces (φ q') := by
  have hswap : List.PermUpTo I (p ++ [a]) ([a] ++ p) :=
    permUpTo_append_comm p [a] fun b hb c hc => by
      have : c = a := List.mem_singleton.mp hc
      subst c
      exact Std.Symm.symm (r := I) (a := a) (b := b) (hind b hb)
  have hperm : List.PermUpTo I (p ++ a :: r) (a :: (p ++ r)) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      List.PermUpTo.append_right r _ _ hswap
  obtain ⟨sa, hsa, htail⟩ := LTS.MTr.cons_iff.mp (mtr_permUpTo h hperm hw)
  have heq := h.d (φ q) sa (φ q') a hsa (hmap q a q' ha)
  exact ⟨hperm, t, heq ▸ htail⟩

/-- A nonempty executable residual target admits either an independent waiting step or a
step consuming one of its occurrences. The branch choice consults the entire residual target. -/
private lemma wait_or_consume (h : Smurf A I B)
    (hno : ∀ a b, B.matching a b → ¬ I a b)
    (hlinear : IsLinear (B := B) R)
    (hmap : ∀ q a q', R.Tr q a q' → A.Tr (φ q) a (φ q'))
    (hterm : ∀ q, R.IsTerminal q → A.IsTerminal (φ q))
    {q : State} {w : List Label} (hne : w ≠ []) (hw : w ∈ A.traces (φ q)) :
    (∃ a q', R.Tr q a q' ∧ (∀ b ∈ w, I a b) ∧ w ∈ A.traces (φ q')) ∨
    (∃ a q' w', R.Tr q a q' ∧ List.PermUpTo I w (a :: w') ∧
      w' ∈ A.traces (φ q')) := by
  classical
  obtain ⟨t, ht⟩ := hw
  have henabled : ∃ a q', R.Tr q a q' := by
    by_contra hn
    have hterminal : R.IsTerminal q := by simpa only [LTS.IsTerminal, not_exists] using hn
    cases w with
    | nil => exact hne rfl
    | cons b w =>
      obtain ⟨s, hs, _⟩ := LTS.MTr.cons_iff.mp ht
      exact hterm q hterminal b s hs
  obtain ⟨a, qa, ha⟩ := henabled
  rcases enabled_trace_cases h (hmap q a qa ha) ht with hind | ⟨p, b, r, rfl, hind, heq⟩
  · obtain ⟨t', ht'⟩ := diamond_label_trace h a w (φ q) (φ qa) t
      (hmap q a qa ha) ht (fun b hb => Std.Symm.symm (r := I) (a := a) (b := b) (hind b hb))
    exact Or.inl ⟨a, qa, ha, hind, t', ht'⟩
  · rcases heq with rfl | hm
    · obtain ⟨hperm, htail⟩ := consume_enabled h hmap ha ht hind
      exact Or.inr ⟨a, qa, p ++ r, ha, hperm, htail⟩
    · obtain ⟨b', hm', qb, hb⟩ := isLinear_partner_unique hlinear q a qa ha
        (B.matchcond a b hm).1
      have heq : b' = b := B.functional a b' b hm' hm
      subst b'
      obtain ⟨sp, hp, _⟩ := LTS.MTr.split ht
      have hind' := matching_prefix_independent h hno hm
        (hmap q a qa ha) (hmap q b qb hb) hp hind
      obtain ⟨hperm, htail⟩ := consume_enabled h hmap hb ht hind'
      exact Or.inr ⟨b, qb, p ++ r, hb, hperm, htail⟩

/-- Waiting paths are finite: a repeated state would give a nonempty cycle independent of
an enabled head of the target. Thus some finite waiting path ends in a consuming step. -/
private lemma finite_progress [Finite State] (h : Smurf A I B)
    (hno : ∀ a b, B.matching a b → ¬ I a b)
    (hlinear : IsLinear (B := B) R)
    (hmap : ∀ q a q', R.Tr q a q' → A.Tr (φ q) a (φ q'))
    (hterm : ∀ q, R.IsTerminal q → A.IsTerminal (φ q))
    (hcycle : ∀ q d, d ≠ [] → R.MTr q d q →
      ∀ a s, A.Tr (φ q) a s → ∃ b ∈ d, ¬ I a b)
    {q : State} {w : List Label} (hne : w ≠ []) (hw : w ∈ A.traces (φ q)) :
    ∃ d a q' w', R.MTr q (d ++ [a]) q' ∧
      (∀ c ∈ d, ∀ b ∈ w, I c b) ∧
      List.PermUpTo I w (a :: w') ∧ w' ∈ A.traces (φ q') := by
  -- Orient the relation towards predecessors for well-founded induction. Its edges are
  -- nonempty waiting paths, not individual transitions, so transitivity is immediate.
  let waits : State → State → Prop := fun q' q =>
    ∃ d, d ≠ [] ∧ R.MTr q d q' ∧ (∀ c ∈ d, ∀ b ∈ w, I c b) ∧
      w ∈ A.traces (φ q)
  have : IsTrans State waits := ⟨by
    rintro x y z ⟨d, hd, hrun, hind, _⟩ ⟨e, he, hrun', hind', hw⟩
    refine ⟨e ++ d, ?_, LTS.MTr.comp R hrun' hrun, ?_, hw⟩
    · intro hnil
      have hlen := congrArg List.length hnil
      simp only [List.length_append, List.length_nil] at hlen
      exact hd (List.eq_nil_of_length_eq_zero (by omega))
    · intro c hc b hb
      rcases List.mem_append.mp hc with hc | hc
      · exact hind' c hc b hb
      · exact hind c hc b hb⟩
  have : Std.Irrefl waits := ⟨by
    rintro q ⟨d, hd, hrun, hind, t, ht⟩
    cases w with
    | nil => exact hne rfl
    | cons a w =>
      obtain ⟨s, ha, _⟩ := LTS.MTr.cons_iff.mp ht
      obtain ⟨b, hb, hnot⟩ := hcycle q d hd hrun a s ha
      exact hnot (Std.Symm.symm (r := I) (a := b) (b := a)
        (hind b hb a List.mem_cons_self))⟩
  have hwf := Finite.wellFounded_of_trans_of_irrefl waits
  revert hw
  refine hwf.induction q (C := fun q => w ∈ A.traces (φ q) →
    ∃ d a q' w', R.MTr q (d ++ [a]) q' ∧
      (∀ c ∈ d, ∀ b ∈ w, I c b) ∧
      List.PermUpTo I w (a :: w') ∧ w' ∈ A.traces (φ q')) ?_
  intro q ih hw
  rcases wait_or_consume h hno hlinear hmap hterm hne hw with
    ⟨a, qa, ha, hind, hw'⟩ | ⟨a, qa, w', ha, hperm, hw'⟩
  · have hwait : waits qa q := ⟨[a], by simp, LTS.MTr.single R ha,
      by simpa only [List.mem_singleton, forall_eq] using hind, hw⟩
    obtain ⟨d, b, qb, w', hrun, hind', hperm, hw''⟩ := ih qa hwait hw'
    refine ⟨a :: d, b, qb, w', .stepL ha hrun, ?_, hperm, hw''⟩
    intro c hc x hx
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hind x hx
    · exact hind' c hc x hx
  · exact ⟨[], a, qa, w', LTS.MTr.single R ha, by simp, hperm, hw'⟩

/-- Construct a representative by induction on the length of the executable residual target.
Waiting labels become the extra suffix; each consuming step strictly shortens the target. -/
private lemma lin_copy_trace [Finite State] (h : Smurf A I B)
    (hno : ∀ a b, B.matching a b → ¬ I a b)
    (hlinear : IsLinear (B := B) R)
    (hmap : ∀ q a q', R.Tr q a q' → A.Tr (φ q) a (φ q'))
    (hterm : ∀ q, R.IsTerminal q → A.IsTerminal (φ q))
    (hcycle : ∀ q d, d ≠ [] → R.MTr q d q →
      ∀ a s, A.Tr (φ q) a s → ∃ b ∈ d, ¬ I a b) :
    ∀ q w, w ∈ A.traces (φ q) →
      ∃ v q' u, R.MTr q v q' ∧ List.PermUpTo I (w ++ u) v := by
  intro q w
  induction hn : w.length using Nat.strong_induction_on generalizing q w with
  | h n ih =>
    intro hw
    by_cases hnil : w = []
    · subst w
      exact ⟨[], q, [], .refl, .nil⟩
    obtain ⟨d, a, q', w', hrun, hind, hperm, hw'⟩ :=
      finite_progress h hno hlinear hmap hterm hcycle hnil hw
    have hlen := hperm.length_eq
    simp only [List.length_cons] at hlen
    obtain ⟨v, q'', u, hv, hp⟩ := ih w'.length (by omega) q' w' rfl hw'
    refine ⟨(d ++ [a]) ++ v, q'', d ++ u, LTS.MTr.comp R hrun hv, ?_⟩
    have hswap : List.PermUpTo I (w ++ d) (d ++ w) :=
      permUpTo_append_comm w d fun b hb c hc =>
        Std.Symm.symm (r := I) (a := c) (b := b) (hind c hc b hb)
    have h₁ : List.PermUpTo I (w ++ (d ++ u)) ((d ++ w) ++ u) := by
      simpa only [List.append_assoc] using List.PermUpTo.append_right u _ _ hswap
    have h₂ : List.PermUpTo I ((d ++ w) ++ u) ((d ++ (a :: w')) ++ u) :=
      List.PermUpTo.append_right u _ _ (List.PermUpTo.append_left d _ _ hperm)
    have h₃ : List.PermUpTo I ((d ++ (a :: w')) ++ u) ((d ++ [a]) ++ v) := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        List.PermUpTo.append_left d _ _ (List.PermUpTo.cons a hp)
    exact h₁.trans (h₂.trans h₃)

end Helpers

-- if lts₁ is a linearisation of lts₂, then the traces of lts₁ are representative of those of lts₂
-- note: requires both LTSs to be finite-state
omit [DecidableEq Pid] in
theorem linearisation_is_representative
    [Independence I]
    [Finite State]
    {pn : Label → Finset Pid}
    {hpn₀ : ∀ l, (pn l).Nonempty}
    {hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂)}
    {hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → (pn l₁) = (pn l₂)}
    (lts₁ lts₂ : LTS State Label)
    (hsmurf : Smurf lts₂ I B)
    (s₁ s₂ : State)
    (φ : State → State)
  : IsLinearisation (B := B) (I := I) lts₁ lts₂ s₁ s₂ φ →
    IsRepresentative I (lts₁.traces s₁) (lts₂.traces s₂)
  := by
    intro ⟨hlinear, hinit, hmap, hterm, hcycle⟩ w hw
    have hno : ∀ a b, B.matching a b → ¬ I a b := by
      intro a b hm hi
      obtain ⟨p, hp⟩ := hpn₀ a
      have hp' : p ∈ pn b := (hpn₂ a b hm) ▸ hp
      exact Finset.disjoint_left.mp (hpn₁ a b hi) hp hp'
    rw [← hinit] at hw
    obtain ⟨v, q, u, hv, hperm⟩ :=
      lin_copy_trace hsmurf hno hlinear hmap hterm hcycle s₁ w hw
    exact ⟨u, v, ⟨q, hv⟩, hperm⟩

end Cslib.Concurrency
