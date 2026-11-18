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

Luc's development, with help from DeepSeek-V4.1-Flash-1017 and Codex GPT-6 Astra Light.
-/

@[expose] public section

namespace Cslib.Concurrency

variable {RState State Label : Type*} {B : Branching Label} {I : Label → Label → Prop}
  {Pid : Type*} [DecidableEq Pid]

-- lts is linear
def IsLinear (lts : LTS State Label) :=
  -- if transitions, either a non-conditional or a matching pair
  (∀ s μ₁ s₁, lts.Tr s μ₁ s₁ → (¬ B.conditional μ₁ ∨ (∃ μ₂ s₂, lts.Tr s μ₂ s₂ ∧ B.matching μ₁ μ₂)))
  -- only pairs are matching conditionals
  ∧ (∀ s μ₁ μ₂ s₁ s₂, (lts.Tr s μ₁ s₁ ∧ lts.Tr s μ₂ s₂ ∧ μ₁ ≠ μ₂) → B.matching μ₁ μ₂)

-- in a linear LTS, every conditional label has a matching partner
theorem isLinear_conditional_partner {lts : LTS State Label} (hlin : IsLinear (B := B) lts) :
    ∀ s μ s', lts.Tr s μ s' → B.conditional μ →
      ∃ μ₂, B.matching μ μ₂ ∧ ∃ s₂, lts.Tr s μ₂ s₂ := by
  intro s μ s' htr hcond
  -- linearity at a conditional transition yields a matching partner
  rcases hlin.1 s μ s' htr with hnc | ⟨μ₂, s₂, htr₂, hmatch⟩
  · exact absurd hcond hnc
  · exact ⟨μ₂, hmatch, s₂, htr₂⟩

-- in a linear LTS, any non-conditional transition must be the unique transition
theorem isLinear_unique_of_not_conditional {lts : LTS State Label} (hlin : IsLinear (B := B) lts) :
    ∀ s μ s' ν t, lts.Tr s μ s' → ¬ B.conditional μ → lts.Tr s ν t →
      ν = μ := by
  intro s μ s' ν t htr hnc htr'
  -- distinct labels enabled at a common state would have to match, hence be conditional
  by_contra hne
  exact hnc (B.matchcond μ ν (hlin.2 s μ ν s' t ⟨htr, htr', fun h => hne h.symm⟩)).1

-- `lts₁` is a linearisation of `lts₂` from states `s₁/s₂` through mapping `φ`
def IsLinearisation [Independence I]
    (lts₁ : LTS RState Label) (lts₂ : LTS State Label) (s₁ : RState) (s₂ : State)
    (φ : RState → State) :=
  -- `lts₁` is linear
  IsLinear (B := B) lts₁
  -- TODO: if lts₂ finite then lts₁ also finite?
  -- there exists a corresponding state for `s₂` in `lts₁`
  ∧ φ s₁ = s₂
  -- all `lts₁` transitions can be mapped onto `lts₂`
  ∧ (∀ s μ s', lts₁.Tr s μ s' → lts₂.Tr (φ s) μ (φ s'))
  -- a state in `lts₁` is only terminal if its mapping in `lts₂` is
  ∧ (∀ s, lts₁.IsTerminal s → lts₂.IsTerminal (φ s))
  -- for any non-empty cycle in `lts₁`, any transition from the corresponding state in `lts₂`
  -- cannot be fully independent
  -- note: the cycle must be non-empty, otherwise the quantifier below is unsatisfiable
  -- (every state reaches itself with the empty trace); if `μ ∈ μs`, then this is covered by
  -- the irreflexivity of `I`
  ∧ (∀ s μs, μs ≠ [] → lts₁.MTr s μs s →
      (∀ μ s', lts₂.Tr (φ s) μ s' → (∃ μ' ∈ μs, ¬ I μ μ')))

section Helpers

variable [Independence I] {R : LTS RState Label} {A : LTS State Label}
  {φ : RState → State}

/-- An enabled action either commutes with the whole target, or meets an equal or matching
label after a prefix independent of it.
Essentially a label-trace version of commute_or_matcheq in Smurf.lean. -/
private lemma enabled_trace_cases (h : Smurf A I B) {s sa t : State} {a : Label}
    -- `a` and `w` are both enabled at `s`
    {w : List Label} (ha : A.Tr s a sa) (hw : A.MTr s w t) :
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

/-- A matching partner also commutes with an executable prefix independent of the original
branch, provided both branches are initially enabled. -/
private lemma matching_prefix_independent (h : Smurf A I B)
    (hno : ∀ a b, B.matching a b → ¬ I a b)
    -- matching pair `a b`, `a` independent of a trace `p`
    {a b : Label} (hm : B.matching a b) {p : List Label} {s sa sb t : State}
    (ha : A.Tr s a sa) (hb : A.Tr s b sb) (hp : A.MTr s p t)
    -- then `b` is also independent of `p`
    (hind : ∀ c ∈ p, I a c) : ∀ c ∈ p, I b c := by
  -- by induction on `p`
  induction p generalizing s sa sb with
  -- empty `p` is trivial
  | nil => simp
  -- otherwise deconstruct `p` into `c :: p`
  | cons c p ih =>
    obtain ⟨sc, hc, hp⟩ := LTS.MTr.cons_iff.mp hp
    -- `c` must be independent of both `a` and `b`
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
    -- the tail `p` is also independent of `b`, by the induction hypothesis
    have htail := ih ha' hb' hp (fun x hx => hind x (List.mem_cons_of_mem c hx))
    simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hbc htail

/-- Move an enabled occurrence to the front and retain an executable residual target. -/
private lemma consume_enabled (h : Smurf A I B)
    -- `A` is Smurf, `R`-transitions map onto `A`
    (hmap : ∀ q a q', R.Tr q a q' → A.Tr (φ q) a (φ q'))
    {q q' : RState} {t : State} {a : Label} {p r : List Label}
    -- `a` enabled in `R`, `p ++ a :: r` enabled in `A`, `a` independent of `p`
    (ha : R.Tr q a q') (hw : A.MTr (φ q) (p ++ a :: r) t)
    (hind : ∀ b ∈ p, I a b) :
    -- then `a` commutes along `p` in `A`, while retaining the tail `r`
    List.PermUpTo I (p ++ a :: r) (a :: (p ++ r)) ∧
      p ++ r ∈ A.traces (φ q') := by
  -- `a` and `p` commute
  have hswap : List.PermUpTo I (p ++ [a]) ([a] ++ p) :=
    permUpTo_append_comm p [a] fun b hb c hc => by
      have : c = a := List.mem_singleton.mp hc
      subst c
      exact Std.Symm.symm (r := I) (a := a) (b := b) (hind b hb)
  -- while retaining the tail `r`
  have hperm : List.PermUpTo I (p ++ a :: r) (a :: (p ++ r)) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      List.PermUpTo.append_right r _ _ hswap
  obtain ⟨sa, hsa, htail⟩ := LTS.MTr.cons_iff.mp (mtr_permUpTo h hperm hw)
  have heq := h.d (φ q) sa (φ q') a hsa (hmap q a q' ha)
  exact ⟨hperm, t, heq ▸ htail⟩

/-- A nonempty executable residual target admits either an independent waiting step or a
step consuming one of its occurrences. The branch choice consults the entire residual target. -/
private lemma wait_or_consume (h : Smurf A I B)
    -- `A` is smurf, `R` is linear, `R`-transitions and -terminals map onto `A`
    (hno : ∀ a b, B.matching a b → ¬ I a b)
    (hlinear : IsLinear (B := B) R)
    (hmap : ∀ q a q', R.Tr q a q' → A.Tr (φ q) a (φ q'))
    (hterm : ∀ q, R.IsTerminal q → A.IsTerminal (φ q))
    -- `w` is a nonempty trace of `A`
    {q : RState} {w : List Label} (hne : w ≠ []) (hw : w ∈ A.traces (φ q)) :
    -- then either `R` can take an independent transition, after which `w` remains enabled
    (∃ a q', R.Tr q a q' ∧ (∀ b ∈ w, I a b) ∧ w ∈ A.traces (φ q')) ∨
    -- or `R` can execute a label from `w`, after which the remainder of `w` remains enabled
    (∃ a q' w', R.Tr q a q' ∧ List.PermUpTo I w (a :: w') ∧
      w' ∈ A.traces (φ q')) := by
  classical
  obtain ⟨t, ht⟩ := hw
  -- `R` can take a transition `a`
  have henabled : ∃ a q', R.Tr q a q' := by
    by_contra hn
    have hterminal : R.IsTerminal q := by simpa only [LTS.IsTerminal, not_exists] using hn
    cases w with
    | nil => exact hne rfl
    | cons b w =>
      obtain ⟨s, hs, _⟩ := LTS.MTr.cons_iff.mp ht
      exact hterm q hterminal b s hs
  obtain ⟨a, qa, ha⟩ := henabled
  -- either `a` fully commutes with `w`, or they hit a match or equality
  rcases enabled_trace_cases h (hmap q a qa ha) ht with hind | ⟨p, b, r, rfl, hind, heq⟩
  -- if the two fully commute, then `w` remains enabled after `a`
  · obtain ⟨t', ht'⟩ := diamond_label_trace h a w (φ q) (φ qa) t
      (hmap q a qa ha) ht (fun b hb => Std.Symm.symm (r := I) (a := a) (b := b) (hind b hb))
    exact Or.inl ⟨a, qa, ha, hind, t', ht'⟩
  -- else, they hit an equality or a match after an independent prefix
  · rcases heq with rfl | hm
    -- if an equality, commute `a` to the front of `w` and execute it
    · obtain ⟨hperm, htail⟩ := consume_enabled h hmap ha ht hind
      exact Or.inr ⟨a, qa, p ++ r, ha, hperm, htail⟩
    -- else a match with `a`, commute this match to the front of `w` and execute it
    · obtain ⟨b', hm', qb, hb⟩ := isLinear_conditional_partner hlinear q a qa ha
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
private lemma finite_progress [Finite RState] (h : Smurf A I B)
    -- `A` is Smurf, `R` is its linearisation
    (hno : ∀ a b, B.matching a b → ¬ I a b)
    (hlinear : IsLinear (B := B) R)
    (hmap : ∀ q a q', R.Tr q a q' → A.Tr (φ q) a (φ q'))
    (hterm : ∀ q, R.IsTerminal q → A.IsTerminal (φ q))
    (hcycle : ∀ q d, d ≠ [] → R.MTr q d q →
      ∀ a s, A.Tr (φ q) a s → ∃ b ∈ d, ¬ I a b)
    -- `A` contains a non-empty trace `w`
    {q : RState} {w : List Label} (hne : w ≠ []) (hw : w ∈ A.traces (φ q)) :
    -- then `R` has a trace `d ++ [a]`
    ∃ d a q' w', R.MTr q (d ++ [a]) q' ∧
      -- s.t. `d` is independent of `w`
      (∀ c ∈ d, ∀ b ∈ w, I c b) ∧
      -- and `a` can be commuted to the front of `w`, leaving its tail enabled
      List.PermUpTo I w (a :: w') ∧ w' ∈ A.traces (φ q') := by
  -- Orient the relation towards predecessors for well-founded induction. Its edges are
  -- nonempty waiting paths, not individual transitions, so transitivity is immediate.
  -- `q' q` is a waiting path if there is a non-empty trace `d` from `q` to `q'` that is
  -- independent of `w`
  let waits : RState → RState → Prop := fun q' q =>
    ∃ d, d ≠ [] ∧ R.MTr q d q' ∧ (∀ c ∈ d, ∀ b ∈ w, I c b) ∧
      w ∈ A.traces (φ q)
  -- waiting paths are transitively closed
  have : IsTrans RState waits := ⟨by
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
  -- waiting paths are irreflexive
  have : Std.Irrefl waits := ⟨by
    rintro q ⟨d, hd, hrun, hind, t, ht⟩
    cases w with
    | nil => exact hne rfl
    | cons a w =>
      obtain ⟨s, ha, _⟩ := LTS.MTr.cons_iff.mp ht
      obtain ⟨b, hb, hnot⟩ := hcycle q d hd hrun a s ha
      exact hnot (Std.Symm.symm (r := I) (a := b) (b := a)
        (hind b hb a List.mem_cons_self))⟩
  -- waiting paths are well-founded
  have hwf := Finite.wellFounded_of_trans_of_irrefl waits
  revert hw
  -- reduce the goal through well-founded induction on waiting paths:
  -- if the theorem holding for all waiting paths `y q` implies the theorem holding for `q`,
  -- then the theorem holds for all `q`
  refine hwf.induction q (C := fun q => w ∈ A.traces (φ q) →
    ∃ d a q' w', R.MTr q (d ++ [a]) q' ∧
      (∀ c ∈ d, ∀ b ∈ w, I c b) ∧
      List.PermUpTo I w (a :: w') ∧ w' ∈ A.traces (φ q')) ?_
  intro q ih hw
  -- assuming that the theorem holds for all waiting paths `y q`
  -- left to prove: the theorem holds for `q`
  -- apply wait_or_consume:
  rcases wait_or_consume h hno hlinear hmap hterm hne hw with
    ⟨a, qa, ha, hind, hw'⟩ | ⟨a, qa, w', ha, hperm, hw'⟩
  -- either `R` can take an independent waiting step `a` to `qa`, and `w` remains enabled
  -- then `qa q` is a waiting path and, by the induction hypothesis, we obtain a witness
  · have hwait : waits qa q := ⟨[a], by simp, LTS.MTr.single R ha,
      by simpa only [List.mem_singleton, forall_eq] using hind, hw⟩
    obtain ⟨d, b, qb, w', hrun, hind', hperm, hw''⟩ := ih qa hwait hw'
    refine ⟨a :: d, b, qb, w', .stepL ha hrun, ?_, hperm, hw''⟩
    intro c hc x hx
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hind x hx
    · exact hind' c hc x hx
  -- or `R` can consume a step from `w` directly, leaving the empty trace as a witness
  · exact ⟨[], a, qa, w', LTS.MTr.single R ha, by simp, hperm, hw'⟩

/-- Construct a representative by induction on the length of the executable residual target.
Waiting labels become the extra suffix; each consuming step strictly shortens the target. -/
private lemma lin_copy_trace [Finite RState] (h : Smurf A I B)
    -- `A` is Smurf, `R` is its linearisation
    (hno : ∀ a b, B.matching a b → ¬ I a b)
    (hlinear : IsLinear (B := B) R)
    (hmap : ∀ q a q', R.Tr q a q' → A.Tr (φ q) a (φ q'))
    (hterm : ∀ q, R.IsTerminal q → A.IsTerminal (φ q))
    (hcycle : ∀ q d, d ≠ [] → R.MTr q d q →
      ∀ a s, A.Tr (φ q) a s → ∃ b ∈ d, ¬ I a b) :
    -- then for all `A`-traces `w`, there exists an `R`-trace `v`
    -- such that `w` is a prefix of `v` up to permutation
    ∀ q w, w ∈ A.traces (φ q) →
      ∃ v q' u, R.MTr q v q' ∧ List.PermUpTo I (w ++ u) v := by
  intro q w
  -- by induction on the length of `w`
  induction hn : w.length using Nat.strong_induction_on generalizing q w with
  | h n ih =>
    intro hw
    -- if `w` is empty, then trivial
    by_cases hnil : w = []
    · subst w
      exact ⟨[], q, [], .refl, .nil⟩
    -- else `R` can execute some action `a` from `w` after a finite number of steps,
    -- leaving the tail `w'` enabled
    -- then the induction hypothesis applies on `w'`, which chains into a full witness
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

-- matching labels can never be independent, given the participation hypotheses
omit [DecidableEq Pid] in
theorem matching_not_independent
    {pn : Label → Finset Pid}
    (hpn₀ : ∀ l, (pn l).Nonempty)
    (hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂))
    (hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → (pn l₁) = (pn l₂)) :
    ∀ a b, B.matching a b → ¬ I a b := by
  intro a b hm hi
  -- matching labels participate in the same set of processes, while independent labels
  -- participate in disjoint ones
  obtain ⟨p, hp⟩ := hpn₀ a
  have hp' : p ∈ pn b := (hpn₂ a b hm) ▸ hp
  exact Finset.disjoint_left.mp (hpn₁ a b hi) hp hp'

-- if `lts₁` is a linearisation of `lts₂`, then the traces of `lts₁` are representative of those
-- of `lts₂`
-- note: requires the linearising LTS to be finite-state; the original one need not be
omit [DecidableEq Pid] in
theorem linearisation_is_representative
    [Independence I]
    [Finite RState]
    {pn : Label → Finset Pid}
    {hpn₀ : ∀ l, (pn l).Nonempty}
    {hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂)}
    {hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → (pn l₁) = (pn l₂)}
    (lts₁ : LTS RState Label) (lts₂ : LTS State Label)
    (hsmurf : Smurf lts₂ I B)
    (s₁ : RState) (s₂ : State) (φ : RState → State)
  : IsLinearisation (B := B) (I := I) lts₁ lts₂ s₁ s₂ φ →
    IsRepresentative I (lts₁.traces s₁) (lts₂.traces s₂)
  := by
    intro ⟨hlinear, hinit, hmap, hterm, hcycle⟩ w hw
    have hno := matching_not_independent hpn₀ hpn₁ hpn₂
    rw [← hinit] at hw
    obtain ⟨v, q, u, hv, hperm⟩ :=
      lin_copy_trace hsmurf hno hlinear hmap hterm hcycle s₁ w hw
    exact ⟨u, v, ⟨q, hv⟩, hperm⟩

end Cslib.Concurrency
