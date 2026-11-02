/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.Relation.Attr
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Congruence

/-! # β-reduction for the λ-calculus

## References

* [A. Chargueraud, *The Locally Nameless Representation*] [Chargueraud2012]
* See also https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/, from which
  this is partially adapted

-/

public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Untyped.Term

/-- A single β-reduction step. -/
@[scoped grind]
inductive Beta : Term Var → Term Var → Prop
/-- Reduce an application to a lambda term. -/
| beta : LC (abs M)→ LC N → Beta (app (abs M) N) (M ^ N)

/-- Full β-reduction. -/
@[reduction_sys "βᶠ"]
abbrev FullBeta : Term Var → Term Var → Prop := Xi Beta

namespace FullBeta

variable {M M' N N' : Term Var}

/-- The left side of a reduction is locally closed. -/
@[scoped grind →]
lemma step_lc_l (step : M ⭢βᶠ M') : LC M := Xi.step_lc_l (by grind) step

/-- Left congruence rule for application in multiple reduction. -/
@[scoped grind ←]
theorem redex_app_l_cong (redex : M ↠βᶠ M') (lc_N : LC N) : app M N ↠βᶠ app M' N := by
  induction redex <;> grind

/-- Right congruence rule for application in multiple reduction. -/
@[scoped grind ←]
theorem redex_app_r_cong (redex : M ↠βᶠ M') (lc_N : LC N) : app N M ↠βᶠ app N M' := by
  induction redex <;> grind

set_option linter.tacticAnalysis.verifyGrindOnly false in
/- Single reduction `app M (fvar x) ⭢βᶠ N` implies reduction on `M` or a root beta step. -/
@[scoped grind →]
lemma invert_step_app_fvar (step : app M (fvar x) ⭢βᶠ N) :
    (∃ M', N = app M' (fvar x) ∧ M ⭢βᶠ M') ∨ (∃ M1, M = abs M1 ∧ N = M1 ^ fvar x) := by
  cases step
  case base h => cases h with | beta => exact .inr ⟨_, rfl, rfl⟩
  case appR step_M _ => exact .inl ⟨_, rfl, step_M⟩
  grind only [cases Xi]

variable [HasFresh Var] [DecidableEq Var]

/-- The right side of a reduction is locally closed. -/
@[scoped grind →]
lemma step_lc_r (step : M ⭢βᶠ M') : LC M' := Xi.step_lc_r (by grind) step

lemma steps_lc_or_rfl {M M' : Term Var} (redex : M ↠βᶠ M') : (LC M ∧ LC M') ∨ M = M' := by
  grind

/-- Substitution of a locally closed term respects a single reduction step. -/
lemma redex_subst_cong_lc (s s' t : Term Var) (x : Var) (step : s ⭢βᶠ s') (h_lc : LC t) :
    s[x := t] ⭢βᶠ s'[x := t] := by
  induction step with
  | base beta => grind [subst_open]
  | abs =>
    #adaptation_note
    /-- A grind regression found moving to nightly-2026-10-01 (changes from lean#15420):
    this goal now needs more E-matching rounds. -/
    grind (ematch := 7) [Xi.abs <| free_union Var]
  | _ => grind

/-- Substitution respects a single reduction step of a free variable. -/
lemma redex_subst_cong (s s' : Term Var) (x y : Var) (step : s ⭢βᶠ s') :
    s[x := fvar y] ⭢βᶠ s'[x := fvar y] :=
  redex_subst_cong_lc _ _ _ _ step (.fvar y)

/-- An β-reduction step does not introduce new free variables. -/
lemma step_not_fv (step : M ⭢βᶠ N) : N.fv ⊆ M.fv := by
  induction step with
  | base h => cases h with | beta => grind [open_preserve_not_fvar]
  | @abs M N =>
    have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
    have := open_close x
    grind [open_preserve_not_fvar 0 M N]
  | _ => grind

/-- Abstracting then closing preserves a single reduction. -/
lemma step_abs_close {x : Var} (step : M ⭢βᶠ M') : M⟦0 ↜ x⟧.abs ⭢βᶠ M'⟦0 ↜ x⟧.abs := by
  grind [Xi.abs ∅, redex_subst_cong]

/-- Abstracting then closing preserves multiple reductions. -/
lemma redex_abs_close {x : Var} (step : M ↠βᶠ M') : (M⟦0 ↜ x⟧.abs ↠βᶠ M'⟦0 ↜ x⟧.abs) :=  by
  induction step using Relation.ReflTransGen.trans_induction_on
  case refl => rfl
  case single ih => exact Relation.ReflTransGen.single (step_abs_close ih)
  case trans l r => exact Relation.ReflTransGen.trans l r

/-- Multiple reduction of opening implies multiple reduction of abstraction. -/
theorem step_abs_cong (xs : Finset Var) (cofin : ∀ x ∉ xs, (M ^ fvar x) ⭢βᶠ (M' ^ fvar x)) :
    M.abs ⭢βᶠ M'.abs := by
  have ⟨fresh, _⟩ := fresh_exists <| free_union [fv] Var
  rw [open_close fresh M 0 ?_, open_close fresh M' 0 ?_]
  all_goals grind [step_abs_close]

/-- Multiple reduction of opening implies multiple reduction of abstraction. -/
theorem redex_abs_cong (xs : Finset Var) (cofin : ∀ x ∉ xs, (M ^ fvar x) ↠βᶠ (M' ^ fvar x)) :
    M.abs ↠βᶠ M'.abs := by
  have ⟨fresh, _⟩ := fresh_exists <| free_union [fv] Var
  rw [open_close fresh M 0 ?_, open_close fresh M' 0 ?_]
  all_goals grind [redex_abs_close]

/- Reduction is preserved when opening with a locally closed term. -/
lemma step_open_cong_l
  (s s' t) (L : Finset Var) (step : ∀ x ∉ L, (s ^ fvar x) ⭢βᶠ (s' ^ fvar x)) (h_lc : LC t) :
    (s ^ t) ⭢βᶠ (s' ^ t) := by
  have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
  grind [subst_intro, redex_subst_cong_lc]

/- Multiple reduction `λ s ↠βᶠ t` implies `t = λ s'` for some s' -/
lemma invert_steps_abs {s t : Term Var} (step : s.abs ↠βᶠ t) :
    ∃ (s' : Term Var), s.abs ↠βᶠ s'.abs ∧ t = s'.abs := by
  induction step with
  | refl => grind
  | tail _ step _ => cases step with grind [step_abs_cong (free_union Var)]

/- `λ s ↠βᶠ λ s'` implies `s ^ t ↠βᶠ s' ^ t'` -/
lemma steps_open_cong_l_abs
  (s s' t : Term Var) (steps : s.abs ↠βᶠ s'.abs) (lc_t : LC t) :
    (s ^ t) ↠βᶠ (s' ^ t) := by
  generalize eq : s.abs = s_abs at steps
  generalize eq' : s'.abs = s'_abs at steps
  induction steps generalizing s s' with
  | refl => grind
  | @tail b c steps' step ih =>
    specialize ih s
    #adaptation_note
    /-- A grind regression found moving to nightly-2026-10-01 (changes from lean#15420):
    `invert_steps_abs` is never instantiated as a hint any more, because the pattern derived
    for it also requires an `Exists` term that the new goal normalization no longer creates.
    Inverting by hand instead. -/
    obtain ⟨m, _, rfl⟩ := invert_steps_abs (eq ▸ steps')
    cases step with grind [step_open_cong_l (L := free_union Var)]

/- `t ↠βᶠ t'` implies `s[x := t] ↠βᶠ s[x := t']`.
   There is no single step lemma in this case because x
   may be substituted for n times, so a single step t ↠βᶠ t
   in general requires n steps in `s[x := t] ↠βᶠ (s[x := t'])` -/
lemma step_subst_cong_r {x : Var} (s t t' : Term Var) (step : t ⭢βᶠ t') (h_lc : LC s) :
    (s[x := t]) ↠βᶠ (s[x := t']) := by
  induction h_lc with
  | fvar y => grind
  | abs => grind [redex_abs_cong (free_union Var)]
  | @app l r =>
     calc
       (l.app r)[x := t] ↠βᶠ l[x := t].app (r[x := t']) := by grind
       _                 ↠βᶠ (l.app r)[x := t'] := by grind

/- `step_subst_cong_r` can be generalized to multiple reductions `t ↠βᶠ t'`.
   This requires s to be locally closed, locally closedness of t and t'
   can be inferred by the fact t reduces to t' -/
lemma steps_subst_cong_r {x : Var} (s t t' : Term Var) (step : t ↠βᶠ t') (h_lc : LC s) :
    (s[x := t]) ↠βᶠ (s[x := t']) := by
  induction step with
  | refl => rfl
  | tail steps step ih => grind [Relation.ReflTransGen.trans, step_subst_cong_r]

/- When both `t` and `s` reduce to `t'` and `s'`, then `t ^ s` reduces to `t' ^ s'` -/
lemma steps_open_cong_abs (s s' t t' : Term Var)
  (step1 : t ↠βᶠ t') (step2 : s.abs ↠βᶠ s'.abs) (lc_t : LC t) (lc_s : LC s.abs) :
    (s ^ t) ↠βᶠ (s' ^ t') := by
  cases lc_s with
  | abs L =>
    have ⟨x, _⟩ := fresh_exists <| free_union [fv] Var
    rw [subst_intro x t s, subst_intro x t' s']
    · trans (s ^ fvar x)[x := t']
      · grind [steps_subst_cong_r]
      · grind [=_ subst_intro, steps_open_cong_l_abs]
    all_goals grind

end LambdaCalculus.LocallyNameless.Untyped.Term.FullBeta

end Cslib
