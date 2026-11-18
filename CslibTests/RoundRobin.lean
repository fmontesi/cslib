/-
Copyright (c) 2026 Luc Edixhoven. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luc Edixhoven
-/

import Cslib.Foundations.Concurrency.RoundRobin.Basic

namespace CslibTests

open Cslib Cslib.Concurrency Cslib.Concurrency.RoundRobin

/-! ## Regression: two independent nonconditional self-loops

A one-state LTS with two independent self-loops is a smurf system, but no linearisation on the
singleton state type satisfies the cycle condition: choosing either label repeatedly gives a
cycle independent of the other always-enabled label.  The construction therefore genuinely needs
a larger state type, and the two queue states alternate the labels. -/

inductive TwoLabel : Type
  | x | y
  deriving DecidableEq

instance : Fintype TwoLabel :=
  ⟨{.x, .y}, fun l => by cases l <;> simp⟩

def twoLTS : LTS Unit TwoLabel where
  Tr _ l _ := l = .x ∨ l = .y

def twoBranching : Branching TwoLabel where
  conditional _ := False
  matching _ _ := False
  symm := Std.Symm.mk (fun _ _ h => h)
  irrefl := Std.Irrefl.mk (fun _ h => h)
  functional _ _ _ h := h.elim
  matchcond _ _ h := h.elim

instance : Std.Symm (fun (a b : TwoLabel) => a ≠ b) := ⟨fun _ _ h => h.symm⟩
instance : Std.Irrefl (fun (a b : TwoLabel) => a ≠ b) := ⟨fun _ h => h rfl⟩
instance : Independence (fun (a b : TwoLabel) => a ≠ b) := inferInstance

theorem twoSmurf : Smurf twoLTS (fun (a b : TwoLabel) => a ≠ b) twoBranching where
  s := by unfold SaneAlphabet; trivial
  m := fun _ _ _ h => h.1.elim
  u := fun _ _ _ _ _ hne _ => Or.inl hne
  r := fun _ _ l1 l2 _ => ⟨(), by cases l1 <;> cases l2 <;> simp [twoLTS]⟩
  f := fun _ _ _ l1 l2 _ => ⟨(), by cases l2 <;> simp [twoLTS], by cases l1 <;> simp [twoLTS]⟩
  d := fun _ _ _ _ _ _ => rfl

/-- Finite existence applies to the two-loop system. -/
example : ∃ (R : Type) (_ : Finite R) (l : LTS R TwoLabel) (r : R) (φ : R → Unit),
    IsLinearisation (B := twoBranching) (I := fun (a b : TwoLabel) => a ≠ b) l twoLTS r () φ :=
  exists_finite_linearisation twoSmurf (fun _ _ h => h.elim) ()

/-- The composed representative-existence theorem applies.  With singleton participation sets,
independence already implies disjointness, and no matching pairs exist. -/
example : ∃ (R : Type) (_ : Finite R) (l : LTS R TwoLabel) (r : R),
    IsRepresentative (fun (a b : TwoLabel) => a ≠ b) (l.traces r) (twoLTS.traces ()) := by
  obtain ⟨R, hfin, l, r, φ, hlin⟩ :=
    exists_finite_linearisation (A := twoLTS) (B := twoBranching)
      (I := fun (a b : TwoLabel) => a ≠ b) twoSmurf (fun _ _ h => h.elim) ()
  exact ⟨R, hfin, l, r,
    linearisation_is_representative (B := twoBranching) (pn := fun l => {l})
      (hpn₀ := fun _ => ⟨_, Finset.mem_singleton_self _⟩)
      (hpn₁ := fun _ _ hi => Finset.disjoint_singleton.mpr (fun h => hi h))
      (hpn₂ := fun _ _ h => h.elim)
      l twoLTS twoSmurf r () φ hlin⟩

/-! ## Regression: an empty alphabet and a terminal state

A system with no transitions at all is a smurf system; the finite alphabet is empty and the
construction yields the terminal one-state scheduler. -/

def noTrLTS : LTS Unit TwoLabel where
  Tr _ _ _ := False

theorem noTrSmurf : Smurf noTrLTS (fun (a b : TwoLabel) => a ≠ b) twoBranching where
  s := by unfold SaneAlphabet; trivial
  m := fun _ _ _ h => h.1.elim
  u := fun _ _ _ _ _ hne h => by
    rcases h with ⟨h1, h2⟩
    exact absurd h1 (by simp [noTrLTS])
  r := by
    intro s s1 l1 l2 h
    obtain ⟨s', htr, -⟩ := LTS.MTr.cons_iff.mp h.2
    exact absurd htr (by simp [noTrLTS])
  f := fun _ _ _ _ _ h => absurd h.2.1 (by simp [noTrLTS])
  d := fun _ _ _ _ h _ => absurd h (by simp [noTrLTS])

example : ∃ (R : Type) (_ : Finite R) (l : LTS R TwoLabel) (r : R) (φ : R → Unit),
    IsLinearisation (B := twoBranching) (I := fun (a b : TwoLabel) => a ≠ b) l noTrLTS r () φ :=
  exists_finite_linearisation noTrSmurf (fun _ _ h => h.elim) ()

example : finiteAlphabet noTrLTS = ∅ := by
  rw [finiteAlphabet]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  rw [Set.Finite.mem_toFinset] at ha
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp ha
  obtain ⟨t, ht⟩ := hs
  exact ht

/-! A one-state system with two mutually matching conditional self-loops `true` and `false`.
Matching is "different label" on `Bool`, which is symmetric, irreflexive, functional, and makes
both labels conditional.  Independence is empty, so matching branches are dependent. -/

def condLTS : LTS Unit Bool where
  Tr _ _ _ := True

theorem bool_ne_symm : ∀ a b : Bool, a ≠ b → b ≠ a := fun _ _ h => h.symm
theorem bool_ne_irrefl : ∀ a : Bool, ¬ a ≠ a := fun _ h => h rfl
theorem bool_ne_functional : ∀ a b c : Bool, a ≠ b → a ≠ c → b = c := by
  intro a b c h1 h2
  cases a <;> cases b <;> cases c <;> simp_all
theorem bool_ne_matchcond : ∀ a b : Bool, a ≠ b → True ∧ True := fun _ _ _ => ⟨trivial, trivial⟩

def condBranching : Branching Bool where
  conditional _ := True
  matching a b := a ≠ b
  symm := Std.Symm.mk bool_ne_symm
  irrefl := Std.Irrefl.mk bool_ne_irrefl
  functional := bool_ne_functional
  matchcond := bool_ne_matchcond

instance : Std.Symm (fun (_ _ : Bool) => False) := ⟨fun _ _ h => h⟩
instance : Std.Irrefl (fun (_ _ : Bool) => False) := ⟨fun _ h => h⟩
instance : Independence (fun (_ _ : Bool) => False) := inferInstance

theorem condSmurf : Smurf condLTS (fun (_ _ : Bool) => False) condBranching where
  s := by unfold SaneAlphabet; trivial
  m := fun _ _ _ _ => ⟨!‹_›, (), by simp [condBranching], trivial⟩
  u := fun _ _ _ l1 l2 hne _ => Or.inr (by simpa [condBranching] using hne)
  r := fun _ _ _ _ _ => ⟨(), trivial⟩
  f := fun _ _ _ _ _ _ => ⟨(), trivial, trivial⟩
  d := fun _ _ _ _ _ _ => rfl

example : ∃ (R : Type) (_ : Finite R) (l : LTS R Bool) (r : R) (φ : R → Unit),
    IsLinearisation (B := condBranching) (I := fun (_ _ : Bool) => False) l condLTS r () φ :=
  exists_finite_linearisation condSmurf (fun a b h => by
    intro hI
    exact hI) ()

end CslibTests
