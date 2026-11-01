/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Data.PFunctor.Basic
public import Cslib.Logics.Modal.Basic
public import Cslib.Logics.Modal.Semantics
public import Cslib.Logics.Modal.LogicalEquivalence

/-! # Unary Modal Logic -/

@[expose] public section

namespace Cslib.Logic.Modal

open PFunctor
open scoped InferenceSystem Proposition Satisfies Frame

variable {τ : PFunctor} [τ.Unary]

/-- Context constructor for the dynamic diamond modality. -/
@[match_pattern]
def Proposition.Context.dynDiamond (c : Context τ Atom) (a : τ.A) : Context τ Atom :=
  .triangle a default c fun ⟨i, hi⟩ => (hi (Subsingleton.elim i default)).elim

@[scoped grind =]
theorem Proposition.unary_triangle_eq_dynDiamond {a : τ.A}
    (φs : PropositionMap τ a Atom) : (Δ[a]φs) = d⟨a⟩(φs default) := by
  rw [PFunctor.Unary.fun_eq_const a φs]
  rfl

@[modal =]
theorem Satisfies.dynDiamond_iff_exists {m : Model World τ Atom}
    {φ : Proposition τ Atom} : ⇓Modal[m,w ⊨ d⟨a⟩φ] ↔
      ∃ w', m.toFrame.diagonal a w w' ∧ ⇓Modal[m,w' ⊨ φ] := by grind

@[modal =]
theorem Satisfies.dynBox_iff_forall {m : Model World τ Atom} {φ : Proposition τ Atom} :
    ⇓Modal[m,w ⊨ d[a]φ] ↔ ∀ w', m.toFrame.diagonal a w w' → ⇓Modal[m,w' ⊨ φ] := by grind

/-- If two operators `op₁` and `op₂` have inverse diagonal relations, then `φ → d[op₁](d⟨op₂⟩φ)`. -/
theorem Satisfies.dynBox_dynDiamond_diagonalInverse₁ {m : Model World τ Atom}
    {op₁ op₂ : τ.A} [m.toFrame.DiagonalInverse op₁ op₂] {φ : Proposition τ Atom} :
    ⇓Modal[m,w ⊨ φ → d[op₁](d⟨op₂⟩φ)] := by
  grind [modal, Frame.DiagonalInverse.diagonalInverse]

/-- If two operators `op₁` and `op₂` have inverse diagonal relations, then `φ → d[op₂](d⟨op₁⟩φ)`. -/
theorem Satisfies.dynBox_dynDiamond_diagonalInverse₂ {m : Model World τ Atom}
    {op₁ op₂ : τ.A} [m.toFrame.DiagonalInverse op₁ op₂] {φ : Proposition τ Atom} :
    ⇓Modal[m,w ⊨ φ → d[op₂](d⟨op₁⟩φ)] :=
  dynBox_dynDiamond_diagonalInverse₁

omit [τ.Unary] in
/-- The dual axiom (reformulated for unary modal logic). -/
theorem Satisfies.unary_dual (f : Frame World τ) {a : τ.A} {φ : Proposition τ Atom} :
    Axiom f⇓(d⟨a⟩φ ↔ ¬d[a]¬φ) := by
  /- We use `grind only` on purpose here because this axiom should be derivable from the more
    more general `Satisfies.dual`. -/
  grind only [modal, Satisfies.dual]

end Cslib.Logic.Modal
