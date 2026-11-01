/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init
public import Cslib.Foundations.Data.PFunctor.Basic

/-! # Modal Frames

A frame is a structure of relations, each with its own arity.

## Implementation notes

Frames for general modal logic were formulated with modal similarity types [Blackburn2001], which
we generalise here to arbitrary polynomial functors.

## References

* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
-/

@[expose] public section

namespace Cslib

/-- A frame is an indexed structure of general relations that can differ in argument positions.

Frames are typically used in combination with modal logics or akin concepts. This is why we use
`op` (for operator) to range over relation indexes.

The definition generalises Definition 1.23 in [Blackburn2001] to general operator signatures given
as `PFunctor`s and possibly-empty world types.
-/
structure Frame (World : Type u) (τ : PFunctor) where
  /-- Accessibility relations. -/
  r : (op : τ.A) → World → (τ.B op → World) → Prop

namespace Frame

/-- The binary relation obtained by observing position `i` of the worlds accessible via `op`. -/
def project (f : Frame World τ) (op : τ.A) (i : τ.B op) : World → World → Prop :=
  fun w w' => ∃ ws, f.r op w ws ∧ ws i = w'

/-- The binary relation induced by restricting the accessibility relation of `op`
to constant tuples of worlds. -/
@[instance_reducible]
def diagonal (f : Frame World τ) (op : τ.A) : World → World → Prop :=
  fun w w' => f.r op w (fun _ => w')

@[scoped grind →, modal →]
theorem r_const_of_diagonal {f : Frame World τ} (h : f.diagonal op w w') :
    f.r op w (fun _ => w') := by grind [Frame.diagonal]

@[scoped grind →, modal →]
theorem diagonal_of_r [PFunctor.Unary τ] {f : Frame World τ} (h : f.r op w ws) :
    f.diagonal op w (ws default) := by grind [Frame.diagonal, PFunctor.Unary.fun_eq_const op ws]

/-- Two operators in a frame have inverse diagonal relations. -/
class DiagonalInverse (f : Frame World τ) (op₁ op₂ : τ.A) where
  diagonalInverse : ∀ w w', f.diagonal op₁ w w' ↔ f.diagonal op₂ w' w

instance (f : Frame World τ) (op₁ op₂ : τ.A) [inst : f.DiagonalInverse op₁ op₂] :
    f.DiagonalInverse op₂ op₁ := ⟨fun w w' => (inst.diagonalInverse w' w).symm⟩

/-- A frame is diagonally symmetric at `op` if, whenever `w` accesses `ws`, some component of `ws`
accesses the constant sequence at `w`. -/
class DiagonalSymm (f : Frame World τ) (op : τ.A) where
  symm w ws : f.r op w ws → ∃ i, f.r op (ws i) (fun _ => w)

/-- A frame is transitive at `op` if accessibility can be composed through any accessible component:
whenever `w` accesses `ws₁` and `ws₁ i` accesses `ws₂`, then `w` accesses `ws₂`.
-/
class Trans (f : Frame World τ) (op : τ.A) where
  trans w ws₁ i ws₂ : f.r op w ws₁ → f.r op (ws₁ i) ws₂ → f.r op w ws₂

/-- Frame transitivity at `op` implies transitivity of all its projected binary relations. -/
instance (f : Frame World τ) [f.Trans op] (i : τ.B op) :
    IsTrans World (f.project op i) where
  trans w₁ w₂ w₃ h₁ h₂ := by
    rcases h₁ with ⟨ws₁, hr₁, rfl⟩
    rcases h₂ with ⟨ws₂, hr₂, h⟩
    exact ⟨ws₂, Frame.Trans.trans _ _ _ _ hr₁ hr₂, h⟩

/-- A frame is right Euclidean at `op` if, whenever a world `w` accesses two tuples `ws₁` and
`ws₂`, some component of `ws₂` accesses `ws₁`. -/
class RightEuclidean (f : Frame World τ) (op : τ.A) where
  rightEuclidean w ws₁ ws₂ : f.r op w ws₁ → f.r op w ws₂ → ∃ i, f.r op (ws₂ i) ws₁

/-- A predicate map `Ps` is preserved from `P` by `op` if, whenever `P` holds at a world `w`,
then for every tuple `ws` accessible from `w` via `op`, each component `ws i` satisfies the
corresponding predicate `Ps i`. -/
def PreservesMap (f : Frame α τ) (op : τ.A) (P : α → Prop) (Ps : τ.B op → α → Prop) : Prop :=
  ∀ w ws, f.r op w ws → P w → ∃ i, Ps i (ws i)

/-- Builds a unary frame from an indexed family of binary relations. -/
def ofRelations {τ : PFunctor} [τ.Unary] (r : τ.A → World → World → Prop) :
    Frame World τ where
  r i w ws := r i w (ws default)

@[scoped grind =, modal =]
lemma ofRelations_iff {τ : PFunctor} [τ.Unary] (r : τ.A → World → World → Prop) (i : τ.A)
    (w : World) (ws : τ.B i → World) : (ofRelations r).r i w ws ↔ r i w (ws default) := by rfl

@[simp, scoped grind =, modal =]
lemma ofRelations_diagonal_iff {τ : PFunctor} [τ.Unary]
    (r : τ.A → World → World → Prop) (i : τ.A) (w w' : World) :
    (ofRelations r).diagonal i w w' ↔ r i w w' := by
  rfl

end Frame

end Cslib
