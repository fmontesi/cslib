/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Basic
public import Mathlib.Algebra.Star.MonoidHom
public import Mathlib.Order.Hom.BoundedLattice

/-!
# Morphisms and isomorphisms of relation algebras

-/

@[expose] public section

namespace Cslib

/-- The type of relation algebra homomorphisms from `α` to `β`, preserving both the Boolean algebra
  and composition operations -/
structure RelationAlgebraHom (α β : Type*) [RelationAlgebra α] [RelationAlgebra β]
    extends BoundedLatticeHom α β, StarMonoidHom α β

open RelationAlgebraHom in
attribute [nolint docBlame] toStarMonoidHom toBoundedLatticeHom

/-- The type of relation algebra equivalence from `α` to `β`, preserving both the Boolean algebra
  and composition operations -/
structure RelationAlgebraEquiv (α β : Type*) [RelationAlgebra α] [RelationAlgebra β]
    extends toOrderIso : OrderIso α β, StarMulEquiv α β

attribute [nolint docBlame] RelationAlgebraEquiv.toStarMulEquiv

namespace RelationAlgebraHom

variable {α β γ : Type*} [RelationAlgebra α] [RelationAlgebra β] [RelationAlgebra γ]

instance : FunLike (RelationAlgebraHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; simp_all

instance : BoundedLatticeHomClass (RelationAlgebraHom α β) α β where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'
  map_bot f := f.map_bot'

instance : MonoidHomClass (RelationAlgebraHom α β) α β where
  map_mul f := f.map_mul'
  map_one f := f.map_one'

instance : StarHomClass (RelationAlgebraHom α β) α β where
  map_star f := f.map_star'

@[ext]
theorem ext {f g : RelationAlgebraHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/-- `id` as a `RelationAlgebraHom` -/
protected def id (α : Type*) [RelationAlgebra α] : RelationAlgebraHom α α :=
  { BoundedLatticeHom.id α, StarMonoidHom.id α with }

/-- Composition of `RelationAlgebraHom` -/
def comp (f : RelationAlgebraHom β γ) (g : RelationAlgebraHom α β) : RelationAlgebraHom α γ :=
  { f.toBoundedLatticeHom.comp g.toBoundedLatticeHom,
    f.toStarMonoidHom.comp g.toStarMonoidHom with }

@[simp]
theorem id_apply (a : α) : RelationAlgebraHom.id α a = a := rfl

@[simp]
theorem comp_apply (f : RelationAlgebraHom β γ) (g : RelationAlgebraHom α β) (a : α) :
    f.comp g a = f (g a) := rfl

theorem isIntegral_of_injective (f : RelationAlgebraHom α β) (hf : Function.Injective f)
    (h : RelationAlgebra.IsIntegral β) : RelationAlgebra.IsIntegral α := by
  refine ⟨fun h1 => IsAtom.ne_bot h ?_, fun b hb => hf ?_⟩
  · rw [← map_one f, h1, map_bot]
  · have hlt : f b < 1 := map_one f ▸ (OrderHomClass.mono f).strictMono_of_injective hf hb
    rw [map_bot]
    exact h.2 _ hlt

end RelationAlgebraHom

namespace RelationAlgebraEquiv

variable {α β γ : Type*} [RelationAlgebra α] [RelationAlgebra β] [RelationAlgebra γ]

instance : EquivLike (RelationAlgebraEquiv α β) α β where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h := by cases f; cases g; simp_all

instance : OrderIsoClass (RelationAlgebraEquiv α β) α β where
  map_le_map_iff f := f.map_rel_iff'

instance : MulEquivClass (RelationAlgebraEquiv α β) α β where
  map_mul f := f.map_mul'

instance : StarHomClass (RelationAlgebraEquiv α β) α β where
  map_star f := f.map_star'

@[ext]
theorem ext {f g : RelationAlgebraEquiv α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/-- The reflexive `RelationAlgebraEquiv` -/
protected def refl (α : Type*) [RelationAlgebra α] : RelationAlgebraEquiv α α :=
  { OrderIso.refl α, StarMulEquiv.refl α with }

/-- The symmetric `RelationAlgebraEquiv` -/
def symm (f : RelationAlgebraEquiv α β) : RelationAlgebraEquiv β α :=
  { f.toOrderIso.symm, f.toStarMulEquiv.symm with }

/-- The transitive `RelationAlgebraEquiv` -/
def trans (f : RelationAlgebraEquiv α β) (g : RelationAlgebraEquiv β γ) :
    RelationAlgebraEquiv α γ :=
  { f.toOrderIso.trans g.toOrderIso, f.toStarMulEquiv.trans g.toStarMulEquiv with }

/-- The `RelationAlgebraHom` underlying an `RelationAlgebraEquiv` -/
def toHom (f : RelationAlgebraEquiv α β) : RelationAlgebraHom α β :=
  { (f.toOrderIso : BoundedLatticeHom α β), f.toStarMulEquiv.toStarMonoidHom with }

@[simp]
theorem refl_apply (a : α) : RelationAlgebraEquiv.refl α a = a := rfl

@[simp]
theorem trans_apply (f : RelationAlgebraEquiv α β) (g : RelationAlgebraEquiv β γ) (a : α) :
    f.trans g a = g (f a) := rfl

@[simp]
theorem toHom_apply (f : RelationAlgebraEquiv α β) (a : α) : f.toHom a = f a := rfl

@[simp]
theorem symm_apply_apply (f : RelationAlgebraEquiv α β) (a : α) : f.symm (f a) = a :=
  f.left_inv a

@[simp]
theorem apply_symm_apply (f : RelationAlgebraEquiv α β) (b : β) : f (f.symm b) = b :=
  f.right_inv b

end RelationAlgebraEquiv

end Cslib
