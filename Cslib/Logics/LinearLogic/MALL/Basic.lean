/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Acclavio, Fabrizio Montesi
-/

module

public import Cslib.Init
public import Cslib.Foundations.Syntax.Context
public import Cslib.Foundations.Logic.InferenceSystem
public import Cslib.Foundations.Logic.LogicalEquivalence
public import Mathlib.Data.Multiset.Fold
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Union
public import Cslib.Foundations.Data.FinFun

@[expose] public section

/-! # Multiplicative Additive Linear Logic (MALL)

## References

* [J.-Y. Girard, *Linear Logic: its syntax and semantics*][Girard1995]

-/

namespace Cslib.Logic

universe u

variable {Atom : Type u}

namespace MALL

/-- Propositions. -/
inductive Proposition (Atom : Type u) : Type u where
  | atom (x : Atom)
  | atomDual (x : Atom)
  -- | one
  -- | zero
  -- | top
  -- | bot
  /-- The multiplicative conjunction connective. -/
  | tensor (a b : Proposition Atom)
  /-- The multiplicative disjunction connective. -/
  | parr (a b : Proposition Atom)
  /-- The additive disjunction connective. -/
  | oplus (a b : Proposition Atom)
  /-- The additive conjunction connective. -/
  | with (a b : Proposition Atom)
deriving DecidableEq, BEq

-- instance : Zero (Proposition Atom) := ⟨.zero⟩
-- instance : One (Proposition Atom) := ⟨.one⟩

-- instance : Top (Proposition Atom) := ⟨.top⟩
-- instance : Bot (Proposition Atom) := ⟨.bot⟩

@[inherit_doc] scoped infix:35 " ⊗ " => Proposition.tensor
@[inherit_doc] scoped infix:35 " ⊕ " => Proposition.oplus
@[inherit_doc] scoped infix:30 " ⅋ " => Proposition.parr
@[inherit_doc] scoped infix:30 " & " => Proposition.with

/-- Propositional duality. -/
@[scoped grind =]
def Proposition.dual : Proposition Atom → Proposition Atom
  | atom x => atomDual x
  | atomDual x => atom x
  | tensor a b => parr a.dual b.dual
  | parr a b => tensor a.dual b.dual
  | oplus a b => .with a.dual b.dual
  | .with a b => oplus a.dual b.dual

@[inherit_doc] scoped postfix:max "⫠" => Proposition.dual


/-- A sequent in MALL is a multiset of propositions. -/
abbrev Sequent Atom := Multiset (Proposition Atom)

open Proposition in
/-- A proof in the sequent calculus for classical linear logic. -/
inductive Proof : Sequent Atom → Type u where
  | ax : Proof {a, a⫠}
  | cut : Proof (a ::ₘ Γ) → Proof (a⫠ ::ₘ Δ) → Proof (Γ + Δ)
  | parr : Proof (a ::ₘ b ::ₘ Γ) → Proof ((a ⅋ b) ::ₘ Γ)
  | tensor : Proof (a ::ₘ Γ) → Proof (b ::ₘ Δ) → Proof ((a ⊗ b) ::ₘ (Γ + Δ))
  | oplus₁ : Proof (a ::ₘ Γ) → Proof ((a ⊕ b) ::ₘ Γ)
  | oplus₂ : Proof (b ::ₘ Γ) → Proof ((a ⊕ b) ::ₘ Γ)
  | with : Proof (a ::ₘ Γ) → Proof (b ::ₘ Γ) → Proof ((a & b) ::ₘ Γ)

namespace ProofNet





----------------------------
-- Trees with unique identifier for each node, and well-formedness condition
----------------------------

inductive BinTree (α : Type*) where
  | leaf (a : α)
  | node (a : α) (t₁ : BinTree α) (t₂ : BinTree α)


def BinTree.names [DecidableEq α] (t : BinTree α) : Finset α :=
  match t with
  | leaf a        => {a}
  | node a t₁ t₂  => {a} ∪ t₁.names ∪ t₂.names

def BinTree.wellFormed [DecidableEq α] (t : BinTree α) : Prop :=
  match t with
  | leaf _ => True
  | node a t₁ t₂ => Disjoint t₁.names t₂.names ∧ a ∉ t₁.names ∪ t₂.names


----------------------------
-- Formula Trees
----------------------------
inductive PropositionBinTree.Value (Atom : Type u) where
  | atom (a : Atom)
  | atomDual (a : Atom)
  | tensor
  | parr
  | oplus
  | with

def PropositionBinTree (Atom Name : Type*) [DecidableEq Name] :=
  Σ (t : BinTree Name), ({n // n ∈ t.names} → PropositionBinTree.Value Atom)



-- ----------------------------
-- -- HERE COULD BE REDUNDANT
-- ----------------------------
-- -- M: is if ok that we rename the seuents?
-- abbrev Sequent (Atom Name : Type*) [DecidableEq Name] := Multiset (PropositionBinTree Atom Name)


-- -- M this may be useless now we have BinForest.wellFormed
-- def Sequent.wellFormed [DecidableEq Name] (Γ : Sequent Atom Name) :=
--   Γ.map (BinTree.names ·.1)
--   |> Multiset.fold (Disjoint · ·)
--   -- |> Multiset.fold (· ∪ ·) ∅
-- ----------------------------
-- ----------------------------



----------------------------
-- TO REVISE
----------------------------

----------------------------
--  Trees
----------------------------
inductive Tree (α : Type*) where
  | leaf (a : α)
  | node : α → List (Tree α) → Tree α
deriving BEq

def Tree.names [DecidableEq α] (t : Tree α) : Finset α :=
  match t with
  | leaf a        => {a}
  | node a children => {a} ∪ children.foldl (fun acc t => acc ∪ t.names) ∅

def isNodeOf [DecidableEq α] (n : α) : (t: Tree α) → Bool :=
  fun t => n ∈ t.names

def isLeafOf [DecidableEq α] (n : α) : Tree α → Bool
  | Tree.leaf a => n == a
  | Tree.node a children =>
      (n != a) &&
      children.foldr (fun t acc => isLeafOf n t || acc) false

def Tree.leaves [DecidableEq α] (t : Tree α) : Finset α :=
  t.names.filter (fun n => isLeafOf n t)

def Tree.internalNodes [DecidableEq α] (t : Tree α) : Finset α :=
  t.names.filter (fun n => ¬ isLeafOf n t)

def Tree.root : Tree α → α
  | Tree.leaf a => a
  | Tree.node a _ => a

def IsSubtreeOf [BEq α] (t₁ t₂ : Tree α) : Bool :=
  t₁ == t₂ ||
  match t₂ with
  | Tree.leaf _ => false
  | Tree.node _ children =>
    children.foldr (fun t acc => IsSubtreeOf t₁ t || acc) false

def Tree.wellFormed [DecidableEq α] (t : Tree α) : Prop :=
  match t with
  | leaf _ => True
  | node a children =>
    Disjoint (children.foldl (fun acc t => acc ∪ t.names) ∅) {a}
    ∧
    children.all (
      fun t =>
      Disjoint t.names (children.foldl (fun acc t => acc ∪ t.names) ∅ \ t.names)
    )

----------------------------
-- Forests
----------------------------

def Forest (α : Type*) := Multiset (Tree α)

def Forest.wellFormed [DecidableEq α] (f : Forest α) : Prop :=
  let trees := f.toList
  (∀ t ∈ trees, Tree.wellFormed t) ∧
  trees.Pairwise (fun t₁ t₂ => Disjoint t₁.names t₂.names)

def subForest [DecidableEq α] (f₁ f₂ : Forest α) : Prop :=
  ∀ t₁ ∈ f₁.toList, ∃ t₂ ∈ f₂.toList, IsSubtreeOf t₁ t₂

noncomputable def Forest.roots [DecidableEq α] : (f : Forest α) → Multiset α
  | f => f.toList.foldl (fun acc t => acc + {t.root}) ∅

----------------------------
-- labels we need for our trees
----------------------------
inductive PropositionTree.Value (Atom : Type u) where
  | atom (a : Atom)
  | atomDual (a : Atom)
  | tensor
  | parr
  | oplus
  | with

-- If we can separate them, could be nice
inductive PropositionTree.Atoms (Atom : Type u) where
  | atom (a : Atom)
  | atomDual (a : Atom)

inductive PropositionTree.Operators (Atom : Type u) where
  | tensor
  | parr
  | oplus
  | with

inductive CoTree.Label (Atom : Type u) where
  | conf
  | conc


----------------------------
-- Trees for formulas and Forests for sequents
----------------------------

def PropositionTree (Atom Name : Type*) [DecidableEq Name] :=
  Σ (t : Tree Name), ({n // n ∈ t.names} → PropositionTree.Value Atom)

def PropositionForest (Atom Name : Type*) [DecidableEq Name] :=
  Σ (f : Forest Name), ∀ t, t ∈ f.toList → PropositionTree.Value Atom

noncomputable def PropositionForest.names [DecidableEq Name] (f : PropositionForest Atom Name) :
  Finset Name :=f.1.toList.foldl (fun acc t => acc ∪ t.names) ∅

def PropositionForest.wellFormed [DecidableEq Name] (f : PropositionForest Atom Name) : Prop :=
  let trees := f.1.toList
  (∀ t ∈ trees, Tree.wellFormed t) ∧
  trees.Pairwise (fun t₁ t₂ => Disjoint t₁.names t₂.names)


----------------------------
-- Formula Tree of a Formula
----------------------------

def formulaTreeOf (F Proposition Atom) [DecidableEq Atom] : PropositionTree Atom Name :=

-- it should keep a buffer to ensure that names are fresh every time we call it recursively,
  sorry


-- theorem : formula tree is wellFormed

-- formula forest of sequent

-- theorem : formula forest is wellFormed



----------------------------
-- Cotrees (for proofnets)
----------------------------


-- CoTree of type a sequent is a tree with leaves subtrees of the formula tree of the sequent, and internal nodes conc or conf

-- CoTree is canonical if no conc or conf node ha either 1 child or children with root the same label

-- a proof structure is a canonical CoTree with leaves atomomic



end ProofNet

end MALL
end Cslib.Logic
