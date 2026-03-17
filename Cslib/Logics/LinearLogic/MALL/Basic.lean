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
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Cslib.Foundations.Data.FinFun
public import Mathlib.Data.List.MinMax

@[expose] public section

/-!
# MALL := (unit-free) Multiplicative Additive Linear Logic
## References
* [J.-Y. Girard, *Linear logic*][Girard1987]

-/

namespace Cslib.Logic


universe u
variable {Atom : Type u}

namespace MALL



/-- Propositions. -/
inductive Proposition (Atom : Type u) : Type u where
  /-- Literals -/
  | atom (x : Atom)
  | atomDual (x : Atom)
  /-- Multiplicative conjunction. -/
  | tensor (a b : Proposition Atom)
  /-- Multiplicative disjunction. -/
  | parr (a b : Proposition Atom)
  /-- Additive  conjunction. -/
  | with (a b : Proposition Atom)
  /-- Additive  disjunction. -/
  | oplus (a b : Proposition Atom)
deriving DecidableEq, BEq

@[inherit_doc] scoped infix:35 " ⊗ " => Proposition.tensor
@[inherit_doc] scoped infix:30 " ⅋ " => Proposition.parr
@[inherit_doc] scoped infix:30 " & " => Proposition.with
@[inherit_doc] scoped infix:35 " ⊕ " => Proposition.oplus

/-- A sequent in MALL is a multiset of propositions. -/
abbrev Sequent Atom := Multiset (Proposition Atom)



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


open Proposition in
/-- A derivation in the sequent calculus for MALL. -/
inductive Derivation : Sequent Atom → Type u where
  | ax : Derivation {a, a⫠}
  | cut : Derivation (a ::ₘ Γ) → Derivation (a⫠ ::ₘ Δ) → Derivation (Γ + Δ)
  | parr : Derivation (a ::ₘ b ::ₘ Γ) → Derivation ((a ⅋ b) ::ₘ Γ)
  | tensor : Derivation (a ::ₘ Γ) → Derivation (b ::ₘ Δ) → Derivation ((a ⊗ b) ::ₘ (Γ + Δ))
  | oplus₁ : Derivation (a ::ₘ Γ) → Derivation ((a ⊕ b) ::ₘ Γ)
  | oplus₂ : Derivation (b ::ₘ Γ) → Derivation ((a ⊕ b) ::ₘ Γ)
  | with : Derivation (a ::ₘ Γ) → Derivation (b ::ₘ Γ) → Derivation ((a & b) ::ₘ Γ)

namespace ProofNet





----------------------------
--  Trees
-- MA we should rename the current trees in the cslib to BinTree,
-- and replace them with these ones
----------------------------

/-- Define Tree data structure, nodes can have any number of children -/
inductive Tree (α : Type*) where
  | leaf (a : α)
  | node (a : α) (children : List (Tree α))
deriving BEq


-- instance {α : Type*} [DecidableEq α] : DecidableEq (Tree α)
-- | Tree.leaf a, Tree.leaf b =>
--   if h : a = b then isTrue (by rw [h]) else isFalse (by intro H; injection H; contradiction)
-- | Tree.node a childrenA, Tree.node b childrenB =>
--   if h1 : a = b then
--     if h2 : childrenA.length = childrenB.length then
--       let decs := List.zipWith (fun t1 t2 => DecidableEq.decEq t1 t2) childrenA childrenB
--       if decs.all (fun d => match d with | isTrue _ => true | _ => false) then
--         isTrue (by
--           intro H
--           injection H with _ hChildren
--           have : childrenA = childrenB := hChildren
--           subst this
--           rfl)
--       else
--         isFalse (by
--           intro H
--           injection H with _ hChildren
--           have : childrenA = childrenB := hChildren
--           subst this
--           have : ¬List.zipWith (fun t1 t2 => DecidableEq.decEq t1 t2) childrenA childrenB |>.all (fun d => match d with | isTrue _ => true | _ => false) := by assumption
--           contradiction)
--     else
--       isFalse (by intro H; injection H with _ hChildren; rw [h1] at hChildren; contradiction)
--   else isFalse (by intro H; injection H with h1 _; contradiction)
-- | _, _ => isFalse (by intro H; cases H)


/-- Names of the nodes in the tree -/
def Tree.names [DecidableEq α] (t : Tree α) : Finset α :=
  match t with
  | leaf a          => {a}
  | node a children => {a} ∪ children.foldl (fun acc t => acc ∪ t.names) ∅

/-- check if a name is in a tree -/
def isNodeOf [DecidableEq α] (n : α) (t : Tree α) : Prop :=
  n ∈ t.names
deriving Decidable

notation:50 n " ∈ " t => isNodeOf n t

/-- Names of the nodes in the tree which are leaves (i.e., no children) -/
def Tree.leaves [DecidableEq α] (t : Tree α) : Finset α :=
  match t with
  | leaf a          => {a}
  | node _ children => children.foldl (fun acc t => acc ∪ t.leaves) ∅

/-- Names of the nodes in the tree which are internal (i.e., have children) -/
def Tree.internalNodes [DecidableEq α] (t : Tree α) : Finset α :=
  t.names.filter (fun n => !(n ∈ t.leaves))

-- returns the root of a tree
def Tree.root (t : Tree α) : Finset α :=
  match t with
  | Tree.leaf a => {a}
  | Tree.node a _ => {a}


/-- Height of a tree, i.e., the length of the longest path from the root -/
def Tree.height : Tree α → ℕ
| Tree.leaf _ => 0
| Tree.node _ children =>
  1 + List.foldl max 0 (children.map Tree.height)


/-- Height of a tree, i.e., the length of the longest path from the root -/
def Tree.size : Tree α → ℕ
| Tree.leaf _ => 1
| Tree.node _ children =>
  1 + List.sum (children.map Tree.size)


lemma max_le_sum {a b c d : ℕ} (h1 : a ≤ c) (h2 : b ≤ d) : max a b ≤ c + d := by
  cases  (Nat.le_total a b)
  case inl h =>
    omega
  case inr h =>
    omega



theorem Tree.boundHeight {t : Tree α} : t.height ≤ t.size := by
  match t with
  | leaf a =>
    simp [Tree.height, Tree.size]
  | node a children =>
    simp [Tree.height, Tree.size]
    induction children with
    | nil => simp
    | cons head tail ih =>
      simp [List.map]
      rw [List.foldl_max]
      apply max_max_le_sum_sum
      · exact Tree.boundHeight (t := head)
      · rw [List.foldl_max] at ih
        rw [List.foldl_max]

--- MI SENTO STUPIDO






/-- Check that each name appears at most once in a tree -/
def Tree.wellFormed [DecidableEq α] (t : Tree α) : Prop :=
  match t with
  | Tree.leaf _ => True
  | Tree.node _ children =>
    t.names.card = t.size
    ∧
    children ≠ []
    ∧
    (∀ t ∈ children, Tree.wellFormed t)







----------------------------
-- Forests
----------------------------

-- forest is a multiset of trees
def Forest (α : Type*) := Multiset (Tree α)

-- well formed forest is a forest where all nodes have disjoint names
def Forest.wellFormed [DecidableEq α] (f : Forest α) : Prop :=
  let trees := f.toList
  (∀ t ∈ trees, Tree.wellFormed t) ∧
  trees.Pairwise (fun t₁ t₂ => Disjoint t₁.names t₂.names)

-- returns the set of names in a forest
noncomputable def Forest.names [DecidableEq α] (f : Forest α) : Finset α :=
  f.toList.foldl (fun acc t => acc ∪ t.names) ∅

-- returns the set of roots of the trees in a forest
noncomputable def Forest.roots [DecidableEq α] (f : Forest α) : Finset α :=
  f.toList.foldl (fun acc t => acc ∪ t.root) ∅

-- check if a name is in the forest, and defines the notation for it
def isTreeInForest [DecidableEq α] (t : Tree α) (f : Forest α) : Prop :=
  t ∈ f.toList



notation:50 t " ∈ₜ " f => isTreeInForest t f


----------------------------
-- labels we need for our trees
----------------------------
inductive FormulaTree.Value (Label : Type u) where
  | atom (a : Label)
  | atomDual (a : Label)
  | tensor
  | parr
  | oplus
  | with


def isLiteral [DecidableEq Label] (v : FormulaTree.Value Label) : Prop :=
  match v with
  | .atom _ => True
  | .atomDual _ => True
  | _ => False

inductive CoTree.Label (Label : Type u) where
  | conf
  | conc


----------------------------
-- Formula-trees
----------------------------

-- A tree of nodes labeled by formulas
def FormulaTree (Atom Nat : Type*) [DecidableEq Nat] :=
  Σ (t : Tree Nat), ({ n : Nat // n ∈ t } → FormulaTree.Value Atom)

-- Check that a formula tree is well-formed
def FormulaTree.wellFormed [DecidableEq Nat] (t : FormulaTree Atom Nat ) : Prop :=
  let ⟨tree, labeling⟩ := t
  Tree.wellFormed tree ∧
  ∀ (n : Nat) (hn : n ∈ tree),
    match labeling ⟨n, hn⟩ with
    | .atom _     => n ∈ tree.leaves
    | .atomDual _ => n ∈ tree.leaves
    | .tensor     => n ∉ tree.leaves
    | .parr       => n ∉ tree.leaves
    | .oplus      => n ∉ tree.leaves
    | .with       => n ∉ tree.leaves


-- homogenous view on binary connectives
inductive BinOp
| tensor | parr | with | oplus
deriving DecidableEq, BEq

def viewBin {Atom : Type} :
Proposition Atom → Option (BinOp × Proposition Atom × Proposition Atom)
| Proposition.tensor A B  => some (BinOp.tensor, A, B)
| Proposition.parr A B    => some (BinOp.parr, A, B)
| Proposition.with A B    => some (BinOp.with, A, B)
| Proposition.oplus A B   => some (BinOp.oplus, A, B)
| _                       => none

def prop_to_indexed_formulaTree {Atom : Type} (p : Proposition Atom) (counter : Nat) :
Nat × FormulaTree Atom Nat :=
  match p with
  | .atom a => (counter + 1, ⟨Tree.leaf counter, fun _ => .atom a⟩)
  | .atomDual a => (counter + 1, ⟨Tree.leaf counter, fun _ => .atomDual a⟩)
  | .tensor A B
  | .parr A B
  | .oplus A B
  | .with A B  =>
    let (counter₁, FormTree₁) := prop_to_indexed_formulaTree A counter
    let (counter₂, FormTree₂) := prop_to_indexed_formulaTree B counter₁
    let op := match p with
      | .tensor _ _ => .tensor
      | .parr _ _ => .parr
      | .oplus _ _ => .oplus
      | .with _ _ => .with
      | _ => .tensor -- this case is impossible, but we need to put something here
    (counter₂, ⟨Tree.node counter [FormTree₁.1, FormTree₂.1], fun n =>
      if h₁ : n.1 ∈ FormTree₁.1 then FormTree₁.2 ⟨n.1, h₁⟩
      else if h₂ : n.1 ∈ FormTree₂.1 then FormTree₂.2 ⟨n.1, h₂⟩
      else op⟩)
  -- | .tensor A B =>
  --   let (counter₁, FormTree₁) := prop_to_indexed_formulaTree A counter
  --   let (counter₂, FormTree₂) := prop_to_indexed_formulaTree B counter₁
  --   (counter₂, ⟨Tree.node counter [FormTree₁.1, FormTree₂.1], fun n =>
  --     if h₁ : n.1 ∈ FormTree₁.1 then FormTree₁.2 ⟨n.1, h₁⟩
  --     else if h₂ : n.1 ∈ FormTree₂.1 then FormTree₂.2 ⟨n.1, h₂⟩
  --     else .tensor⟩)
  -- | .parr A B =>
  --   let (counter₁, FormTree₁) := prop_to_indexed_formulaTree A counter
  --   let (counter₂, FormTree₂) := prop_to_indexed_formulaTree B counter₁
  --   (counter₂, ⟨Tree.node counter [FormTree₁.1, FormTree₂.1], fun n =>
  --     if h₁ : n.1 ∈ FormTree₁.1 then FormTree₁.2 ⟨n.1, h₁⟩
  --     else if h₂ : n.1 ∈ FormTree₂.1 then FormTree₂.2 ⟨n.1, h₂⟩
  --     else .parr⟩)
  -- | .oplus A B =>
  --   let (counter₁, FormTree₁) := prop_to_indexed_formulaTree A counter
  --   let (counter₂, FormTree₂) := prop_to_indexed_formulaTree B counter₁
  --   (counter₂, ⟨Tree.node counter [FormTree₁.1, FormTree₂.1], fun n =>
  --     if h₁ : n.1 ∈ FormTree₁.1 then FormTree₁.2 ⟨n.1, h₁⟩
  --     else if h₂ : n.1 ∈ FormTree₂.1 then FormTree₂.2 ⟨n.1, h₂⟩
  --     else .oplus⟩)
  -- | .with A B  =>
  --   let (counter₁, FormTree₁) := prop_to_indexed_formulaTree A counter
  --   let (counter₂, FormTree₂) := prop_to_indexed_formulaTree B counter₁
  --   (counter₂, ⟨Tree.node counter [FormTree₁.1, FormTree₂.1], fun n =>
  --     if h₁ : n.1 ∈ FormTree₁.1 then FormTree₁.2 ⟨n.1, h₁⟩
  --     else if h₂ : n.1 ∈ FormTree₂.1 then FormTree₂.2 ⟨n.1, h₂⟩
  --     else .with⟩)

def prop_to_formulaTree {Atom : Type} (p : Proposition Atom) : FormulaTree Atom Nat :=
  (prop_to_indexed_formulaTree p 0).2


#check prop_to_formulaTree (Proposition.oplus (Proposition.atom "a") (Proposition.tensor (Proposition.atom "b") (Proposition.atomDual "c")))

theorem propToFormulaTree_is_wellFormed {Atom : Type}
  (p : Proposition Atom) : (prop_to_formulaTree p).wellFormed := by
  induction p
  case atom a =>
    simp [prop_to_formulaTree, prop_to_indexed_formulaTree]
    constructor
    · simp [Tree.wellFormed]
    · intros n hn


----------------------------
-- Formula-forests (sequents)
----------------------------

-- A forest of formulas labeled by Nodes
def FormulaForest (Atom Nat : Type u) [DecidableEq Nat] :=
  Σ (f : Forest Nat), (t : { t : Tree Nat // t ∈ₜ f }) →
    (n : { n : Nat // n ∈ t }) → FormulaTree.Value Atom


-- Check that a formula forest is well-formed
def FormulaForest.wellFormed {Atom Nat : Type u} [DecidableEq Nat]
  (f : FormulaForest Atom Nat) : Prop :=
  let ⟨forest, labeling⟩ := f
  Forest.wellFormed forest
  ∧
  ∀ (t : { t : Tree Nat // t ∈ₜ forest }) (n : { n : Nat // n ∈ t }),
    match labeling t n with
    | .atom _     => n.1 ∈ t.1.leaves
    | .atomDual _ => n.1 ∈ t.1.leaves
    | .tensor     => n.1 ∉ t.1.leaves
    | .parr       => n.1 ∉ t.1.leaves
    | .oplus      => n.1 ∉ t.1.leaves
    | .with       => n.1 ∉ t.1.leaves


-- check if a formula tree is in the formula forest
def FormulaTree_in_FormulaForest {Atom Nat : Type u} [DecidableEq Nat]
  (t : FormulaTree Atom Nat)
  (f : FormulaForest Atom Nat) : Prop :=
  ∃ (ht : t.1 ∈ₜ f.1),
    ∀ (n : Nat) (hn : n ∈ t.1),
      t.2 ⟨n, hn⟩ = f.2 ⟨t.1, ht⟩ ⟨n, hn⟩

-- check if a forest is a subforest of another forest
def subForest {Atom Nat : Type u} [DecidableEq Nat] (f₁ f₂ : FormulaForest Atom Nat) : Prop :=
  ∀ t₁ : FormulaTree Atom Nat,
    FormulaTree_in_FormulaForest t₁ f₁ → FormulaTree_in_FormulaForest  t₁ f₂



-- ----------------------------
-- -- Cotrees (for proofnets)
-- ----------------------------


-- -- CoTree of type a sequent is a tree with leaves subtrees
-- -- of the formula tree of the sequent, and internal nodes conc or conf

-- -- CoTree is canonical if no conc or conf node has either 1 child
-- -- or children with root the same label

-- -- a proof structure is a canonical CoTree with leaves atomomic



end ProofNet

end MALL
end Cslib.Logic
