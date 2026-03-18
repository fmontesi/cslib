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
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Interval.Finset.Defs


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
  | lwith (a b : Proposition Atom)
  /-- Additive  disjunction. -/
  | oplus (a b : Proposition Atom)
deriving DecidableEq, BEq

@[inherit_doc] scoped infix:35 " ⊗ " => Proposition.tensor
@[inherit_doc] scoped infix:30 " ⅋ " => Proposition.parr
@[inherit_doc] scoped infix:30 " & " => Proposition.lwith
@[inherit_doc] scoped infix:35 " ⊕ " => Proposition.oplus

/-- A sequent in MALL is a multiset of propositions. -/
abbrev Sequent Atom := Multiset (Proposition Atom)


def Proposition.isAtomic (p : Proposition Atom) : Prop :=
  match p with
  | .atom _ | .atomDual _ => True
  | _ => False


/-- Propositional duality. -/
@[scoped grind =]
def Proposition.dual : Proposition Atom → Proposition Atom
  | atom x => atomDual x
  | atomDual x => atom x
  | tensor a b => parr a.dual b.dual
  | parr a b => tensor a.dual b.dual
  | oplus a b => lwith a.dual b.dual
  | lwith a b => oplus a.dual b.dual

@[inherit_doc] scoped postfix:max "⫠" => Proposition.dual



/-- Duality preserves size. -/
theorem Proposition.dual_sizeOf (a : Proposition Atom) : sizeOf a = sizeOf a⫠ := by
  induction a <;> simp [dual] <;> grind




open Proposition in
/-- A derivation in the sequent calculus for MALL. -/
inductive Derivation : Sequent Atom → Type u where
  | ax : Derivation {a, a⫠}
  | cut : Derivation (a ::ₘ Γ) → Derivation (a⫠ ::ₘ Δ) → Derivation (Γ + Δ)
  | parr : Derivation (a ::ₘ b ::ₘ Γ) → Derivation ((a ⅋ b) ::ₘ Γ)
  | tensor : Derivation (a ::ₘ Γ) → Derivation (b ::ₘ Δ) → Derivation ((a ⊗ b) ::ₘ (Γ + Δ))
  | oplus₁ : Derivation (a ::ₘ Γ) → Derivation ((a ⊕ b) ::ₘ Γ)
  | oplus₂ : Derivation (b ::ₘ Γ) → Derivation ((a ⊕ b) ::ₘ Γ)
  | lwith : Derivation (a ::ₘ Γ) → Derivation (b ::ₘ Γ) → Derivation ((a & b) ::ₘ Γ)

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


-- DecidableEq Tree defined by mutual induction on tree and lists
mutual
  def Tree.decEq {α : Type*} [DecidableEq α] : DecidableEq (Tree α)
    | .leaf a, .leaf b => by
        cases (inferInstance : DecidableEq α) a b with
        | isTrue  h  => exact isTrue (by rw [h])
        | isFalse h => exact isFalse (by intro H; injection H; exact h ‹_›)
    | .leaf _, .node _ _  => isFalse (by intro H; injection H)
    | .node _ _, .leaf _  => isFalse (by intro H; injection H)
    | .node a chindrenA, .node b chindrenB => by
        cases (inferInstance : DecidableEq α) a b with
        | isFalse h => exact isFalse (by intro H; injection H; exact h ‹_›)
        | isTrue  h  =>
            cases Tree.decEqList chindrenA chindrenB with
            | isTrue  h2  => exact isTrue (by rw [h, h2])
            | isFalse h2 => exact isFalse (by intro H; injection H; exact h2 ‹_›)

  def Tree.decEqList {α : Type*} [DecidableEq α] : DecidableEq (List (Tree α))
    | [], []           => isTrue  (by rfl)
    | [], _ :: _       => isFalse (by intro H; injection H)
    | _ :: _, []       => isFalse (by intro H; injection H)
    | h₁ :: t₁, h₂ :: t₂ => by
        cases Tree.decEq h₁ h₂ with
        | isFalse h => exact isFalse (by intro H; injection H; exact h ‹_›)
        | isTrue  h  =>
            cases Tree.decEqList t₁ t₂ with
            | isTrue  h2  => exact isTrue (by rw [h, h2])
            | isFalse h2 => exact isFalse (by intro H; injection H; exact h2 ‹_›)
end

instance {α : Type*} [DecidableEq α] : DecidableEq (Tree α) := Tree.decEq



private def Tree.indHelper {α : Type*} {P : Tree α → Prop}
    (hleaf : ∀ a, P (leaf a))
    (hnode : ∀ a children, (∀ t ∈ children, P t) → P (node a children)) :
    ∀ (t : Tree α), P t
  | .leaf a => hleaf a
  | .node a children =>
    hnode a children (fun t ht =>
      let rec listHelper : ∀ (l : List (Tree α)), ∀ t ∈ l, P t
        | [], _, h => absurd h (nofun)
        | x :: xs, t, h =>
            (List.mem_cons.mp h).elim
              (fun hx => hx ▸ Tree.indHelper hleaf hnode x)
              (fun hxs => listHelper xs t hxs)
      listHelper children t ht)

theorem Tree.ind {α : Type*} {P : Tree α → Prop}
    (hleaf : ∀ a, P (leaf a))
    (hnode : ∀ a children, (∀ t ∈ children, P t) → P (node a children))
    (t : Tree α) : P t := Tree.indHelper hleaf hnode t






def List.fUnion [DecidableEq α] (l : List (Finset α)) : Finset α := l.foldl (· ∪ ·) ∅

/-- Names of the nodes in the tree -/
def Tree.names [DecidableEq α] (t : Tree α) : Finset α :=
  match t with
  | leaf a          => {a}
  | node a children => {a} ∪ List.fUnion (children.map Tree.names)

/-- check if a name is in a tree -/
def isNodeOf [DecidableEq α] (n : α) (t : Tree α) : Prop :=
  n ∈ t.names
deriving Decidable

notation:50 n " ∈ " t => isNodeOf n t

/-- Names of the nodes in the tree which are leaves (i.e., no children) -/
def Tree.leaves [DecidableEq α] (t : Tree α) : Finset α :=
  match t with
  | leaf a          => {a}
  | node _ children => List.fUnion (children.map Tree.leaves)

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

/-- Lemma to prove boundHeight -/
-- MA this should go in the basic arithmetic file, but I need it here for now
lemma max_le_sum {a b c d : ℕ} (h1 : a ≤ c) (h2 : b ≤ d) : max a b ≤ c + d := by
  cases  (Nat.le_total a b)
  case inl h =>
    omega
  case inr h =>
    omega


-- MA the two following should go in some basic list file, but I need it here for now
lemma foldl_max_cons (a : ℕ) (l : List ℕ) :
    List.foldl max a l = max a (List.foldl max 0 l) := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl]
    rw [ih (max a x), ih (max 0 x)]
    omega

lemma foldl_max_le_sum {α : Type*} {f g : α → ℕ} {l : List α}
    (h : ∀ x ∈ l, f x ≤ g x) :
    List.foldl max 0 (l.map f) ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map, List.sum_cons, List.foldl, Nat.zero_max]
    rw [foldl_max_cons]
    have h1 := h head (by simp)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact max_le_sum h1 h2


/-- The height of a tree is bounded by its size -/
theorem Tree.boundHeight {α : Type*} {t : Tree α} : t.height ≤ t.size := by
  induction t using Tree.ind with
   | hleaf a => simp [Tree.height, Tree.size]
   | hnode a children ih =>
     simp [Tree.height, Tree.size]
     exact foldl_max_le_sum ih


/-- Check that each name appears at most once in a tree -/
def Tree.wellFormed [DecidableEq α] (t : Tree α) : Prop :=
  match t with
  | Tree.leaf _ => True
  | Tree.node a children =>
    (∀ t ∈ children, Tree.wellFormed t)
    ∧
    children ≠ []
    ∧
    (∀ t ∈ children, a ∉ t.names)
    ∧
    (∀ t ∈ children, ∀ t' ∈ children, t ≠ t' → t.names ∩ (t'.names) = ∅)



lemma treeWellformed_iff_sizeOfNames_eq_size {α : Type*} [DecidableEq α] (t : Tree α) :
  Tree.wellFormed t ↔ t.names.card = t.size := by
  induction t using Tree.ind with
  | hleaf a => simp [Tree.wellFormed, Tree.names, Tree.size]
  | hnode a children ih =>
    simp [Tree.wellFormed, Tree.names, Tree.size]
    constructor
    · intro h
      have h1 := h.1
      have h2 := h.2.1
      have h3 := h.2.2.1
      have h4 := h.2.2.2
      sorry



----------------------------
-- Forests
----------------------------

-- forest is a list of trees
def Forest (α : Type*) := List (Tree α)

-- well formed forest is a forest where all nodes have disjoint names
def Forest.wellFormed {α : Type*} [DecidableEq α] (f : Forest α) : Prop :=
  (∀ t, List.Mem t f -> Tree.wellFormed t)
  ∧
  List.Pairwise (fun t₁ t₂ => Disjoint t₁.names t₂.names) f

-- returns the set of names in a forest
def Forest.names [DecidableEq α] (f : Forest α) : Finset α :=
  List.fUnion (f.map Tree.names)

-- returns the set of roots of the trees in a forest
def Forest.roots [DecidableEq α] (f : Forest α) : Finset α :=
  List.fUnion (f.map Tree.root)



----------------------------
-- labels we need for our trees
----------------------------
inductive FormulaTree.Value (Label : Type u) where
  | atom (a : Label)
  | atomDual (a : Label)
  | tensor
  | parr
  | oplus
  | lwith


def isLiteral [DecidableEq Label] (v : FormulaTree.Value Label) : Prop :=
  match v with
  | .atom _ => True
  | .atomDual _ => True
  | _ => False

----------------------------
-- Formula-trees
----------------------------

-- A tree of nodes labeled by formulas
def FormulaTree (Atom Nat : Type*) [DecidableEq Nat] :=
  Σ (t : Tree Nat), ({ n : Nat // n ∈ t } → FormulaTree.Value Atom)


-- Check that a formula tree is well-formed
def FormulaTree.wellFormed {Atom : Type*} [DecidableEq Nat] [DecidableEq Atom]
  (t : FormulaTree Atom Nat) : Prop :=
  t.1.wellFormed
  ∧
  ∀ (n : Nat) (hn : n ∈ t.1), (n ∈ t.1.leaves) → isLiteral (t.2 ⟨n, hn⟩)

-- homogenous view on binary connectives
inductive BinOp
| tensor | parr | lwith | oplus
deriving DecidableEq, BEq

def viewBin {Atom : Type} :
Proposition Atom → Option (BinOp × Proposition Atom × Proposition Atom)
| Proposition.tensor A B  => some (BinOp.tensor, A, B)
| Proposition.parr A B    => some (BinOp.parr, A, B)
| Proposition.lwith A B    => some (BinOp.lwith, A, B)
| Proposition.oplus A B   => some (BinOp.oplus, A, B)
| _                       => none


-- Convert a proposition to a formula tree, labeling the nodes with natural numbers
def prop_to_indexed_formulaTree {Atom : Type} (p : Proposition Atom) (counter : Nat) : (FormulaTree Atom Nat) × Nat :=
  match p with
  | .atom a => (⟨Tree.leaf counter, fun _ => .atom a⟩, counter + 1)
  | .atomDual a => (⟨Tree.leaf counter, fun _ => .atomDual a⟩, counter + 1)
  | .tensor A B
  | .parr A B
  | .oplus A B
  | .lwith A B  =>
    let (FormTree₁,counter₁) := prop_to_indexed_formulaTree A (counter+1)
    let (FormTree₂,counter₂) := prop_to_indexed_formulaTree B counter₁
    let op := match p with
      | Proposition.tensor _ _ => FormulaTree.Value.tensor
      | Proposition.parr _ _ => FormulaTree.Value.parr
      | Proposition.oplus _ _ => FormulaTree.Value.oplus
      | Proposition.lwith _ _ => FormulaTree.Value.lwith
      | _ => FormulaTree.Value.tensor -- escape
    (⟨Tree.node counter [FormTree₁.1, FormTree₂.1], fun n =>
      if h₁ : n.1 ∈ FormTree₁.1 then FormTree₁.2 ⟨n.1, h₁⟩
      else if h₂ : n.1 ∈ FormTree₂.1 then FormTree₂.2 ⟨n.1, h₂⟩
      else op⟩, counter₂)

def prop_to_formulaTree {Atom : Type} (p : Proposition Atom) : (FormulaTree Atom Nat) :=
  (prop_to_indexed_formulaTree p 0).1

/--The value of the second component returned by the indexed formula tree constructor minus the initial counter is the size of the formula tree -/
lemma indexed_formulaTree_snd_minus_seed_is_size {Atom : Type} (p : Proposition Atom) (n : ℕ) :
    (prop_to_indexed_formulaTree p n).2 = n + sizeOf p := by
  induction p generalizing n with
  | atom a | atomDual a =>
    simp [prop_to_indexed_formulaTree, Tree.size, sizeOf]
    exact Nat.eq_of_beq_eq_true rfl
  | tensor A B ihA ihB | parr A B ihA ihB | oplus A B ihA ihB | lwith A B ihA ihB =>
    simp [prop_to_indexed_formulaTree, Tree.size]
    rw [ihA, ihB]
    omega


lemma formulaTree_size_is_formula_size {Atom : Type} (p : Proposition Atom) (n : ℕ) :
    (prop_to_indexed_formulaTree p n).1.1.size = sizeOf p := by
    induction p generalizing n with
    | atom a | atomDual a =>
      simp [prop_to_indexed_formulaTree, Tree.size]
    | tensor A B ihA ihB | parr A B ihA ihB | oplus A B ihA ihB | lwith A B ihA ihB =>
      simp [prop_to_indexed_formulaTree, Tree.size]
      rw [ihA, ihB]
      omega


lemma prop_to_indexed_formulaTree_names {Atom : Type} (p : Proposition Atom) (n : Nat) :
    (prop_to_indexed_formulaTree p n).1.1.names = Finset.Ico n (n + sizeOf p) := by
  induction p generalizing n with
  | atom a | atomDual a=>
    simp [prop_to_indexed_formulaTree, Tree.names]
  | tensor A B ihA ihB | parr A B ihA ihB | oplus A B ihA ihB | lwith A B ihA ihB =>
    simp [Tree.names, prop_to_indexed_formulaTree]
    rw [ihA _, ihB _, indexed_formulaTree_snd_minus_seed_is_size]
    ext x
    simp [Finset.mem_insert,List.fUnion,Finset.mem_Ico]
    omega

lemma prop_to_formulaTree_names {Atom : Type} (p : Proposition Atom) :
    (prop_to_indexed_formulaTree p n).1.1.names = Finset.Ico n (n + sizeOf p) := by
  simp [prop_to_indexed_formulaTree_names p n]


lemma prop_to_formulaTree_atomic {Atom : Type} (p : Proposition Atom) :
    p.isAtomic → (prop_to_formulaTree p).1.leaves = (prop_to_formulaTree p).1.names := by
    intro patom
    match p with
    | .atom a | .atomDual a =>
      simp [prop_to_formulaTree, prop_to_indexed_formulaTree, Tree.leaves, Tree.names]


theorem propToFormulaTree_is_wellFormed {Atom : Type} [DecidableEq Atom]
  (p : Proposition Atom) : (prop_to_formulaTree p).wellFormed := by
  induction p with
  | atom a | atomDual a =>
    simp [prop_to_formulaTree,prop_to_indexed_formulaTree,FormulaTree.wellFormed]
    constructor
    simp [Tree.wellFormed]
    simp [isLiteral]
  | tensor A B ihA ihB | parr A B ihA ihB | oplus A B ihA ihB | lwith A B ihA ihB =>
    simp [prop_to_formulaTree, prop_to_indexed_formulaTree, FormulaTree.wellFormed]
    constructor
    · simp [Tree.wellFormed]
      constructor
      constructor
      simp [prop_to_formulaTree] at ihA
      sorry
    · intro n hn node
      simp [isLiteral]
      sorry




  -- | .tensor A B | .parr A B | .oplus A B | .lwith A B =>
    -- simp [prop_to_formulaTree, FormulaTree.wellFormed]
    -- constructor

----------------------------
-- Formula-forests (sequents)
----------------------------

-- A forest of formulas labeled by Nodes
def FormulaForest (Atom Nat : Type u) [DecidableEq Nat] :=
  Σ (f : Forest Nat), (t : { t : Tree Nat // List.Mem t f }) →
    (n : { n : Nat // n ∈ t.1 }) → FormulaTree.Value Atom


-- Check that a formula forest is well-formed
def FormulaForest.wellFormed {Atom Nat : Type u} [DecidableEq Nat]
  (f : FormulaForest Atom Nat) : Prop :=
  let ⟨forest, labeling⟩ := f
  Forest.wellFormed forest
  ∧
  ∀ (t : { t : Tree Nat // List.Mem t forest }) (n : { n : Nat // n ∈ t.1 }),
    match labeling t n with
    | .atom _     => n.1 ∈ t.1.leaves
    | .atomDual _ => n.1 ∈ t.1.leaves
    | .tensor     => n.1 ∉ t.1.leaves
    | .parr       => n.1 ∉ t.1.leaves
    | .oplus      => n.1 ∉ t.1.leaves
    | .lwith       => n.1 ∉ t.1.leaves


-- check if a formula tree is in the formula forest
def FormulaTree_in_FormulaForest {Atom Nat : Type u} [DecidableEq Nat]
  (t : FormulaTree Atom Nat)
  (f : FormulaForest Atom Nat) : Prop :=
  ∃ (ht : List.Mem t.1 f.1),
    ∀ (n : Nat) (hn : n ∈ t.1),
      t.2 ⟨n, hn⟩ = f.2 ⟨t.1, ht⟩ ⟨n, hn⟩

-- check if a forest is a subforest of another forest
def subForest {Atom Nat : Type u} [DecidableEq Nat] (f₁ f₂ : FormulaForest Atom Nat) : Prop :=
  ∀ t₁ : FormulaTree Atom Nat,
    FormulaTree_in_FormulaForest t₁ f₁ → FormulaTree_in_FormulaForest  t₁ f₂



-- ----------------------------
-- -- Cotrees (for proofnets)
-- ----------------------------


inductive CoTree.Label (Label : Type u) where
  | conf
  | conc


-- -- CoTree of type a sequent is a tree with leaves subtrees
-- -- of the formula tree of the sequent, and internal nodes conc or conf

-- -- CoTree is canonical if no conc or conf node has either 1 child
-- -- or children with root the same label

-- -- a proof structure is a canonical CoTree with leaves atomomic



end ProofNet

end MALL
end Cslib.Logic







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
