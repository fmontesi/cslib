import Cslib.Foundations.Semantics.LTS.Bisimulation
import Cslib.Foundations.Concurrency.Basic
import Cslib.Foundations.Relation.Confluence
import Mathlib.Data.List.Basic

/-! Luc's playground
  With help from DeepSeek-V4.1-Flash-1017.
-/

namespace Cslib.Concurrency

-- placeholder characterisation of sane' alphabet
def SaneAlphabet (_ : Type*) : Prop :=
  true

-- identify conditionals and matching sets of labels within an alphabet
structure Branching (α : Type*) where
  conditional : α → Prop
  matching : α → α → Prop
  [symm : Std.Symm matching]
  [irrefl : Std.Irrefl matching]

attribute [instance] Branching.symm

variable {State Label : Type*}

-- Defines a set of smurf LTSs.
structure Smurf (lts : LTS State Label) (I : Label → Label → Prop) [Independence I]
    (B : Branching Label) where
  -- labelling alphabet should be sane
  s : SaneAlphabet Label
  -- conditionals should come in matching sets
  m : ∀ s s₁ l₁, B.conditional l₁ ∧ lts.Tr s l₁ s₁ →
    ∃ l₂ s₂, B.matching l₁ l₂ ∧ lts.Tr s l₂ s₂
  -- no local concurrency
  -- distinct pairs of outgoing transitions are either independent or part of a matching set
  u : ∀ s s₁ s₂ l₁ l₂, l₁ ≠ l₂ → lts.Tr s l₁ s₁ ∧ lts.Tr s l₂ s₂ →
    I l₁ l₂ ∨ B.matching l₁ l₂
  -- backward concurrency
  r : ∀ s s₁ l₁ l₂, I l₁ l₂ ∧ lts.MTr s [l₁, l₂] s₁ →
    ∃ s₂, lts.Tr s l₂ s₂
  -- forward concurrency (diamond)
  f : ∀ s s₁ s₂ l₁ l₂, I l₁ l₂ ∧ lts.Tr s l₁ s₁ ∧ lts.Tr s l₂ s₂ →
    ∃ s₃, lts.Tr s₁ l₂ s₃ ∧ lts.Tr s₂ l₁ s₃
  -- the LTS is deterministic
  d : ∀ s s₁ s₂ l, lts.Tr s l s₁ → lts.Tr s l s₂ → s₁ = s₂

variable {Pid : Type*} [DecidableEq Pid]

-- projection of an execution trace onto a process
def ProjectTrace {pn : Label → Finset Pid} (lst : List Label) (p : Pid) : List Label :=
  lst.filter (fun l => decide (p ∈ pn l))

/-- Split a trace at its last step; the prefix still starts at the original state. -/
lemma mtr_split_last
    {s s' : State}
    {l : List Label}
    {a : Label}
    {lts : LTS State Label}
    (h : lts.MTr s (l ++ [a]) s')
  : ∃ sm, lts.MTr s l sm ∧ lts.Tr sm a s'
  := by
    obtain ⟨sm, h1, h2⟩ := LTS.MTr.split h
    exact ⟨sm, h1, LTS.MTr.single_invert lts _ _ _ h2⟩

section Helpers

variable {pn : Label → Finset Pid} {lts : LTS State Label}
  {I : Label → Label → Prop} [Independence I] {B : Branching Label}
  {hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂)}
  {hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → pn l₁ = pn l₂}

/-- If `p` does not observe any label of `u`, then `u` projects to the empty trace. -/
private lemma projectTrace_eq_nil {u : List Label} {p : Pid}
    (h : ∀ l ∈ u, p ∉ pn l) : ProjectTrace (pn := pn) u p = [] := by
  induction u with
  | nil => rfl
  | cons a t ih =>
    have ha : p ∉ pn a := h a (by simp)
    have ht : ProjectTrace (pn := pn) t p = [] :=
      ih (fun l hl => h l (by simp [hl]))
    rw [ProjectTrace, List.filter_cons, decide_eq_false ha]
    exact ht

omit [DecidableEq Pid] in
/-- `B.matching` is symmetric. -/
private lemma matching_comm {a b : Label} (h : B.matching a b) : B.matching b a :=
  Std.Symm.symm (r := B.matching) (a := a) (b := b) h

/-! ### Trace equivalence

Independent adjacent labels can be exchanged inside an execution, using backward
concurrency (`Smurf.r`) to bring the second one forward, forward concurrency
(`Smurf.f`) to compare the two orders, and determinism (`Smurf.d`) to identify the
targets.  Consequently an execution is determined by its *trace*, i.e. by its label
list up to `List.PermUpTo I`. -/

omit [DecidableEq Pid] in
/-- Adjacent independent labels can be exchanged inside an execution. -/
private lemma mtr_swap_indep (h : Smurf lts I B) {a b : Label} (hab : I a b)
    {α γ : List Label} {s t : State} (hm : lts.MTr s (α ++ a :: b :: γ) t) :
    lts.MTr s (α ++ b :: a :: γ) t := by
  obtain ⟨s₁, hα, hm'⟩ := LTS.MTr.split hm
  obtain ⟨s₂, htra, hm''⟩ := LTS.MTr.cons_iff.mp hm'
  obtain ⟨s₃, htrb, hγ⟩ := LTS.MTr.cons_iff.mp hm''
  -- `b` is available before `a`
  have h2 : lts.MTr s₁ [a, b] s₃ := .stepL htra (.stepL htrb .refl)
  obtain ⟨s₂', htrb'⟩ := h.r s₁ s₃ a b ⟨hab, h2⟩
  -- the forward diamond compares the two orders
  obtain ⟨s₃', hb, ha⟩ := h.f s₁ s₂ s₂' a b ⟨hab, htra, htrb'⟩
  have hEq : s₃' = s₃ := h.d s₂ s₃' s₃ b hb htrb
  subst hEq
  exact LTS.MTr.comp lts hα (.stepL htrb' (.stepL ha hγ))

omit [DecidableEq Pid] in
/-- Executions are determined by their trace: `List.PermUpTo I`-equivalent label lists
describe executions between the same two states. -/
private lemma mtr_permUpTo (h : Smurf lts I B) {u v : List Label}
    (hp : List.PermUpTo I u v) :
    ∀ {s t : State}, lts.MTr s u t → lts.MTr s v t := by
  induction hp with
  | nil => exact fun hm => hm
  | cons a _ ih =>
    intro s t hm
    obtain ⟨s₁, htr, hm'⟩ := LTS.MTr.cons_iff.mp hm
    exact .stepL htr (ih hm')
  | swap a b w hI =>
    intro s t hm
    have hab : I a b := hI.elim id (fun hba => Std.Symm.symm (r := I) (a := b) (b := a) hba)
    exact mtr_swap_indep h hab (α := []) (γ := w) hm
  | trans _ _ ih₁ ih₂ => exact fun hm => ih₂ (ih₁ hm)

/-- In a deterministic LTS the end state of a trace is determined by its labels. -/
private lemma mtr_det (hd : ∀ s s₁ s₂ l, lts.Tr s l s₁ → lts.Tr s l s₂ → s₁ = s₂)
    {s s₁ s₂ : State} {u : List Label} (h1 : lts.MTr s u s₁) (h2 : lts.MTr s u s₂) :
    s₁ = s₂ := by
  induction u generalizing s with
  | nil => exact (LTS.MTr.nil_eq lts h1).symm.trans (LTS.MTr.nil_eq lts h2)
  | cons a t ih =>
    obtain ⟨sa1, hta1, ht1⟩ := LTS.MTr.cons_iff.mp h1
    obtain ⟨sa2, hta2, ht2⟩ := LTS.MTr.cons_iff.mp h2
    rw [hd s sa1 sa2 a hta1 hta2] at ht1
    exact ih ht1 ht2

omit [DecidableEq Pid] in
/-- Executions along trace-equivalent label lists end in the same state. -/
private lemma mtr_det_permUpTo (h : Smurf lts I B) {u v : List Label}
    (hp : List.PermUpTo I u v) {s t₁ t₂ : State}
    (h₁ : lts.MTr s u t₁) (h₂ : lts.MTr s v t₂) : t₁ = t₂ :=
  (mtr_det h.d h₂ (mtr_permUpTo h hp h₁)).symm

-- backward concurrency extended to trace and label
-- t commutes past its prefix l
private lemma backward_concurrency_trace_label
    {lts : LTS State Label}
    {I : Label → Label → Prop}
    [Independence I]
    {B : Branching Label}
    (h : Smurf lts I B)
    (t : List Label)
    (l : Label)
    (s sₗ sₗₜ : State)
    (hl : lts.Tr s l sₗ)
    (ht : lts.MTr sₗ t sₗₜ)
    (hind : ∀ a ∈ t, I a l)
  : ∃ sₜ, lts.MTr s t sₜ
  := by
    -- structural induction on the trace, generalising the states
    induction t generalizing s sₗ sₗₜ with
    | nil => exact ⟨s, .refl⟩
    | cons a t' ih =>
      obtain ⟨s₁, ha, ht'⟩ := LTS.MTr.cons_iff.mp ht
      have ha_ind : I a l := hind a List.mem_cons_self
      have hl_ind : I l a := Std.Symm.symm (r := I) (a := a) (b := l) ha_ind
      -- backward concurrency: `a` is already enabled before `l`
      obtain ⟨s₂, htra⟩ := h.r s s₁ l a ⟨hl_ind, .stepL hl (.stepL ha .refl)⟩
      -- the forward diamond and determinism identify the two targets of `a`
      obtain ⟨s₃, hl₃, ha₃⟩ := h.f s s₂ sₗ a l ⟨ha_ind, htra, hl⟩
      rw [h.d sₗ s₃ s₁ a ha₃ ha] at hl₃
      -- the tail runs after `a` from `s₂`, by the induction hypothesis
      obtain ⟨sₜ, htail⟩ := ih s₂ s₁ sₗₜ hl₃ ht' fun m hm => hind m (List.mem_cons_of_mem a hm)
      exact ⟨sₜ, .stepL htra htail⟩

-- backwards concurrency extended to label and trace
-- l commutes past its prefix t
private lemma backward_concurrency_label_trace
    {lts : LTS State Label}
    {I : Label → Label → Prop}
    [Independence I]
    {B : Branching Label}
    (h : Smurf lts I B)
    (l : Label)
    (t : List Label)
    (s sₜ sₜₗ : State)
    (ht : lts.MTr s t sₜ)
    (hl : lts.Tr sₜ l sₜₗ)
    (hind : ∀ a ∈ t, I a l)
  : ∃ sₗ, lts.Tr s l sₗ
  := by
    induction t generalizing s sₜ sₜₗ with
    | nil => exact ⟨sₜₗ, by rwa [LTS.MTr.nil_eq lts ht]⟩
    | cons a t' ih =>
      obtain ⟨s₁, ha, ht'⟩ := LTS.MTr.cons_iff.mp ht
      have ha_ind : I a l := hind a List.mem_cons_self
      obtain ⟨sₗ, hl'⟩ := ih s₁ sₜ sₜₗ ht' hl fun m hm => hind m (List.mem_cons_of_mem a hm)
      exact h.r s sₗ a l ⟨ha_ind, .stepL ha (.stepL hl' .refl)⟩

-- backward concurrency extended to trace and trace
-- t₁ commutes past its prefix t₂
private lemma backward_concurrency_trace_trace
    {lts : LTS State Label}
    {I : Label → Label → Prop}
    [Independence I]
    {B : Branching Label}
    (h : Smurf lts I B)
    (t₁ t₂ : List Label)
    (s s₂ s₂₁ : State)
    (ht₂ : lts.MTr s t₂ s₂)
    (ht₁ : lts.MTr s₂ t₁ s₂₁)
    (hind : ∀ a ∈ t₁, ∀ b ∈ t₂, I a b)
  : ∃ s₁, lts.MTr s t₁ s₁
  := by
    induction t₂ generalizing s s₂ with
    | nil => exact ⟨s₂₁, by rwa [LTS.MTr.nil_eq lts ht₂]⟩
    | cons b t₂' ih =>
      obtain ⟨s_b, hb, ht₂'⟩ := LTS.MTr.cons_iff.mp ht₂
      have hind_b : ∀ a ∈ t₁, I a b := fun a ha => hind a ha b List.mem_cons_self
      obtain ⟨s₁, ht₁'⟩ := ih s_b s₂ ht₂' ht₁ fun a ha c hc =>
        hind a ha c (List.mem_cons_of_mem b hc)
      exact backward_concurrency_trace_label h t₁ b s s_b s₁ hb ht₁' hind_b

-- diamond extended to trace and label
-- t commutes past l
private lemma diamond_trace_label
    {lts : LTS State Label}
    {I : Label → Label → Prop}
    [Independence I]
    {B : Branching Label}
    (h : Smurf lts I B)
    (t : List Label)
    (l : Label)
    (s sₜ sₗ : State)
    (ht : lts.MTr s t sₜ)
    (hl : lts.Tr s l sₗ)
    (hind : ∀ a ∈ t, I a l)
  : ∃ sₜₗ, lts.Tr sₜ l sₜₗ
  := by
    induction t generalizing s sₜ sₗ with
    | nil => exact ⟨sₗ, by rwa [← LTS.MTr.nil_eq lts ht]⟩
    | cons a t' ih =>
      obtain ⟨s₁, ha, ht'⟩ := LTS.MTr.cons_iff.mp ht
      have ha_ind : I a l := hind a List.mem_cons_self
      obtain ⟨s₃, hl₁, _⟩ := h.f s s₁ sₗ a l ⟨ha_ind, ha, hl⟩
      exact ih s₁ sₜ s₃ ht' hl₁ fun m hm => hind m (List.mem_cons_of_mem a hm)

-- diamond extended to label and trace
-- l commutes past t
private lemma diamond_label_trace
    {lts : LTS State Label}
    {I : Label → Label → Prop}
    [Independence I]
    {B : Branching Label}
    (h : Smurf lts I B)
    (l : Label)
    (t : List Label)
    (s sₗ sₜ : State)
    (hl : lts.Tr s l sₗ)
    (ht : lts.MTr s t sₜ)
    (hind : ∀ a ∈ t, I a l)
  : ∃ sₗₜ, lts.MTr sₗ t sₗₜ
  := by
    induction t generalizing s sₗ sₜ with
    | nil => exact ⟨sₗ, .refl⟩
    | cons a t' ih =>
      obtain ⟨s₁, ha, ht'⟩ := LTS.MTr.cons_iff.mp ht
      have ha_ind : I a l := hind a List.mem_cons_self
      obtain ⟨s₂, hl₁, ha₂⟩ := h.f s s₁ sₗ a l ⟨ha_ind, ha, hl⟩
      obtain ⟨sₗₜ, htail⟩ := ih s₁ s₂ sₜ hl₁ ht' fun m hm => hind m (List.mem_cons_of_mem a hm)
      exact ⟨sₗₜ, .stepL ha₂ htail⟩

-- diamond extended to trace and trace
-- t₁ commutes past t₂
private lemma diamond_trace_trace
    {lts : LTS State Label}
    {I : Label → Label → Prop}
    [Independence I]
    {B : Branching Label}
    (h : Smurf lts I B)
    (t₁ t₂ : List Label)
    (s s₁ s₂ : State)
    (ht₁ : lts.MTr s t₁ s₁)
    (ht₂ : lts.MTr s t₂ s₂)
    (hind : ∀ a ∈ t₁, ∀ b ∈ t₂, I a b)
  : ∃ s₂₁, lts.MTr s₂ t₁ s₂₁
  := by
    induction t₂ generalizing s s₁ s₂ with
    | nil => exact ⟨s₁, by rwa [← LTS.MTr.nil_eq lts ht₂]⟩
    | cons b t₂' ih =>
      obtain ⟨s_b, hb, ht₂'⟩ := LTS.MTr.cons_iff.mp ht₂
      have hind_b : ∀ a ∈ t₁, I a b := fun a ha => hind a ha b List.mem_cons_self
      obtain ⟨s_b', ht₁'⟩ := diamond_label_trace h b t₁ s s_b s₁ hb ht₁ hind_b
      exact ih s_b s_b' s₂ ht₁' ht₂' fun a ha c hc => hind a ha c (List.mem_cons_of_mem b hc)

-- two lists whose elements are pairwise independent can be swapped
private lemma permUpTo_append_comm {I : Label → Label → Prop} [Independence I] :
    ∀ u v : List Label,
      (∀ a ∈ u, ∀ b ∈ v, I a b) → List.PermUpTo I (u ++ v) (v ++ u) := by
  intro u
  induction u with
  | nil => intro v _; simpa using List.PermUpTo.refl v
  | cons a u ih =>
    intro v h
    have hmove : ∀ v' : List Label, (∀ b ∈ v', I a b) →
        List.PermUpTo I (a :: (v' ++ u)) (v' ++ (a :: u)) := by
      intro v'
      induction v' with
      | nil => intro _; simpa using List.PermUpTo.refl (a :: u)
      | cons b v' ihv =>
        intro hb
        exact (List.PermUpTo.swap a b (v' ++ u) (Or.inl (hb b List.mem_cons_self))).trans
          (List.PermUpTo.cons b (ihv fun c hc => hb c (List.mem_cons_of_mem b hc)))
    exact (List.PermUpTo.cons a
      (ih v fun x hx y hy => h x (List.mem_cons_of_mem a hx) y hy)).trans
      (hmove v fun b hb => h a List.mem_cons_self b hb)

/-- If a prefix of an execution `Y` ends in a label `b` that does not commute with `lX`,
where `lX` is enabled after an execution `X` independent of `Y`, then `lX` and `b`
match or are equal. -/
private lemma counterexample_match
    {lts : LTS State Label}
    {I : Label → Label → Prop}
    [Independence I]
    {B : Branching Label}
    (h : Smurf lts I B)
    {X Y : List Label}
    {s xEnd xEnd' yEnd : State}
    {lX b : Label}
    {u v : List Label}
    (htX : lts.MTr s X xEnd)
    (hX : lts.Tr xEnd lX xEnd')
    (htY : lts.MTr s Y yEnd)
    (hind : ∀ w ∈ X, ∀ z ∈ Y, I w z)
    (hY : Y = u ++ [b] ++ v)
    (hu : ∀ z ∈ u, I lX z)
    (hb : ¬ I lX b)
  : B.matching lX b ∨ lX = b
  := by
    obtain ⟨sᵤ, hub, _⟩ := LTS.MTr.split (by rwa [← hY] : lts.MTr s ((u ++ [b]) ++ v) yEnd)
    have hind' : ∀ x ∈ u ++ [b], ∀ w ∈ X, I x w := fun x hx w hw =>
      Std.Symm.symm (r := I) (a := w) (b := x)
        (hind w hw x (by rw [hY]; exact List.mem_append_left v hx))
    have hu' : ∀ z ∈ u, I z lX := fun z hz =>
      Std.Symm.symm (r := I) (a := lX) (b := z) (hu z hz)
    obtain ⟨s₅, hsub⟩ := diamond_trace_trace h (u ++ [b]) X s sᵤ xEnd hub htX hind'
    obtain ⟨s₃, h₃, h₄⟩ := mtr_split_last (l := u) (a := b) hsub
    obtain ⟨s₄, h₅⟩ := diamond_trace_label h u lX xEnd s₃ xEnd' h₃ hX hu'
    by_cases heq : lX = b
    · exact Or.inr heq
    · exact Or.inl ((h.u s₃ s₄ s₅ lX b heq ⟨h₅, h₄⟩).resolve_left hb)

-- two traces from the same state will either fully commute, or result in a match or an equality
omit [DecidableEq Pid] in
private lemma commute_or_matcheq
    {lts : LTS State Label}
    {I : Label → Label → Prop}
    [Independence I]
    {B : Branching Label}
    (h : Smurf lts I B)
    -- plus a concrete state and two traces
    (s s₁ s₂ : State)
    (t₁ t₂ : List Label)
    (ht₁ : lts.MTr s t₁ s₁) (ht₂ : lts.MTr s t₂ s₂)
  :
  (∀ a ∈ t₁, ∀ b ∈ t₂, I a b)
  ∨ ∃ (u₁ u₂ : List Label) (a b : Label) (v₁ v₂ : List Label),
      t₁ = u₁ ++ a :: v₁
    ∧ t₂ = u₂ ++ b :: v₂
    ∧ (B.matching a b ∨ a = b)
    ∧ (∀ x ∈ u₁, ∀ y ∈ u₂, I x y)
    ∧ (∀ y ∈ u₂, I a y)
    ∧ (∀ x ∈ u₁, I x b)
  := by
    -- by induction on t₁.length + t₂.length
    induction hn : t₁.length + t₂.length using Nat.strong_induction_on generalizing
        s t₁ t₂ s₁ s₂ with
    | _ n ih =>
      -- an empty trace commutes with everything: all cross pairs are independent
      rcases List.eq_nil_or_concat t₁ with rfl | ⟨t₁', a₀, rfl⟩
      · exact Or.inl (by simp)
      rcases List.eq_nil_or_concat t₂ with rfl | ⟨t₂', b₀, rfl⟩
      · exact Or.inl (by simp)
      simp only [List.concat_eq_append] at ht₁ ht₂ hn ⊢
      -- split both traces at their last step
      -- t₁ = t₁' :: a₀, t₂ = t₂' :: b₀
      obtain ⟨s₁', ht₁', ha₀⟩ := mtr_split_last (l := t₁') (a := a₀) ht₁
      obtain ⟨s₂', ht₂', hb₀⟩ := mtr_split_last (l := t₂') (a := b₀) ht₂
      -- apply induction hypothesis to t₁' and t₂'
      rcases ih (t₁'.length + t₂'.length) (by grind) s s₁' s₂' t₁' t₂' ht₁' ht₂' rfl
        with hind | hmatch
      · -- t₁' and t₂' commute
        by_cases ha₀c : ∃ u b₁ v, t₂' = u ++ [b₁] ++ v ∧ (∀ b ∈ u, I a₀ b) ∧ ¬ I a₀ b₁
        · -- a₀ does not commute with t₂': the counterexample provides a witness
          obtain ⟨u, b₁, v, hubv, ha₀u, ha₀b₁⟩ := ha₀c
          have hm : B.matching a₀ b₁ ∨ a₀ = b₁ :=
            counterexample_match h ht₁' ha₀ ht₂' hind hubv ha₀u ha₀b₁
          refine Or.inr ⟨t₁', u, a₀, b₁, [], v ++ [b₀], ?_, ?_, hm, ?_, ?_, ?_⟩
          all_goals grind
        -- otherwise a₀ commutes with t₂'
        -- absence of a counterexample prefix means commutation with every label
        have key : ∀ (x : Label) (L : List Label),
            (¬ ∃ u b v, L = u ++ [b] ++ v ∧ (∀ a ∈ u, I x a) ∧ ¬ I x b) →
            ∀ a ∈ L, I x a := by
          intro x L
          induction L with
          | nil => simp
          | cons d L ih =>
            intro hno
            by_cases hd : I x d
            · intro c hc
              rcases List.mem_cons.mp hc with rfl | hc
              · exact hd
              · exact ih (fun ⟨u, b, v, hL, hu, hb⟩ =>
                  hno ⟨d :: u, b, v, by simp [hL],
                    fun y hy => by
                      rcases List.mem_cons.mp hy with rfl | hy
                      · exact hd
                      · exact hu y hy, hb⟩) c hc
            · exact absurd ⟨[], d, L, rfl, by simp, hd⟩ hno
        have ha₀t₂' : ∀ c ∈ t₂', I a₀ c := key a₀ t₂' ha₀c
        have hind : ∀ a ∈ t₂', ∀ b ∈ (t₁' ++ [a₀]), I a b := by
          intro a ha b hb
          rcases List.mem_append.mp hb with hb | hb
          · exact Std.Symm.symm (r := I) (a := b) (b := a) (hind b hb a ha)
          · rw [List.mem_singleton] at hb
            rw [hb]
            exact Std.Symm.symm (r := I) (a := a₀) (b := a) (ha₀t₂' a ha)
        -- check whether there exists a counterexample for b₀ commuting with t₁' ++ [a₀]
        by_cases hb₀c : ∃ u a₁ v, t₁' = u ++ [a₁] ++ v ∧ (∀ a ∈ u, I b₀ a) ∧ ¬ I b₀ a₁
        · -- b₀ does not commute with t₁': the counterexample provides a witness
          obtain ⟨u, a₁, v, huv, hb₀u, hb₀a₁⟩ := hb₀c
          have hm : B.matching a₁ b₀ ∨ a₁ = b₀ :=
            (counterexample_match h ht₂' hb₀ ht₁'
              (fun w hw z hz => hind w hw z (List.mem_append_left [a₀] hz)) huv hb₀u hb₀a₁).elim
              (fun h => Or.inl (matching_comm h)) fun h => Or.inr h.symm
          have hb₀u' : ∀ y ∈ u, I y b₀ := fun y hy =>
            Std.Symm.symm (r := I) (a := b₀) (b := y) (hb₀u y hy)
          refine Or.inr ⟨u, t₂', a₁, b₀, v ++ [a₀], [], ?_, ?_, hm, ?_, ?_, ?_⟩
          all_goals grind
        -- otherwise b₀ commutes with every label of t₁'; co-enable a₀ and b₀
        have hb₀t₁' : ∀ c ∈ t₁', I b₀ c := key b₀ t₁' hb₀c
        have hind₂ : ∀ a ∈ t₁', ∀ b ∈ t₂', I a b := fun a ha b hb =>
          Std.Symm.symm (r := I) (a := b) (b := a) (hind b hb a (List.mem_append_left [a₀] ha))
        obtain ⟨ρ, hcomm₂⟩ := diamond_trace_trace h t₂' t₁' s s₂' s₁' ht₂' ht₁'
          fun a ha b hb => hind a ha b (List.mem_append_left [a₀] hb)
        obtain ⟨ρ', hcomm₁⟩ := diamond_trace_trace h t₁' t₂' s s₁' s₂' ht₁' ht₂' hind₂
        have hρ : ρ = ρ' := mtr_det_permUpTo h (permUpTo_append_comm t₁' t₂' hind₂)
          (LTS.MTr.comp lts ht₁' hcomm₂) (LTS.MTr.comp lts ht₂' hcomm₁)
        obtain ⟨sa, hρa₀⟩ := diamond_trace_label h t₂' a₀ s₁' ρ s₁ hcomm₂ ha₀
          fun a ha => Std.Symm.symm (r := I) (a := a₀) (b := a) (ha₀t₂' a ha)
        obtain ⟨sb, hρ'b₀⟩ := diamond_trace_label h t₁' b₀ s₂' ρ' s₂ hcomm₁ hb₀
          fun a ha => Std.Symm.symm (r := I) (a := b₀) (b := a) (hb₀t₁' a ha)
        have hindW : ∀ x ∈ t₁', ∀ y ∈ t₂', I x y := fun x hx y hy =>
          Std.Symm.symm (r := I) (a := y) (b := x) (hind y hy x (List.mem_append_left [a₀] hx))
        have hb₀W : ∀ x ∈ t₁', I x b₀ := fun x hx =>
          Std.Symm.symm (r := I) (a := b₀) (b := x) (hb₀t₁' x hx)
        by_cases heq : a₀ = b₀
        · exact Or.inr ⟨t₁', t₂', a₀, b₀, [], [], rfl, rfl, Or.inr heq, hindW, ha₀t₂', hb₀W⟩
        · rcases h.u ρ sa sb a₀ b₀ heq ⟨hρa₀, hρ.symm ▸ hρ'b₀⟩ with hI | hm
          · apply Or.inl
            intro a ha b hb
            simp only [List.mem_append, List.mem_singleton] at ha hb
            rcases ha with ha | rfl <;> rcases hb with hb | rfl
            exacts [hindW a ha b hb, hb₀W a ha, ha₀t₂' b hb, hI]
          · exact Or.inr ⟨t₁', t₂', a₀, b₀, [], [], rfl, rfl, Or.inl hm, hindW, ha₀t₂', hb₀W⟩
      · -- a witness for t₁', t₂' also works for t₁, t₂
        obtain ⟨u₁, u₂, a, b, v₁, v₂, h1, h2, hw, hc, hl, hr⟩ := hmatch
        exact Or.inr ⟨u₁, u₂, a, b, v₁ ++ [a₀], v₂ ++ [b₀], by grind, by grind, hw, hc, hl, hr⟩

/-- Two lists are either prefix-comparable, or have a longest common prefix followed by
distinct labels. -/
private lemma prefix_or_exists_first_diff :
    ∀ u v : List Label,
      u <+: v ∨ v <+: u ∨
        ∃ t₀ u' v' x₁ x₂, u = t₀ ++ [x₁] ++ u' ∧ v = t₀ ++ [x₂] ++ v' ∧ x₁ ≠ x₂ := by
  intro u
  induction u with
  | nil => intro v; exact Or.inl List.nil_prefix
  | cons a u ih =>
    intro v
    cases v with
    | nil => exact Or.inr (Or.inl List.nil_prefix)
    | cons b v =>
      by_cases hab : a = b
      · subst b
        rcases ih v with h | h | ⟨t₀, u', v', x₁, x₂, hu, hv, hne⟩
        · exact Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
        · exact Or.inr (Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h⟩))
        · exact Or.inr (Or.inr ⟨a :: t₀, u', v', x₁, x₂, by simp [hu], by simp [hv], hne⟩)
      · exact Or.inr (Or.inr ⟨[], u, v, a, b, rfl, rfl, hab⟩)

-- PermUpTo preserves equivalence of projections
private lemma permupto_equiv_proj
    {pn : Label → Finset Pid}
    (I : Label → Label → Prop)
    [Independence I]
    (hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂))
  :
    ∀ (t₁ t₂ : List Label) (p : Pid),
    List.PermUpTo I t₁ t₂ → ProjectTrace (pn := pn) t₁ p = ProjectTrace (pn := pn) t₂ p
  := by
    intro t₁ t₂ p hp
    -- independence ensures that `p` observes at most one label of an independent pair,
    -- so swapping such a pair does not change the projection
    induction hp with
    | nil => rfl
    | cons a _ ih =>
      simp only [ProjectTrace, List.filter_cons] at ih ⊢
      rw [ih]
    | swap a b w hI =>
      have hind : I a b := hI.elim id fun h => Std.Symm.symm (r := I) (a := b) (b := a) h
      simp only [ProjectTrace, List.filter_cons]
      by_cases ha : p ∈ pn a
      · have hb : p ∉ pn b := fun hb => Finset.disjoint_left.mp (hpn₁ a b hind) ha hb
        simp [ha, hb]
      · by_cases hb : p ∈ pn b
        · simp [ha, hb]
        · simp [ha, hb]
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

-- helper lemma for the prefix case, using PermUpTo to shift equal labels to the front
private lemma prefix_or_match_permupto
    {pn : Label → Finset Pid}
    {lts : LTS State Label}
    {I : Label → Label → Prop}
    [Independence I]
    {B : Branching Label}
    (hpn₀ : ∀ l, (pn l).Nonempty)
    (hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂))
    (hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → (pn l₁) = (pn l₂))
    (h : Smurf lts I B)
  : ∀ (s s₁ s₂ : State) (t₁ t₂ : List Label) (p : Pid),
  (lts.MTr s t₁ s₁ ∧ lts.MTr s t₂ s₂) →
  (
    ProjectTrace (pn := pn) t₁ p <+: ProjectTrace (pn := pn) t₂ p
    ∨
    ProjectTrace (pn := pn) t₂ p <+: ProjectTrace (pn := pn) t₁ p
    ∨
    (
      ∃ (q : Pid) (u₁ u₂ t₁' t₂' v₁ v₂ : List Label) (x₁ x₂ : Label),
      q ∈ pn x₁
      ∧ List.PermUpTo I t₁' u₁ ∧ t₁' ++ [x₁] ++ v₁ = t₁
      ∧ List.PermUpTo I t₂' u₂ ∧ t₂' ++ [x₂] ++ v₂ = t₂
      ∧ ProjectTrace (pn := pn) u₁ q = ProjectTrace (pn := pn) u₂ q
      ∧ B.matching x₁ x₂
    )
  )
  := by
    intro s s₁ s₂ t₁ t₂ p
    -- induction on combined length of t₁ and t₂
    induction hn : t₁.length + t₂.length using Nat.strong_induction_on generalizing
        s s₁ s₂ t₁ t₂ p with
    | _ n ih =>
      intro hm
      -- base case: both traces are empty, so both projections are empty
      rcases n with _ | n
      · obtain rfl : t₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
        obtain rfl : t₂ = [] := List.eq_nil_of_length_eq_zero (by omega)
        exact Or.inl (by simp [ProjectTrace])
      -- induction case
      -- apply commute_or_matcheq: either t₁ and t₂ commute, or they hit a match or equivalence
      rcases commute_or_matcheq h s s₁ s₂ t₁ t₂ hm.left hm.right with
        hcom | ⟨u₁, u₂, x₁, x₂, v₁, v₂, ht₁, ht₂, hmeq, hind₁, hind₂, hind₃⟩
      -- if the two commute, then one of the two projections will be a prefix of the other
      · -- one of the two projections must be empty
        by_cases h₁ : ProjectTrace (pn := pn) t₁ p = []
        · rw [h₁]
          exact Or.inl List.nil_prefix
        · refine Or.inr (Or.inl ?_)
          -- some label of `t₁` is observed by `p`
          obtain ⟨a, ha, hap⟩ : ∃ a ∈ t₁, p ∈ pn a := by
            by_contra hcon
            exact h₁ (projectTrace_eq_nil fun l hl hpl => hcon ⟨l, hl, hpl⟩)
          -- full commutation makes every label of `t₂` unobserved by `p`
          have h₂ : ProjectTrace (pn := pn) t₂ p = [] :=
            projectTrace_eq_nil fun b hb hpb =>
              Finset.disjoint_left.mp (hpn₁ a b (hcom a ha b hb)) hap hpb
          rw [h₂]
          exact List.nil_prefix
      -- otherwise, distinguish between match and equality
      rcases hmeq with hmatch | heq
      -- if match, then this provides a witness: a process observing the
      -- matching labels observes neither prefix
      · obtain ⟨q, hq⟩ := hpn₀ x₁
        have hqx₂ : q ∈ pn x₂ := (hpn₂ x₁ x₂ hmatch) ▸ hq
        have hu₁nil : ProjectTrace (pn := pn) u₁ q = [] :=
          projectTrace_eq_nil fun x hx hqx =>
            Finset.disjoint_left.mp (hpn₁ x x₂ (hind₃ x hx)) hqx hqx₂
        have hu₂nil : ProjectTrace (pn := pn) u₂ q = [] :=
          projectTrace_eq_nil fun y hy hqy =>
            Finset.disjoint_left.mp (hpn₁ x₁ y (hind₂ y hy)) hq hqy
        apply Or.inr
        apply Or.inr
        refine ⟨q, u₁, u₂, u₁, u₂, v₁, v₂, x₁, x₂, hq, ?_, ?_, ?_, ?_, ?_, hmatch⟩
        · exact List.PermUpTo.refl _
        · rw [ht₁]
          simp only [List.append_assoc, List.cons_append, List.nil_append]
        · exact List.PermUpTo.refl _
        · rw [ht₂]
          simp only [List.append_assoc, List.cons_append, List.nil_append]
        · rw [hu₁nil, hu₂nil]
      -- if eq, then commute u₁ ++ [x₁] ++ v₁ to [x₁] ++ u₁ ++ v₁ (and similarly for ₂)
      -- in the equality case both prefixes are independent of the shared label
      have hp₁ : List.PermUpTo I t₁ (x₁ :: (u₁ ++ v₁)) := by
        rw [ht₁]
        have hswap : List.PermUpTo I (u₁ ++ [x₁]) ([x₁] ++ u₁) :=
          permUpTo_append_comm u₁ [x₁] fun a ha b hb => by
            rw [List.mem_singleton] at hb
            subst hb
            rw [heq]
            exact hind₃ a ha
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using
          List.PermUpTo.append_right v₁ (u₁ ++ [x₁]) ([x₁] ++ u₁) hswap
      have hp₂ : List.PermUpTo I t₂ (x₁ :: (u₂ ++ v₂)) := by
        rw [ht₂, ← heq]
        have hswap : List.PermUpTo I (u₂ ++ [x₁]) ([x₁] ++ u₂) :=
          permUpTo_append_comm u₂ [x₁] fun a ha b hb => by
            rw [List.mem_singleton] at hb
            subst hb
            exact Std.Symm.symm (r := I) (a := b) (b := a) (hind₂ a ha)
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using
          List.PermUpTo.append_right v₂ (u₂ ++ [x₁]) ([x₁] ++ u₂) hswap
      -- so both projections are the projection of the tails, preceded by the shared label
      have hproj₁ : ProjectTrace (pn := pn) t₁ p
          = (if p ∈ pn x₁ then [x₁] else [])
            ++ ProjectTrace (pn := pn) (u₁ ++ v₁) p := by
        rw [permupto_equiv_proj I hpn₁ t₁ (x₁ :: (u₁ ++ v₁)) p hp₁]
        by_cases hxp : p ∈ pn x₁ <;> simp [ProjectTrace, hxp]
      have hproj₂ : ProjectTrace (pn := pn) t₂ p
          = (if p ∈ pn x₁ then [x₁] else [])
            ++ ProjectTrace (pn := pn) (u₂ ++ v₂) p := by
        rw [permupto_equiv_proj I hpn₁ t₂ (x₁ :: (u₂ ++ v₂)) p hp₂]
        by_cases hxp : p ∈ pn x₁ <;> simp [ProjectTrace, hxp]
      -- move the shared label to the front of both traces
      have ⟨sₓ, hx, hx₁, hx₂⟩ : ∃ sₓ, lts.Tr s x₁ sₓ
          ∧ lts.MTr sₓ (u₁ ++ v₁) s₁ ∧ lts.MTr sₓ (u₂ ++ v₂) s₂ := by
        obtain ⟨sₓ, hx, hx₁⟩ := LTS.MTr.cons_iff.mp (mtr_permUpTo h hp₁ hm.left)
        obtain ⟨sₓ', hx', hx₂⟩ := LTS.MTr.cons_iff.mp (mtr_permUpTo h hp₂ hm.right)
        rw [← h.d s sₓ sₓ' x₁ hx hx'] at hx₂
        exact ⟨sₓ, hx, hx₁, hx₂⟩
      -- apply induction hypothesis to now shorter tails u₁ ++ v₁, u₂ ++ v₂
      have hlen : (u₁ ++ v₁).length + (u₂ ++ v₂).length < n + 1 := by
        have h₁ : t₁.length = u₁.length + (v₁.length + 1) := by
          rw [ht₁]
          simp
        have h₂ : t₂.length = u₂.length + (v₂.length + 1) := by
          rw [ht₂]
          simp
        rw [List.length_append, List.length_append]
        omega
      rcases ih ((u₁ ++ v₁).length + (u₂ ++ v₂).length) hlen sₓ s₁ s₂
          (u₁ ++ v₁) (u₂ ++ v₂) p rfl ⟨hx₁, hx₂⟩ with
        hpre | hpre | ⟨q, u₁', u₂', t₁', t₂', v₁', v₂', x₁', x₂', hq',
                       hperm₁, hEq₁, hperm₂, hEq₂, hproj, hmat⟩
      · -- the tail projections are prefix-comparable: prepend `x₁` on both sides
        left
        rw [hproj₁, hproj₂]
        obtain ⟨c, hc⟩ := hpre
        exact ⟨c, by rw [List.append_assoc, hc]⟩
      · -- symmetric to the previous case
        right
        left
        rw [hproj₂, hproj₁]
        obtain ⟨c, hc⟩ := hpre
        exact ⟨c, by rw [List.append_assoc, hc]⟩
      · -- a recursive witness for the tails: rebuild one for the full traces
        -- both `tᵢ' ++ [xᵢ']` and `uᵢ` are prefixes of `uᵢ ++ vᵢ`, so each recursive
        -- decomposition splits at the boundary between `uᵢ` and `vᵢ`
        have hL₁ : t₁' <+: t₁' ++ [x₁'] ++ v₁' :=
          (List.prefix_append t₁' [x₁']).trans (List.prefix_append (t₁' ++ [x₁']) v₁')
        have hA₁ : t₁' ++ [x₁'] <+: t₁' ++ [x₁'] ++ v₁' := List.prefix_append _ _
        have hU₁ : u₁ <+: t₁' ++ [x₁'] ++ v₁' := by
          rw [hEq₁]; exact List.prefix_append _ _
        have hL₂ : t₂' <+: t₂' ++ [x₂'] ++ v₂' :=
          (List.prefix_append t₂' [x₂']).trans (List.prefix_append (t₂' ++ [x₂']) v₂')
        have hA₂ : t₂' ++ [x₂'] <+: t₂' ++ [x₂'] ++ v₂' := List.prefix_append _ _
        have hU₂ : u₂ <+: t₂' ++ [x₂'] ++ v₂' := by
          rw [hEq₂]; exact List.prefix_append _ _
        -- the shared label is independent of both prefixes
        have hswap₁ : List.PermUpTo I (u₁ ++ [x₁]) ([x₁] ++ u₁) :=
          permUpTo_append_comm u₁ [x₁] fun a ha b hb => by
            rw [List.mem_singleton] at hb
            subst hb
            rw [heq]
            exact hind₃ a ha
        have hswap₂ : List.PermUpTo I (u₂ ++ [x₂]) ([x₂] ++ u₂) :=
          permUpTo_append_comm u₂ [x₂] fun a ha b hb => by
            rw [List.mem_singleton] at hb
            subst hb
            rw [← heq]
            exact Std.Symm.symm (r := I) (a := x₁) (b := a) (hind₂ a ha)
        -- projections of a cons
        have hcons : ∀ (a : Label) (L : List Label),
            ProjectTrace (pn := pn) (a :: L) q
              = (if q ∈ pn a then [a] else []) ++ ProjectTrace (pn := pn) L q := by
          intro a L
          by_cases h : q ∈ pn a <;> simp [ProjectTrace, h]
        have hcons_nil : ∀ (a : Label) (L : List Label), q ∉ pn a →
            ProjectTrace (pn := pn) (a :: L) q = ProjectTrace (pn := pn) L q := by
          intro a L ha
          simp [ProjectTrace, ha]
        by_cases hl₁ : (t₁' ++ [x₁']).length ≤ u₁.length
        · -- case A on side 1: the recursive matching label lies in `u₁`
          obtain ⟨w₁, hw₁⟩ := List.prefix_of_prefix_length_le hA₁ hU₁ hl₁
          have hEqA₁ : t₁' ++ [x₁'] ++ (w₁ ++ [x₁] ++ v₁) = t₁ := by
            rw [ht₁, ← hw₁]
            simp only [List.append_assoc, List.cons_append, List.nil_append]
          have hmem₁ : x₁' ∈ u₁ := by
            rw [← hw₁]
            exact List.mem_append_left w₁
              (List.mem_append_right t₁' (List.mem_singleton_self x₁'))
          by_cases hl₂ : (t₂' ++ [x₂']).length ≤ u₂.length
          · -- A/A
            obtain ⟨w₂, hw₂⟩ := List.prefix_of_prefix_length_le hA₂ hU₂ hl₂
            have hEqA₂ : t₂' ++ [x₂'] ++ (w₂ ++ [x₂] ++ v₂) = t₂ := by
              rw [ht₂, ← hw₂]
              simp only [List.append_assoc, List.cons_append, List.nil_append]
            exact Or.inr (Or.inr ⟨q, u₁', u₂', t₁', t₂',
              w₁ ++ [x₁] ++ v₁, w₂ ++ [x₂] ++ v₂, x₁', x₂',
              hq', hperm₁, hEqA₁, hperm₂, hEqA₂, hproj, hmat⟩)
          · -- A/B
            have hB₂ : u₂ <+: t₂' := by
              apply List.prefix_of_prefix_length_le hU₂ hL₂
              simp only [List.length_append, List.length_singleton] at hl₂ ⊢
              omega
            obtain ⟨w₂, hw₂⟩ := hB₂
            have hv₂ : v₂ = w₂ ++ ([x₂'] ++ v₂') := by
              have h := hEq₂
              rw [← hw₂] at h
              simp only [List.append_assoc] at h
              exact (List.append_cancel_left h).symm
            have hpermB₂ : List.PermUpTo I (u₂ ++ [x₂] ++ w₂) (x₂ :: u₂') := by
              have hrec : List.PermUpTo I (u₂ ++ w₂) u₂' := by
                rw [hw₂]
                exact hperm₂
              exact (List.PermUpTo.append_right w₂ (u₂ ++ [x₂]) ([x₂] ++ u₂) hswap₂).trans
                (List.PermUpTo.cons x₂ hrec)
            have hEqB₂ : (u₂ ++ [x₂] ++ w₂) ++ [x₂'] ++ v₂' = t₂ := by
              rw [ht₂, hv₂]
              simp only [List.append_assoc, List.cons_append, List.nil_append]
            have hdisj : Disjoint (pn x₁') (pn x₂) := hpn₁ x₁' x₂ (hind₃ x₁' hmem₁)
            have hqx₂ : q ∉ pn x₂ :=
              fun hmem => Finset.disjoint_left.mp hdisj hq' hmem
            refine Or.inr (Or.inr ⟨q, u₁', x₂ :: u₂', t₁', u₂ ++ [x₂] ++ w₂,
              w₁ ++ [x₁] ++ v₁, v₂', x₁', x₂',
              hq', hperm₁, hEqA₁, hpermB₂, hEqB₂, ?_, hmat⟩)
            simp only [hcons x₂ u₂', ite_eq_right hqx₂, List.nil_append, hproj]
        · -- case B on side 1: the recursive matching label lies in `v₁`
          have hB₁ : u₁ <+: t₁' := by
            apply List.prefix_of_prefix_length_le hU₁ hL₁
            simp only [List.length_append, List.length_singleton] at hl₁ ⊢
            omega
          obtain ⟨w₁, hw₁⟩ := hB₁
          have hv₁ : v₁ = w₁ ++ ([x₁'] ++ v₁') := by
            have h := hEq₁
            rw [← hw₁] at h
            simp only [List.append_assoc] at h
            exact (List.append_cancel_left h).symm
          have hpermB₁ : List.PermUpTo I (u₁ ++ [x₁] ++ w₁) (x₁ :: u₁') := by
            have hrec : List.PermUpTo I (u₁ ++ w₁) u₁' := by
              rw [hw₁]
              exact hperm₁
            exact (List.PermUpTo.append_right w₁ (u₁ ++ [x₁]) ([x₁] ++ u₁) hswap₁).trans
              (List.PermUpTo.cons x₁ hrec)
          have hEqB₁ : (u₁ ++ [x₁] ++ w₁) ++ [x₁'] ++ v₁' = t₁ := by
            rw [ht₁, hv₁]
            simp only [List.append_assoc, List.cons_append, List.nil_append]
          by_cases hl₂ : (t₂' ++ [x₂']).length ≤ u₂.length
          · -- B/A
            obtain ⟨w₂, hw₂⟩ := List.prefix_of_prefix_length_le hA₂ hU₂ hl₂
            have hEqA₂ : t₂' ++ [x₂'] ++ (w₂ ++ [x₂] ++ v₂) = t₂ := by
              rw [ht₂, ← hw₂]
              simp only [List.append_assoc, List.cons_append, List.nil_append]
            have hmem₂ : x₂' ∈ u₂ := by
              rw [← hw₂]
              exact List.mem_append_left w₂
                (List.mem_append_right t₂' (List.mem_singleton_self x₂'))
            have hdisj : Disjoint (pn x₂) (pn x₂') :=
              hpn₁ x₂ x₂' (heq ▸ hind₂ x₂' hmem₂)
            have hq₂' : q ∈ pn x₂' := (hpn₂ x₁' x₂' hmat) ▸ hq'
            have hqx₂ : q ∉ pn x₂ :=
              fun hmem => Finset.disjoint_left.mp hdisj hmem hq₂'
            have hqx₁ : q ∉ pn x₁ := by
              rw [heq]
              exact hqx₂
            refine Or.inr (Or.inr ⟨q, x₁ :: u₁', u₂', u₁ ++ [x₁] ++ w₁, t₂',
              v₁', w₂ ++ [x₂] ++ v₂, x₁', x₂',
              hq', hpermB₁, hEqB₁, hperm₂, hEqA₂, ?_, hmat⟩)
            simp only [hcons x₁ u₁', ite_eq_right hqx₁, List.nil_append, hproj]
          · -- B/B
            have hB₂ : u₂ <+: t₂' := by
              apply List.prefix_of_prefix_length_le hU₂ hL₂
              simp only [List.length_append, List.length_singleton] at hl₂ ⊢
              omega
            obtain ⟨w₂, hw₂⟩ := hB₂
            have hv₂ : v₂ = w₂ ++ ([x₂'] ++ v₂') := by
              have h := hEq₂
              rw [← hw₂] at h
              simp only [List.append_assoc] at h
              exact (List.append_cancel_left h).symm
            have hpermB₂ : List.PermUpTo I (u₂ ++ [x₂] ++ w₂) (x₂ :: u₂') := by
              have hrec : List.PermUpTo I (u₂ ++ w₂) u₂' := by
                rw [hw₂]
                exact hperm₂
              exact (List.PermUpTo.append_right w₂ (u₂ ++ [x₂]) ([x₂] ++ u₂) hswap₂).trans
                (List.PermUpTo.cons x₂ hrec)
            have hEqB₂ : (u₂ ++ [x₂] ++ w₂) ++ [x₂'] ++ v₂' = t₂ := by
              rw [ht₂, hv₂]
              simp only [List.append_assoc, List.cons_append, List.nil_append]
            refine Or.inr (Or.inr ⟨q, x₁ :: u₁', x₂ :: u₂',
              u₁ ++ [x₁] ++ w₁, u₂ ++ [x₂] ++ w₂, v₁', v₂', x₁', x₂',
              hq', hpermB₁, hEqB₁, hpermB₂, hEqB₂, ?_, hmat⟩)
            simp only [hcons x₁ u₁', hcons x₂ u₂']
            rw [heq, hproj]

end Helpers

theorem if_smurf_then_traces
    {pn : Label → Finset Pid}
    {lts : LTS State Label}
    {I : Label → Label → Prop}
    [Independence I]
    {B : Branching Label}
    {hpn₀ : ∀ l, (pn l).Nonempty}
    {hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂)}
    {hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → (pn l₁) = (pn l₂)}
    (h : Smurf lts I B) :
  ∀ {s : State} {t₁ t₂ : List Label} {p : Pid},
    t₁ ∈ lts.traces s ∧ t₂ ∈ lts.traces s →
    (
      ProjectTrace (pn := pn) t₁ p <+: ProjectTrace (pn := pn) t₂ p
      ∨
      ProjectTrace (pn := pn) t₂ p <+: ProjectTrace (pn := pn) t₁ p
      ∨
      (
        ∃ (q : Pid) (t₁' t₂' : List Label) (l₁ l₂ : Label),
          (
            t₁' ++ [l₁] <+: t₁
            ∧ t₂' ++ [l₂] <+: t₂
            ∧ B.matching l₁ l₂
            ∧ ProjectTrace (pn := pn) t₁' q = ProjectTrace (pn := pn) t₂' q
          )
      )
    )
  := by
    intro s t₁ t₂ p ⟨h₁, h₂⟩
    obtain ⟨s₁, ht₁⟩ := h₁
    obtain ⟨s₂, ht₂⟩ := h₂
    have h₃ : lts.MTr s t₁ s₁ ∧ lts.MTr s t₂ s₂ := by grind
    rcases prefix_or_match_permupto hpn₀ hpn₁ hpn₂ h s s₁ s₂ t₁ t₂ p h₃
        with hleft | hright | hmatch
    · exact Or.inl hleft
    · exact Or.inr (Or.inl hright)
    · obtain ⟨q, u₁, u₂, t₁', t₂', v₁, v₂, x₁, x₂,
              hq, hperm₁, hEq₁, hperm₂, hEq₂, hproj, hm⟩ := hmatch
      apply Or.inr
      apply Or.inr
      refine ⟨q, t₁', t₂', x₁, x₂, ?_, ?_, ?_, ?_⟩
      · rw [← hEq₁]
        exact List.prefix_append _ _
      · rw [← hEq₂]
        exact List.prefix_append _ _
      · exact hm
      · rw [permupto_equiv_proj I hpn₁ t₁' u₁ q hperm₁,
            permupto_equiv_proj I hpn₁ t₂' u₂ q hperm₂, hproj]

end Cslib.Concurrency
