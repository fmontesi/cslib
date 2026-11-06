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

/-- An enabled action whose label does not occur in a trace either matches a label
of that trace, or commutes past all of it. Irreflexivity of `matching` is what makes
the hypothesis `a ∉ u` necessary: the degenerate `matching a a` witness is not
available, and `Smurf.u` does not apply to equal labels. -/
private lemma commute_or_matching
    (h : Smurf lts I B) {s s₁ s₂ : State} {a : Label} {u : List Label} {p : Pid}
    (ha : lts.Tr s a s₁) (hu : lts.MTr s u s₂)
    (hne : a ∉ u) (hproj : ProjectTrace (pn := pn) u p = []) :
    (∃ v b, v ++ [b] <+: u ∧ B.matching a b) ∨
      ∃ s₃, lts.MTr s₁ u s₃ ∧ lts.Tr s₂ a s₃ := by
  induction hu generalizing s₁ with
  | refl => exact Or.inr ⟨s₁, .refl, ha⟩
  | @stepL s b sm v se hb hv ih =>
    have hpb : p ∉ pn b := by
      intro hp
      simp [ProjectTrace, hp] at hproj
    have hvproj : ProjectTrace (pn := pn) v p = [] := by
      simpa [ProjectTrace, hpb] using hproj
    have hne' : a ≠ b := by
      rintro rfl
      exact hne List.mem_cons_self
    have hne_v : a ∉ v := fun hmem => hne (List.mem_cons_of_mem b hmem)
    rcases h.u s s₁ sm a b hne' ⟨ha, hb⟩ with hind | hm
    · obtain ⟨sx, hs₁x, hsmx⟩ := h.f s s₁ sm a b ⟨hind, ha, hb⟩
      rcases ih hsmx hne_v hvproj with ⟨w, c, hw, hm⟩ | ⟨s₃, hx₃, he₃⟩
      · refine Or.inl ⟨b :: w, c, ?_, hm⟩
        obtain ⟨suffix, hsuffix⟩ := hw
        exact ⟨suffix, congrArg (b :: ·) hsuffix⟩
      · exact Or.inr ⟨s₃, .stepL hs₁x hx₃, he₃⟩
    · exact Or.inl ⟨[], b, ⟨v, rfl⟩, hm⟩

/-- The projection of `t ++ [l]` when `p` does not observe `l`. -/
private lemma projectTrace_concat_notMem (t : List Label) (l : Label) (p : Pid)
    (h : p ∉ pn l) :
    ProjectTrace (pn := pn) (t ++ [l]) p = ProjectTrace (pn := pn) t p := by
  unfold ProjectTrace
  rw [List.filter_append, List.filter_cons, List.filter_nil, decide_eq_false h]
  simp

/-- The projection of `t ++ [l]` when `p` observes `l`. -/
private lemma projectTrace_concat_mem (t : List Label) (l : Label) (p : Pid)
    (h : p ∈ pn l) :
    ProjectTrace (pn := pn) (t ++ [l]) p = ProjectTrace (pn := pn) t p ++ [l] := by
  unfold ProjectTrace
  rw [List.filter_append, List.filter_cons, List.filter_nil, decide_eq_true h]
  simp


/-- Split a trace at its last step; the prefix still starts at the original state. -/
private lemma mtr_split_last {s s' : State} {l : List Label} {a : Label}
    (h : lts.MTr s (l ++ [a]) s') : ∃ sm, lts.MTr s l sm ∧ lts.Tr sm a s' := by
  obtain ⟨sm, h1, h2⟩ := LTS.MTr.split h
  exact ⟨sm, h1, LTS.MTr.single_invert lts _ _ _ h2⟩

/-- Cancel a common prefix on the left of a prefix relation. -/
private lemma prefix_cancel_left {C X Y : List Label} (h : C ++ X <+: C ++ Y) :
    X <+: Y := by
  obtain ⟨W, hW⟩ := h
  rw [List.append_assoc] at hW
  exact ⟨W, List.append_cancel_left hW⟩

/-- A nonempty list that is a prefix of a singleton is that singleton. -/
private lemma eq_of_prefix_singleton {R : List Label} {x : Label}
    (hne : R ≠ []) (h : R <+: [x]) : R = [x] := by
  obtain ⟨W, hW⟩ := h
  have hlen : R.length + W.length = 1 := by
    simpa using congrArg List.length hW
  have hR1 : R.length = 1 := by
    cases R with
    | nil => exact absurd rfl hne
    | cons r R' =>
      cases R' with
      | nil => simp
      | cons r' R'' => simp at hlen; omega
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp hR1
  have hWnil : W = [] := by
    cases W with
    | nil => rfl
    | cons w W' => simp at hlen; omega
  subst hy
  have h2 : [y] ++ W = [x] := by simpa using hW
  rw [hWnil, List.append_nil] at h2
  simpa using h2

/-- The projection on `p` is monotone under appending a single label. -/
private lemma projectTrace_prefix_concat (t : List Label) (l : Label) (p : Pid) :
    ProjectTrace (pn := pn) t p <+: ProjectTrace (pn := pn) (t ++ [l]) p := by
  by_cases hl : p ∈ pn l
  · rw [projectTrace_concat_mem t l p hl]
    exact List.prefix_append _ _
  · rw [projectTrace_concat_notMem t l p hl]

omit [DecidableEq Pid] in
/-- If a nonempty list of labels is a prefix of a singleton, they are equal. -/
private lemma eq_of_singleton_prefix {a b : Label} (h : [a] <+: [b]) : a = b := by
  have h' : ([a] : List Label) = [b] := h.eq_of_length (by simp)
  simpa using h'

/-- The projection of a concatenation is the concatenation of the projections. -/
private lemma projectTrace_append (u w : List Label) :
    ProjectTrace (pn := pn) (u ++ w) p
      = ProjectTrace (pn := pn) u p ++ ProjectTrace (pn := pn) w p := by
  unfold ProjectTrace
  rw [List.filter_append]

/-- The projection of `u ++ c :: w` when `u` is unobserved and `c` is observed. -/
private lemma projectTrace_first {u : List Label} {c : Label} (w : List Label)
    (hu : ProjectTrace (pn := pn) u p = []) (hc : p ∈ pn c) :
    ProjectTrace (pn := pn) (u ++ c :: w) p = c :: ProjectTrace (pn := pn) w p := by
  rw [projectTrace_append, hu]
  simp [ProjectTrace, hc]

/-- Every list with nonempty projection splits as an unobserved prefix, an observed
label, and a remainder. -/
private lemma exists_first_observed {l : List Label}
    (h : ProjectTrace (pn := pn) l p ≠ []) :
    ∃ u c w, l = u ++ c :: w ∧ (∀ x ∈ u, p ∉ pn x) ∧ p ∈ pn c := by
  induction l with
  | nil => exact absurd rfl h
  | cons x xs ih =>
    by_cases hx : p ∈ pn x
    · exact ⟨[], x, xs, by simp, by simp, hx⟩
    · have hxs : ProjectTrace (pn := pn) xs p ≠ [] := by
        intro h0
        apply h
        simpa [ProjectTrace, hx] using h0
      obtain ⟨u, c, w, rfl, hu, hc⟩ := ih hxs
      refine ⟨x :: u, c, w, by simp, ?_, hc⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact hx
      · exact hu y hy'

omit [DecidableEq Pid] in
/-- A single step whose label is not observed by `p`. -/
private def UnobsStep (pn : Label → Finset Pid) (lts : LTS State Label) (p : Pid)
    (s t : State) : Prop :=
  ∃ l, p ∉ pn l ∧ lts.Tr s l t

/-- An unobserved multistep transition is a reflexive-transitive chain of unobserved
steps. -/
private lemma mtr_unobs_reflTransGen {s t : State} {u : List Label}
    (h : lts.MTr s u t) (hu : ProjectTrace (pn := pn) u p = []) :
    Relation.ReflTransGen (UnobsStep pn lts p) s t := by
  induction u generalizing s t with
  | nil =>
    cases h
    exact Relation.ReflTransGen.refl
  | cons z u' ih =>
    obtain ⟨sz, hz, hu'⟩ := LTS.MTr.cons_iff.mp h
    have hzU : p ∉ pn z := by
      intro hp
      simp [ProjectTrace, hp] at hu
    have hu'P : ProjectTrace (pn := pn) u' p = [] := by
      simpa [ProjectTrace, hzU] using hu
    exact Relation.ReflTransGen.head ⟨z, hzU, hz⟩ (ih hu' hu'P)

/-- A reflexive-transitive chain of unobserved steps is an unobserved multistep
transition. -/
private lemma reflTransGen_unobs_mtr {s t : State}
    (h : Relation.ReflTransGen (UnobsStep pn lts p) s t) :
    ∃ u, lts.MTr s u t ∧ ProjectTrace (pn := pn) u p = [] := by
  induction h with
  | refl => exact ⟨[], .refl, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨u, hu, hup⟩ := ih
    obtain ⟨l, hl, htr⟩ := hbc
    exact ⟨u ++ [l], hu.stepR lts htr, by
      rw [projectTrace_concat_notMem u l p hl, hup]⟩

/-- An observed label enabled at a state stays enabled after any unobserved trace
starting at that state. -/
private lemma push_obs_enabled (h : Smurf lts I B)
    (hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → pn l₁ = pn l₂)
    {s τ : State} {c : Label} {u : List Label} (hc : p ∈ pn c)
    {s' : State} (htr : lts.Tr s c s') (hu : lts.MTr s u τ)
    (hup : ProjectTrace (pn := pn) u p = []) :
    ∃ τ', lts.Tr τ c τ' := by
  induction u generalizing s s' τ with
  | nil =>
    cases hu
    exact ⟨s', htr⟩
  | cons z u' ih =>
    obtain ⟨sz, hz, hu'⟩ := LTS.MTr.cons_iff.mp hu
    have hzu : p ∉ pn z := by
      intro hp
      simp [ProjectTrace, hp] at hup
    have hup' : ProjectTrace (pn := pn) u' p = [] := by
      simpa [ProjectTrace, hzu] using hup
    have hzc : z ≠ c := fun hEq => hzu (hEq ▸ hc)
    have hind : I c z := by
      rcases h.u s s' sz c z (Ne.symm hzc) ⟨htr, hz⟩ with hi | hm
      · exact hi
      · exact absurd ((hpn₂ c z hm) ▸ hc) hzu
    obtain ⟨sx, hs'x, hszx⟩ := h.f s s' sz c z ⟨hind, htr, hz⟩
    exact ih hszx hu' hup'

/-- A label enabled both before an unobserved trace and after it can be commuted
after the trace, keeping the same target state. -/
private lemma push_obs_mtr (h : Smurf lts I B)
    (hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → pn l₁ = pn l₂)
    {s s' τ τ' : State} {c : Label} {u : List Label} (hc : p ∈ pn c)
    (htr : lts.Tr s c s') (hu : lts.MTr s u τ) (hτ : lts.Tr τ c τ')
    (hup : ProjectTrace (pn := pn) u p = []) :
    lts.MTr s' u τ' := by
  induction u generalizing s s' τ τ' with
  | nil =>
    cases hu
    have hEq : s' = τ' := h.d s s' τ' c htr hτ
    rw [hEq]
    exact .refl
  | cons z u' ih =>
    obtain ⟨sz, hz, hu'⟩ := LTS.MTr.cons_iff.mp hu
    have hzu : p ∉ pn z := by
      intro hp
      simp [ProjectTrace, hp] at hup
    have hup' : ProjectTrace (pn := pn) u' p = [] := by
      simpa [ProjectTrace, hzu] using hup
    have hzc : z ≠ c := fun hEq => hzu (hEq ▸ hc)
    have hind : I c z := by
      rcases h.u s s' sz c z (Ne.symm hzc) ⟨htr, hz⟩ with hi | hm
      · exact hi
      · exact absurd ((hpn₂ c z hm) ▸ hc) hzu
    obtain ⟨sx, hs'x, hszx⟩ := h.f s s' sz c z ⟨hind, htr, hz⟩
    exact .stepL hs'x (ih hszx hu' hτ hup')

/-! ### Unobserved executions

The alignment argument compares executions along labels that `p` does not observe.
Two such executions out of a common state either already expose a matching pair of
labels, or can be joined by further unobserved executions.

Because *every* label involved is unobserved, a conflict found among them is a valid
one no matter where the two matching labels sit: any prefixes project to the empty
trace, so the two projections agree automatically.  Positions therefore do not matter
at this layer, which is what keeps it independent of the trace bookkeeping needed for
the observed labels. -/

/-- A list of labels, none of which involves `p`. -/
private def Unobs (pn : Label → Finset Pid) (p : Pid) (L : List Label) : Prop :=
  ∀ x ∈ L, p ∉ pn x

omit [DecidableEq Pid] in
private lemma unobs_nil : Unobs pn p [] := fun x hx => by simp at hx

omit [DecidableEq Pid] in
private lemma unobs_cons {x : Label} {L : List Label} :
    Unobs pn p (x :: L) ↔ p ∉ pn x ∧ Unobs pn p L := by
  refine ⟨fun h => ⟨h x List.mem_cons_self, fun y hy => h y (List.mem_cons_of_mem x hy)⟩, ?_⟩
  rintro ⟨hx, hL⟩ y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hx
  · exact hL y hy

omit [DecidableEq Pid] in
private lemma Unobs.append {L₁ L₂ : List Label} (h₁ : Unobs pn p L₁) (h₂ : Unobs pn p L₂) :
    Unobs pn p (L₁ ++ L₂) := fun x hx => by
  rcases List.mem_append.mp hx with h | h
  exacts [h₁ x h, h₂ x h]

omit [DecidableEq Pid] in
private lemma Unobs.left {L₁ L₂ : List Label} (h : Unobs pn p (L₁ ++ L₂)) : Unobs pn p L₁ :=
  fun x hx => h x (List.mem_append_left L₂ hx)

omit [DecidableEq Pid] in
private lemma Unobs.right {L₁ L₂ : List Label} (h : Unobs pn p (L₁ ++ L₂)) : Unobs pn p L₂ :=
  fun x hx => h x (List.mem_append_right L₁ hx)

private lemma Unobs.projTrace_nil {L : List Label} (h : Unobs pn p L) :
    ProjectTrace (pn := pn) L p = [] :=
  projectTrace_eq_nil h

omit [DecidableEq Pid] in
/-- `t` is reached from `s` along an execution whose labels all avoid `p`. -/
private def UReach (lts : LTS State Label) (pn : Label → Finset Pid) (p : Pid)
    (s t : State) : Prop :=
  ∃ w, lts.MTr s w t ∧ Unobs pn p w

omit [DecidableEq Pid] in
/-- Two states are joinable when they have a common descendant along unobserved
executions. -/
private def UJoin (lts : LTS State Label) (pn : Label → Finset Pid) (p : Pid)
    (s t : State) : Prop :=
  ∃ ρ, UReach lts pn p s ρ ∧ UReach lts pn p t ρ

omit [DecidableEq Pid] in
private lemma UReach.refl (s : State) : UReach lts pn p s s := ⟨[], .refl, unobs_nil⟩

omit [DecidableEq Pid] in
private lemma UReach.single {s t : State} {l : Label} (h : lts.Tr s l t) (hl : p ∉ pn l) :
    UReach lts pn p s t :=
  ⟨[l], .stepL h .refl, fun x hx => by
    rw [List.mem_singleton] at hx
    exact hx ▸ hl⟩

omit [DecidableEq Pid] in
private lemma UReach.trans {s t u : State} (h₁ : UReach lts pn p s t)
    (h₂ : UReach lts pn p t u) : UReach lts pn p s u := by
  obtain ⟨w₁, hm₁, hu₁⟩ := h₁
  obtain ⟨w₂, hm₂, hu₂⟩ := h₂
  exact ⟨w₁ ++ w₂, LTS.MTr.comp lts hm₁ hm₂, hu₁.append hu₂⟩

omit [DecidableEq Pid] in
private lemma UJoin.refl (s : State) : UJoin lts pn p s s :=
  ⟨s, UReach.refl s, UReach.refl s⟩

omit [DecidableEq Pid] in
private lemma UJoin.symm {s t : State} (h : UJoin lts pn p s t) : UJoin lts pn p t s := by
  obtain ⟨ρ, h₁, h₂⟩ := h
  exact ⟨ρ, h₂, h₁⟩

omit [DecidableEq Pid] in
private lemma UJoin.of_reach {s t ρ : State} (h₁ : UReach lts pn p s ρ)
    (h₂ : UReach lts pn p t ρ) : UJoin lts pn p s t := ⟨ρ, h₁, h₂⟩

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

omit [DecidableEq Pid] in
/-- Trace-equivalent unobserved executions are joinable. -/
private lemma ujoin_of_permUpTo (h : Smurf lts I B) {u v : List Label}
    (hp : List.PermUpTo I u v) {s τ₁ τ₂ : State}
    (h₁ : lts.MTr s u τ₁) (h₂ : lts.MTr s v τ₂) : UJoin lts pn p τ₁ τ₂ :=
  (mtr_det_permUpTo h hp h₁ h₂) ▸ UJoin.refl τ₁

omit [DecidableEq Pid] in
/-- Membership transfers to a list containing the given one as a prefix. -/
private lemma mem_of_prefix {l₁ l₂ : List Label} {c : Label} (h : l₁ <+: l₂) (hc : c ∈ l₁) :
    c ∈ l₂ := by
  obtain ⟨suf, rfl⟩ := h
  exact List.mem_append_left suf hc

omit [DecidableEq Pid] in
/-- Split a list at an occurrence of one of its members, with no earlier occurrence. -/
private lemma exists_split_of_mem {L : List Label} {a : Label} (h : a ∈ L) :
    ∃ w w', L = w ++ a :: w' ∧ a ∉ w := by
  induction L with
  | nil => exact absurd h (by simp)
  | cons b L' ih =>
    by_cases hab : a = b
    · subst hab
      exact ⟨[], L', rfl, by simp⟩
    · have h' : a ∈ L' := by
        rcases List.mem_cons.mp h with h' | h'
        · exact absurd h' hab
        · exact h'
      obtain ⟨w, w', hL, hw⟩ := ih h'
      refine ⟨b :: w, w', by simp [hL], ?_⟩
      intro hmem
      rcases List.mem_cons.mp hmem with h'' | h''
      · exact hab h''
      · exact hw h''

/-- **Conflict or join for unobserved executions, with side-tagged witnesses.**

Two executions along labels that `p` does not observe either already expose a conflict —
a label of the first execution `matching` a label of the second — or each can be joined to
the other's end by replaying *the other side's* labels.  Tagging the two completions this
way is what makes the conflicts reported downstream usable: a matching pair always has one
label from each side, hence one label from each of the two ambient traces.

The bound on the total length drives the induction. -/
private lemma unobs_conflict_or_join (h : Smurf lts I B) (n : ℕ) :
    ∀ {s : State} {u₁ u₂ : List Label} {τ₁ τ₂ : State},
      u₁.length + u₂.length ≤ n →
      lts.MTr s u₁ τ₁ → lts.MTr s u₂ τ₂ → Unobs pn p u₁ → Unobs pn p u₂ →
      (∃ c₁ c₂, c₁ ∈ u₁ ∧ c₂ ∈ u₂ ∧ B.matching c₁ c₂) ∨
      (∃ (v₂ v₁ : List Label) (ρ : State),
        lts.MTr τ₁ v₂ ρ ∧ lts.MTr τ₂ v₁ ρ ∧
        (∀ c ∈ v₂, c ∈ u₂) ∧ (∀ c ∈ v₁, c ∈ u₁)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s u₁ u₂ τ₁ τ₂ hn hm₁ hm₂ hu₁ hu₂
    rcases u₁ with _ | ⟨x, u₁'⟩
    · -- the first execution is empty: the second replays itself
      have hτ : s = τ₁ := LTS.MTr.nil_eq lts hm₁
      exact Or.inr ⟨u₂, [], τ₂, hτ ▸ hm₂, .refl, fun c hc => hc, fun c hc => by simp at hc⟩
    rcases u₂ with _ | ⟨y, u₂'⟩
    · -- the second execution is empty: the first replays itself
      have hτ : s = τ₂ := LTS.MTr.nil_eq lts hm₂
      exact Or.inr ⟨[], x :: u₁', τ₁, .refl, hτ ▸ hm₁,
        fun c hc => by simp at hc, fun c hc => hc⟩
    obtain ⟨σ₁, hx, hm₁'⟩ := LTS.MTr.cons_iff.mp hm₁
    obtain ⟨σ₂, hy, hm₂'⟩ := LTS.MTr.cons_iff.mp hm₂
    have hxu : p ∉ pn x := (unobs_cons.mp hu₁).1
    have hu₁' : Unobs pn p u₁' := (unobs_cons.mp hu₁).2
    have hyu : p ∉ pn y := (unobs_cons.mp hu₂).1
    have hu₂' : Unobs pn p u₂' := (unobs_cons.mp hu₂).2
    by_cases hxy : x = y
    · -- equal labels: both executions continue from the same state
      subst hxy
      have hσ : σ₁ = σ₂ := h.d s σ₁ σ₂ x hx hy
      subst hσ
      have hlen : u₁'.length + u₂'.length < n := by
        simp only [List.length_cons] at hn
        omega
      rcases ih _ hlen (le_refl _) hm₁' hm₂' hu₁' hu₂' with
        ⟨c₁, c₂, hc₁, hc₂, hm⟩ | ⟨v₂, v₁, ρ, hM₁, hM₂, hv₂, hv₁⟩
      · exact Or.inl ⟨c₁, c₂, List.mem_cons_of_mem x hc₁, List.mem_cons_of_mem x hc₂, hm⟩
      · exact Or.inr ⟨v₂, v₁, ρ, hM₁, hM₂,
          fun c hc => List.mem_cons_of_mem x (hv₂ c hc),
          fun c hc => List.mem_cons_of_mem x (hv₁ c hc)⟩
    rcases h.u s σ₁ σ₂ x y hxy ⟨hx, hy⟩ with hind | hmatch
    · -- the two labels are independent: exchange them
      obtain ⟨z, hσ₁y, hσ₂x⟩ := h.f s σ₁ σ₂ x y ⟨hind, hx, hy⟩
      by_cases hy₁ : y ∈ u₁'
      · -- `y` also occurs in the first execution, after its head
        obtain ⟨w, w', hdec, hw⟩ := exists_split_of_mem hy₁
        subst hdec
        obtain ⟨μ, hμ, hm'⟩ := LTS.MTr.split hm₁'
        obtain ⟨μ', hμy, hμw'⟩ := LTS.MTr.cons_iff.mp hm'
        have hμu : Unobs pn p w := fun c hc => hu₁' c (List.mem_append_left _ hc)
        rcases commute_or_matching h hσ₁y hμ hw hμu.projTrace_nil with
          ⟨v, c, hv, hmat⟩ | ⟨s', hzw, hyμ⟩
        · -- a conflict inside the first execution
          have hc : c ∈ w := mem_of_prefix hv (by simp)
          exact Or.inl ⟨c, y, List.mem_cons_of_mem x (List.mem_append_left _ hc),
            List.mem_cons_self, matching_comm hmat⟩
        · -- `y` is available right after the first step, so the rest commutes
          have hEq : s' = μ' := h.d μ s' μ' y hyμ hμy
          subst hEq
          have hzw' : lts.MTr z (w ++ w') τ₁ := LTS.MTr.comp lts hzw hμw'
          have hA : lts.MTr σ₂ (x :: (w ++ w')) τ₁ := .stepL hσ₂x hzw'
          have huA : Unobs pn p (x :: (w ++ w')) := by
            intro c hc
            refine hu₁ c ?_
            simp only [List.mem_append, List.mem_cons] at hc ⊢
            tauto
          have hlen : (x :: (w ++ w')).length + u₂'.length < n := by
            simp only [List.length_append, List.length_cons] at hn ⊢
            omega
          rcases ih _ hlen (le_refl _) hA hm₂' huA hu₂' with
            ⟨c₁, c₂, hc₁, hc₂, hm⟩ | ⟨v₂, v₁, ρ, hM₁, hM₂, hv₂, hv₁⟩
          · refine Or.inl ⟨c₁, c₂, ?_, List.mem_cons_of_mem y hc₂, hm⟩
            simp only [List.mem_append, List.mem_cons] at hc₁ ⊢
            tauto
          · refine Or.inr ⟨v₂, v₁, ρ, hM₁, hM₂, fun c hc => ?_, fun c hc => ?_⟩
            · exact List.mem_cons_of_mem y (hv₂ c hc)
            · have h := hv₁ c hc
              simp only [List.mem_append, List.mem_cons] at h ⊢
              tauto
      by_cases hx₂ : x ∈ u₂'
      · -- symmetrically, `x` occurs in the second execution
        obtain ⟨w, w', hdec, hw⟩ := exists_split_of_mem hx₂
        subst hdec
        obtain ⟨μ, hμ, hm'⟩ := LTS.MTr.split hm₂'
        obtain ⟨μ', hμx, hμw'⟩ := LTS.MTr.cons_iff.mp hm'
        have hμu : Unobs pn p w := fun c hc => hu₂' c (List.mem_append_left _ hc)
        rcases commute_or_matching h hσ₂x hμ hw hμu.projTrace_nil with
          ⟨v, c, hv, hmat⟩ | ⟨s', hzw, hxμ⟩
        · have hc : c ∈ w := mem_of_prefix hv (by simp)
          exact Or.inl ⟨x, c, List.mem_cons_self,
            List.mem_cons_of_mem y (List.mem_append_left _ hc), hmat⟩
        · have hEq : s' = μ' := h.d μ s' μ' x hxμ hμx
          subst hEq
          have hzw' : lts.MTr z (w ++ w') τ₂ := LTS.MTr.comp lts hzw hμw'
          have hB : lts.MTr σ₁ (y :: (w ++ w')) τ₂ := .stepL hσ₁y hzw'
          have huB : Unobs pn p (y :: (w ++ w')) := by
            intro c hc
            refine hu₂ c ?_
            simp only [List.mem_append, List.mem_cons] at hc ⊢
            tauto
          have hlen : u₁'.length + (y :: (w ++ w')).length < n := by
            simp only [List.length_append, List.length_cons] at hn ⊢
            omega
          rcases ih _ hlen (le_refl _) hm₁' hB hu₁' huB with
            ⟨c₁, c₂, hc₁, hc₂, hm⟩ | ⟨v₂, v₁, ρ, hM₁, hM₂, hv₂, hv₁⟩
          · refine Or.inl ⟨c₁, c₂, List.mem_cons_of_mem x hc₁, ?_, hm⟩
            simp only [List.mem_append, List.mem_cons] at hc₂ ⊢
            tauto
          · refine Or.inr ⟨v₂, v₁, ρ, hM₁, hM₂, fun c hc => ?_, fun c hc => ?_⟩
            · have h := hv₂ c hc
              simp only [List.mem_append, List.mem_cons] at h ⊢
              tauto
            · exact List.mem_cons_of_mem x (hv₁ c hc)
      · -- neither label recurs: both are available at the diamond, then recurse
        rcases commute_or_matching h hσ₁y hm₁' hy₁ hu₁'.projTrace_nil with
          ⟨v, c, hv, hmat⟩ | ⟨s₁', hzs₁, hτ₁y⟩
        · have hc : c ∈ u₁' := mem_of_prefix hv (by simp)
          exact Or.inl ⟨c, y, List.mem_cons_of_mem x hc, List.mem_cons_self,
            matching_comm hmat⟩
        · rcases commute_or_matching h hσ₂x hm₂' hx₂ hu₂'.projTrace_nil with
            ⟨v, c, hv, hmat⟩ | ⟨s₂', hzs₂, hτ₂x⟩
          · have hc : c ∈ u₂' := mem_of_prefix hv (by simp)
            exact Or.inl ⟨x, c, List.mem_cons_self, List.mem_cons_of_mem y hc, hmat⟩
          · have hlen : u₁'.length + u₂'.length < n := by
              simp only [List.length_cons] at hn
              omega
            rcases ih _ hlen (le_refl _) hzs₁ hzs₂ hu₁' hu₂' with
              ⟨c₁, c₂, hc₁, hc₂, hm⟩ | ⟨v₂, v₁, ρ, hM₁, hM₂, hv₂, hv₁⟩
            · exact Or.inl ⟨c₁, c₂, List.mem_cons_of_mem x hc₁,
                List.mem_cons_of_mem y hc₂, hm⟩
            · refine Or.inr ⟨y :: v₂, x :: v₁, ρ, .stepL hτ₁y hM₁, .stepL hτ₂x hM₂,
                fun c hc => ?_, fun c hc => ?_⟩
              · rcases List.mem_cons.mp hc with rfl | hc
                · exact List.mem_cons_self
                · exact List.mem_cons_of_mem y (hv₂ c hc)
              · rcases List.mem_cons.mp hc with rfl | hc
                · exact List.mem_cons_self
                · exact List.mem_cons_of_mem x (hv₁ c hc)
    · -- the two labels match
      exact Or.inl ⟨x, y, List.mem_cons_self, List.mem_cons_self, hmatch⟩

/-- The joinability form of `unobs_conflict_or_join`: the tagged completions are
unobserved, since each replays labels of a `p`-unobserved execution. -/
private lemma ujoin_of_unobs (h : Smurf lts I B) {s : State} {u₁ u₂ : List Label}
    {τ₁ τ₂ : State} (hm₁ : lts.MTr s u₁ τ₁) (hm₂ : lts.MTr s u₂ τ₂)
    (hu₁ : Unobs pn p u₁) (hu₂ : Unobs pn p u₂) :
    (∃ c₁ c₂, c₁ ∈ u₁ ∧ c₂ ∈ u₂ ∧ B.matching c₁ c₂) ∨ UJoin lts pn p τ₁ τ₂ := by
  rcases unobs_conflict_or_join h (u₁.length + u₂.length) (le_refl _) hm₁ hm₂ hu₁ hu₂ with
    hc | ⟨v₂, v₁, ρ, hM₁, hM₂, hv₂, hv₁⟩
  · exact Or.inl hc
  · exact Or.inr ⟨ρ, ⟨v₂, hM₁, fun c hc => hu₂ c (hv₂ c hc)⟩,
      ⟨v₁, hM₂, fun c hc => hu₁ c (hv₁ c hc)⟩⟩

/-- Base case of the alignment lemma: both executions are entirely `p`-unobserved.

Every prefix of either execution then projects to the empty trace, so *any* matching
pair of labels — one from each execution — is a valid witness, and the two final labels
`l₁`, `l₂` become co-enabled once both executions are joined. -/
private lemma aligned_conflict_unobs {s u₁ u₂ s₁ s₂ : State} {Ar Br : List Label}
    {l₁ l₂ : Label} {p : Pid}
    (h : Smurf lts I B)
    (hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂))
    (hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → pn l₁ = pn l₂)
    (hA : lts.MTr s Ar u₁) (hB : lts.MTr s Br u₂)
    (huA : Unobs pn p Ar) (huB : Unobs pn p Br)
    (hlast₁ : lts.Tr u₁ l₁ s₁) (hlast₂ : lts.Tr u₂ l₂ s₂)
    (hl₁ : p ∈ pn l₁) (hl₂ : p ∈ pn l₂) (hll : l₁ ≠ l₂) :
    ∃ (q : Pid) (x₁ x₂ : List Label) (m₁ m₂ : Label),
      x₁ ++ [m₁] <+: Ar ++ [l₁] ∧ x₂ ++ [m₂] <+: Br ++ [l₂] ∧
      B.matching m₁ m₂ ∧
        ProjectTrace (pn := pn) x₁ q = ProjectTrace (pn := pn) x₂ q := by
  have hprojA : ProjectTrace (pn := pn) Ar p = [] := huA.projTrace_nil
  have hprojB : ProjectTrace (pn := pn) Br p = [] := huB.projTrace_nil
  rcases ujoin_of_unobs h hA hB huA huB with
    ⟨c₁, c₂, hc₁, hc₂, hmat⟩ | ⟨ρ, ⟨v₂, hM₁, hv₂u⟩, ⟨v₁, hM₂, hv₁u⟩⟩
  · -- a matching pair among the labels themselves: stop just before both
    obtain ⟨v₁', w₁', hdec₁, _⟩ := exists_split_of_mem hc₁
    obtain ⟨v₂', w₂', hdec₂, _⟩ := exists_split_of_mem hc₂
    have hv₁'u : Unobs pn p v₁' := by
      intro c hc
      refine huA c ?_
      rw [hdec₁]
      exact List.mem_append_left _ hc
    have hv₂'u : Unobs pn p v₂' := by
      intro c hc
      refine huB c ?_
      rw [hdec₂]
      exact List.mem_append_left _ hc
    refine ⟨p, v₁', v₂', c₁, c₂, ?_, ?_, hmat, ?_⟩
    · refine (show v₁' ++ [c₁] <+: Ar from ?_).trans (List.prefix_append Ar [l₁])
      rw [hdec₁]
      exact ⟨w₁', by simp⟩
    · refine (show v₂' ++ [c₂] <+: Br from ?_).trans (List.prefix_append Br [l₂])
      rw [hdec₂]
      exact ⟨w₂', by simp⟩
    · rw [hv₁'u.projTrace_nil, hv₂'u.projTrace_nil]
  · -- no conflict: both executions are joined, so the last two labels are co-enabled
    obtain ⟨τ₁', hτ₁'⟩ := push_obs_enabled h hpn₂ hl₁ hlast₁ hM₁ hv₂u.projTrace_nil
    obtain ⟨τ₂', hτ₂'⟩ := push_obs_enabled h hpn₂ hl₂ hlast₂ hM₂ hv₁u.projTrace_nil
    rcases h.u ρ τ₁' τ₂' l₁ l₂ hll ⟨hτ₁', hτ₂'⟩ with hind | hm
    · exact absurd (hpn₁ l₁ l₂ hind) (Finset.not_disjoint_iff.mpr ⟨p, hl₁, hl₂⟩)
    · exact ⟨p, Ar, Br, l₁, l₂, List.prefix_refl _, List.prefix_refl _, hm,
        by rw [hprojA, hprojB]⟩

/-- **Alignment lemma (the combinatorial heart of the theorem).**

Two executions out of a common state whose prefixes have the same projection on `p`,
and whose last steps are labelled by distinct `p`-observed labels, exhibit a matching
pair at prefixes with equal projections.

This is the grid ("bubble") chase: because `hEq` already supplies prefixes with equal
projections, it is enough to find labels `m₁`, `m₂` that are `matching` and lie at the
same projection position in the two traces.  `unobs_conflict_or_join` supplies the
unobserved gaps, and `push_obs_enabled` / `push_obs_mtr` carry the shared observed
labels across a join, so the walk can advance one projection position at a time. -/
private lemma aligned_conflict {s u₁ u₂ s₁ s₂ : State} {t₁' t₂' : List Label}
    {l₁ l₂ : Label} {p : Pid}
    (h : Smurf lts I B)
    (hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂))
    (hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → pn l₁ = pn l₂)
    (ht₁' : lts.MTr s t₁' u₁) (ht₂' : lts.MTr s t₂' u₂)
    (hlast₁ : lts.Tr u₁ l₁ s₁) (hlast₂ : lts.Tr u₂ l₂ s₂)
    (hEq : ProjectTrace (pn := pn) t₁' p = ProjectTrace (pn := pn) t₂' p)
    (hl₁ : p ∈ pn l₁) (hl₂ : p ∈ pn l₂) (hll : l₁ ≠ l₂) :
    ∃ (q : Pid) (x₁ x₂ : List Label) (m₁ m₂ : Label),
      x₁ ++ [m₁] <+: t₁' ++ [l₁] ∧ x₂ ++ [m₂] <+: t₂' ++ [l₂] ∧
      B.matching m₁ m₂ ∧
        ProjectTrace (pn := pn) x₁ q = ProjectTrace (pn := pn) x₂ q := by
  sorry

/-- Branching case: two traces with equal projections that end in distinct labels
observed by `p`.  The hypothesis already provides the prefixes, so the conclusion is
supplied by the alignment lemma. -/
private lemma core_branch {s u₁ u₂ s₁ s₂ : State} {t₁' t₂' : List Label}
    {l₁ l₂ : Label} {p : Pid}
    (h : Smurf lts I B)
    (hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂))
    (hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → pn l₁ = pn l₂)
    (hpn₀ : ∀ l, (pn l).Nonempty)
    (ht₁' : lts.MTr s t₁' u₁) (ht₂' : lts.MTr s t₂' u₂)
    (hlast₁ : lts.Tr u₁ l₁ s₁) (hlast₂ : lts.Tr u₂ l₂ s₂)
    (hEq : ProjectTrace (pn := pn) t₁' p = ProjectTrace (pn := pn) t₂' p)
    (hl₁ : p ∈ pn l₁) (hl₂ : p ∈ pn l₂) (hll : l₁ ≠ l₂) :
    ∃ (q : Pid) (x₁ x₂ : List Label) (m₁ m₂ : Label),
      x₁ ++ [m₁] <+: t₁' ++ [l₁] ∧ x₂ ++ [m₂] <+: t₂' ++ [l₂] ∧
      B.matching m₁ m₂ ∧
        ProjectTrace (pn := pn) x₁ q = ProjectTrace (pn := pn) x₂ q := by
  classical
  -- The hypothesis `hpn₀` is part of the interface; the argument does not need it.
  obtain ⟨_, _⟩ := hpn₀ l₁
  -- If the state space is a subsingleton, `l₁` and `l₂` are enabled at the same
  -- state, so they must be a matching pair at the prefixes `t₁'`, `t₂'`.
  by_cases hsingle : ∀ a b : State, a = b
  · have hlast₂' : lts.Tr u₁ l₂ s₂ := by
      rw [hsingle u₁ u₂]
      exact hlast₂
    rcases h.u u₁ s₁ s₂ l₁ l₂ hll ⟨hlast₁, hlast₂'⟩ with hind | hm
    · exact absurd (hpn₁ l₁ l₂ hind) (Finset.not_disjoint_iff.mpr ⟨p, hl₁, hl₂⟩)
    · exact ⟨p, t₁', t₂', l₁, l₂, List.prefix_refl _, List.prefix_refl _, hm, hEq⟩
  · exact aligned_conflict h hpn₁ hpn₂ ht₁' ht₂' hlast₁ hlast₂ hEq hl₁ hl₂ hll

/-- Two traces out of the same state satisfy the trichotomy.

The induction splits both traces at their **last** label (`t = t' ++ [l]`), not at
their head. This keeps both prefixes `t₁'` and `t₂'` anchored at the same state `s`,
so the induction hypothesis applies directly to them.

If the prefix projections differ, the induction hypothesis is applied to the
smaller pair `(t₁, t₂')` (resp. `(t₁', t₂)`): the extra observed label has to be
the last element of the difference, which yields a prefix relation.  Only the case
of equal prefix projections with distinct observed final labels remains; it is the
branching point of the two traces. -/
private lemma core {s : State} {t₁ t₂ : List Label} {p : Pid}
    (h : Smurf lts I B)
    (hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂))
    (hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → pn l₁ = pn l₂)
    (hpn₀ : ∀ l, (pn l).Nonempty)
    {s₁ s₂ : State} (ht₁ : lts.MTr s t₁ s₁) (ht₂ : lts.MTr s t₂ s₂) :
    ProjectTrace (pn := pn) t₁ p <+: ProjectTrace (pn := pn) t₂ p ∨
    ProjectTrace (pn := pn) t₂ p <+: ProjectTrace (pn := pn) t₁ p ∨
    (∃ (q : Pid) (t₁' t₂' : List Label) (l₁ l₂ : Label),
        t₁' ++ [l₁] <+: t₁ ∧ t₂' ++ [l₂] <+: t₂ ∧ B.matching l₁ l₂ ∧
        ProjectTrace (pn := pn) t₁' q = ProjectTrace (pn := pn) t₂' q) := by
  classical
  induction hn : t₁.length + t₂.length using Nat.strong_induction_on generalizing
      s t₁ t₂ s₁ s₂ with
  | _ n ihp =>
    -- Handle the trivial cases first.
    rcases List.eq_nil_or_concat t₁ with rfl | ⟨t₁', l₁, rfl⟩
    · exact Or.inl (by simp [ProjectTrace])
    · rcases List.eq_nil_or_concat t₂ with rfl | ⟨t₂', l₂, rfl⟩
      · exact Or.inr (Or.inl (by simp [ProjectTrace]))
      · -- both traces are nonempty: split the last step off each
        obtain ⟨u₁, ht₁', hlast₁⟩ := mtr_split_last
          (l := t₁') (a := l₁) (by simpa using ht₁)
        obtain ⟨u₂, ht₂', hlast₂⟩ := mtr_split_last
          (l := t₂') (a := l₂) (by simpa using ht₂)
        simp only [List.concat_eq_append] at ht₁ ht₂ hn ⊢
        -- induction hypothesis on the prefixes, both still starting at `s`
        have hlen : t₁'.length + t₂'.length < n := by
          simp only [List.length_append, List.length_singleton] at hn ⊢
          omega
        rcases ihp (t₁'.length + t₂'.length) hlen
          (s := s) (s₁ := u₁) (s₂ := u₂) ht₁' ht₂' rfl with h1 | h2 | h3
        · -- `ProjectTrace t₁' p <+: ProjectTrace t₂' p`
          by_cases hEq : ProjectTrace (pn := pn) t₁' p
              = ProjectTrace (pn := pn) t₂' p
          · -- Equal prefix projections: the final labels decide.
            by_cases hl₁ : p ∈ pn l₁
            · by_cases hl₂ : p ∈ pn l₂
              · by_cases hll : l₁ = l₂
                · subst hll
                  refine Or.inl ?_
                  rw [projectTrace_concat_mem t₁' l₁ p hl₁,
                    projectTrace_concat_mem t₂' l₁ p hl₂, hEq]
                · exact Or.inr (Or.inr (core_branch h hpn₁ hpn₂ hpn₀ ht₁' ht₂'
                    hlast₁ hlast₂ hEq hl₁ hl₂ hll))
              · refine Or.inr (Or.inl ?_)
                rw [projectTrace_concat_mem t₁' l₁ p hl₁,
                  projectTrace_concat_notMem t₂' l₂ p hl₂, hEq]
                exact List.prefix_append _ _
            · refine Or.inl ?_
              by_cases hl₂ : p ∈ pn l₂
              · rw [projectTrace_concat_notMem t₁' l₁ p hl₁,
                  projectTrace_concat_mem t₂' l₂ p hl₂, hEq]
                exact List.prefix_append _ _
              · rw [projectTrace_concat_notMem t₁' l₁ p hl₁,
                  projectTrace_concat_notMem t₂' l₂ p hl₂, hEq]
          · -- `P(t₂')` properly extends `P(t₁')`: compare `t₁` with `t₂'`.
            obtain ⟨R, hR⟩ := h1
            have hRne : R ≠ [] := by
              intro h0
              exact hEq (by rw [← hR, h0, List.append_nil])
            have hlt : (t₁' ++ [l₁]).length + t₂'.length < n := by
              simp only [List.length_append, List.length_singleton] at hn ⊢
              omega
            rcases ihp ((t₁' ++ [l₁]).length + t₂'.length) hlt
              (s := s) (s₁ := s₁) (s₂ := u₂) ht₁ ht₂' rfl
              with hres | hres | hres
            · exact Or.inl (hres.trans (projectTrace_prefix_concat t₂' l₂ p))
            · -- `P(t₂') <+: P(t₁)`: then `R = [l₁]`.
              by_cases hl₁ : p ∈ pn l₁
              · rw [projectTrace_concat_mem t₁' l₁ p hl₁] at hres
                rw [← hR] at hres
                have hRle : R <+: [l₁] := prefix_cancel_left hres
                have hReq : R = [l₁] := eq_of_prefix_singleton hRne hRle
                refine Or.inl ?_
                rw [projectTrace_concat_mem t₁' l₁ p hl₁]
                by_cases hl₂ : p ∈ pn l₂
                · rw [projectTrace_concat_mem t₂' l₂ p hl₂, ← hR, hReq]
                  exact List.prefix_append _ _
                · rw [projectTrace_concat_notMem t₂' l₂ p hl₂, ← hR, hReq]
              · rw [projectTrace_concat_notMem t₁' l₁ p hl₁] at hres
                have hE : ProjectTrace (pn := pn) t₁' p
                    = ProjectTrace (pn := pn) t₂' p :=
                  List.IsPrefix.eq_of_length ⟨R, hR⟩ (by
                    have h1len := List.IsPrefix.length_le
                      (⟨R, hR⟩ :
                        ProjectTrace (pn := pn) t₁' p <+: ProjectTrace (pn := pn) t₂' p)
                    have h2len := hres.length_le
                    omega)
                refine Or.inl ?_
                rw [projectTrace_concat_notMem t₁' l₁ p hl₁]
                by_cases hl₂ : p ∈ pn l₂
                · rw [projectTrace_concat_mem t₂' l₂ p hl₂, ← hE]
                  exact List.prefix_append _ _
                · rw [projectTrace_concat_notMem t₂' l₂ p hl₂, ← hE]
            · -- the witness already works for the full traces
              obtain ⟨q, x₁, x₂, m₁, m₂, hx₁, hx₂, hm, hproj⟩ := hres
              refine Or.inr (Or.inr ⟨q, x₁, x₂, m₁, m₂, hx₁, ?_, hm, hproj⟩)
              exact hx₂.trans (List.prefix_append t₂' [l₂])
        · -- `ProjectTrace t₂' p <+: ProjectTrace t₁' p` (symmetric)
          by_cases hEq : ProjectTrace (pn := pn) t₁' p
              = ProjectTrace (pn := pn) t₂' p
          · -- Equal prefix projections: the final labels decide.
            by_cases hl₁ : p ∈ pn l₁
            · by_cases hl₂ : p ∈ pn l₂
              · by_cases hll : l₁ = l₂
                · subst hll
                  refine Or.inl ?_
                  rw [projectTrace_concat_mem t₁' l₁ p hl₁,
                    projectTrace_concat_mem t₂' l₁ p hl₂, hEq]
                · exact Or.inr (Or.inr (core_branch h hpn₁ hpn₂ hpn₀ ht₁' ht₂'
                    hlast₁ hlast₂ hEq hl₁ hl₂ hll))
              · refine Or.inr (Or.inl ?_)
                rw [projectTrace_concat_mem t₁' l₁ p hl₁,
                  projectTrace_concat_notMem t₂' l₂ p hl₂, hEq]
                exact List.prefix_append _ _
            · refine Or.inl ?_
              by_cases hl₂ : p ∈ pn l₂
              · rw [projectTrace_concat_notMem t₁' l₁ p hl₁,
                  projectTrace_concat_mem t₂' l₂ p hl₂, hEq]
                exact List.prefix_append _ _
              · rw [projectTrace_concat_notMem t₁' l₁ p hl₁,
                  projectTrace_concat_notMem t₂' l₂ p hl₂, hEq]
          · -- `P(t₁')` properly extends `P(t₂')`: compare `t₁'` with `t₂`.
            obtain ⟨R, hR⟩ := h2
            have hRne : R ≠ [] := by
              intro h0
              exact hEq (by rw [← hR, h0, List.append_nil])
            have hlt : t₁'.length + (t₂' ++ [l₂]).length < n := by
              simp only [List.length_append, List.length_singleton] at hn ⊢
              omega
            rcases ihp (t₁'.length + (t₂' ++ [l₂]).length) hlt
              (s := s) (s₁ := u₁) (s₂ := s₂) ht₁' ht₂ rfl
              with hres | hres | hres
            · -- `P(t₁') <+: P(t₂)`: then `R = [l₂]`.
              by_cases hl₂ : p ∈ pn l₂
              · rw [projectTrace_concat_mem t₂' l₂ p hl₂] at hres
                rw [← hR] at hres
                have hRle : R <+: [l₂] := prefix_cancel_left hres
                have hReq : R = [l₂] := eq_of_prefix_singleton hRne hRle
                refine Or.inr (Or.inl ?_)
                rw [projectTrace_concat_mem t₂' l₂ p hl₂]
                by_cases hl₁ : p ∈ pn l₁
                · rw [projectTrace_concat_mem t₁' l₁ p hl₁, ← hR, hReq]
                  exact List.prefix_append _ _
                · rw [projectTrace_concat_notMem t₁' l₁ p hl₁, ← hR, hReq]
              · rw [projectTrace_concat_notMem t₂' l₂ p hl₂] at hres
                rw [← hR] at hres
                exfalso
                exact hRne (List.eq_nil_of_prefix_nil (prefix_cancel_left (by simpa using hres)))
            · -- `P(t₂) <+: P(t₁')`, hence also a prefix of `P(t₁)`
              refine Or.inr (Or.inl (hres.trans ?_))
              by_cases hl₁ : p ∈ pn l₁
              · rw [projectTrace_concat_mem t₁' l₁ p hl₁]
                exact List.prefix_append _ _
              · rw [projectTrace_concat_notMem t₁' l₁ p hl₁]
            · -- the witness already works for the full traces
              obtain ⟨q, x₁, x₂, m₁, m₂, hx₁, hx₂, hm, hproj⟩ := hres
              refine Or.inr (Or.inr ⟨q, x₁, x₂, m₁, m₂,
                hx₁.trans (List.prefix_append t₁' [l₁]), hx₂, hm, hproj⟩)
        · -- the witness already works for the full traces
          obtain ⟨q, x₁, x₂, m₁, m₂, hx₁, hx₂, hm, hproj⟩ := h3
          exact Or.inr (Or.inr ⟨q, x₁, x₂, m₁, m₂,
            hx₁.trans (List.prefix_append t₁' [l₁]),
            hx₂.trans (List.prefix_append t₂' [l₂]), hm, hproj⟩)

omit [DecidableEq Pid] in
/-- Two distinct labels enabled at the same state and both observed by `p` must be a
matching pair: independence would force disjoint process sets, yet both contain `p`. -/
private theorem obs_match
    (h : Smurf lts I B) (hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂))
    {s s₁ s₂ : State} {a b : Label} (hab : a ≠ b)
    (ha : p ∈ pn a) (hb : p ∈ pn b)
    (hta : lts.Tr s a s₁) (htb : lts.Tr s b s₂) : B.matching a b := by
  rcases h.u s s₁ s₂ a b hab ⟨hta, htb⟩ with hind | hm
  · exact absurd hb (Finset.disjoint_left.mp (hpn₁ a b hind) ha)
  · exact hm
end Helpers

theorem ifSmurfThenTraces {pn : Label → Finset Pid} {lts : LTS State Label}
    {I : Label → Label → Prop} [Independence I] {B : Branching Label}
    {hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂)}
    {hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → (pn l₁) = (pn l₂)}
    {hpn₀ : ∀ l, (pn l).Nonempty}
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
  -- See scripts/SmurfProofSketch.md for the full proof sketch.
  intro s t₁ t₂ p ht
  obtain ⟨h₁, h₂⟩ := ht
  obtain ⟨s₁, hm₁⟩ := h₁
  obtain ⟨s₂, hm₂⟩ := h₂
  exact core h hpn₁ hpn₂ hpn₀ hm₁ hm₂





section Helpers2

-- a label can commute past an independent trace
private lemma label_commute_trace
    {lts : LTS State Label}
    {I : Label → Label → Prop}
    [Independence I]
    {B : Branching Label}
    {s s' s'' : State}
    {t : List Label}
    {l : Label}
    (h : Smurf lts I B)
    (ht : lts.MTr s t s')
    (hl : lts.Tr s' l s'')
    (hind : ∀ m ∈ t, I m l)
  : ∃ sl, lts.Tr s l sl ∧ lts.MTr sl t s''
  := by
    -- structural induction on t, generalising the start and end states
    induction t generalizing s s' with
    | nil =>
      cases ht
      exact ⟨s'', hl, .refl⟩
    | cons a t' ih =>
      obtain ⟨s₁, ha, ht'⟩ := LTS.MTr.cons_iff.mp ht
      have ha_ind : I a l := hind a (by simp)
      have ht'_ind : ∀ m ∈ t', I m l := fun m hm => hind m (by simp [hm])
      -- the tail can be run after `l`
      obtain ⟨sl, hl₁, hmtr⟩ := ih ht' hl ht'_ind
      -- backward concurrency: `l` was already enabled before `a`
      obtain ⟨s₂, hl₂⟩ := h.r s sl a l ⟨ha_ind, .stepL ha (.stepL hl₁ .refl)⟩
      -- the forward diamond and determinism identify `sl` with the diamond's corner
      obtain ⟨s₃, hl₃, ha₃⟩ := h.f s s₁ s₂ a l ⟨ha_ind, ha, hl₂⟩
      obtain rfl : sl = s₃ := h.d s₁ sl s₃ l hl₁ hl₃
      exact ⟨s₂, hl₂, .stepL ha₃ hmtr⟩

-- two traces from the same state will either fully commute or result in a match at some point
private lemma commute_or_match
    {pn : Label → Finset Pid}
    {lts : LTS State Label}
    {I : Label → Label → Prop}
    [Independence I]
    {B : Branching Label}
    (hpn₀ : ∀ l, (pn l).Nonempty)
    (hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂))
    (hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → (pn l₁) = (pn l₂))
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
      have hlen : t₁'.length + t₂'.length < n := by grind
      rcases ih (t₁'.length + t₂'.length) hlen s s₁' s₂' t₁' t₂' ht₁' ht₂' rfl with hind | hmatch
      · -- everything commutes
        -- TODO: a₀, b₀ not part of IH, need something to commute them back or prove correctness in spite
        -- check whether a₀ and b₀ are equal
        -- by_cases heq : a₀ = b₀
        -- · apply Or.inr
          -- exists t₁', t₂', a₀, b₀, [], [], rfl, rfl
          -- sorry
        -- if a₀ and b₀ are equal, then witness
        -- otherwise, helper lemma to commute both a₀ and b₀ back to s
        -- apply Smurf.u to a₀ and b₀ in s
        -- if the two are independent, then everything is independent
        -- otherwise the two match, which is a witness
        sorry
      · -- match or equality found: also holds for t₁, t₂
        obtain ⟨u₁, u₂, a, b, v₁, v₂, _, _, _, _, _, _⟩ := hmatch
        apply Or.inr
        have _ : t₁' ++ [a₀] = u₁ ++ a :: (v₁ ++ [a₀]) := by grind
        have _ : t₂' ++ [b₀] = u₂ ++ b :: (v₂ ++ [b₀]) := by grind
        exists u₁, u₂, a, b, v₁ ++ [a₀], v₂ ++ [b₀]

-- lemma to cover the two (symmetric) prefix cases from the main theorem
private lemma prefixCase
    -- all the parameters from the main theorem
    {pn : Label → Finset Pid}
    {lts : LTS State Label}
    {I : Label → Label → Prop}
    [Independence I]
    {B : Branching Label}
    (hpn₀ : ∀ l, (pn l).Nonempty)
    (hpn₁ : ∀ l₁ l₂, I l₁ l₂ → Disjoint (pn l₁) (pn l₂))
    (hpn₂ : ∀ l₁ l₂, B.matching l₁ l₂ → (pn l₁) = (pn l₂))
    (h : Smurf lts I B)
    -- plus a concrete state and process, two traces and tails
    -- one of the two projections of the traces is a prefix of the other
    (s : State)
    (p : Pid)
    (t₁ t₂ : List Label)
    (l₁ l₂ : Label)
    (ht₁ : lts.MTr s t₁ s₁) (ht₂ : lts.MTr s t₂ s₂)
    (hl₁ : lts.Tr s₁ l₁ s₁') (hl₂ : lts.Tr s₂ l₂ s₂')
    (hprefix : ProjectTrace (pn := pn) t₁ p <+: ProjectTrace (pn := pn) t₂ p)
  : ProjectTrace (pn := pn) (t₁ ++ [l₁]) p <+: ProjectTrace (pn := pn) (t₂ ++ [l₂]) p
  ∨
  ProjectTrace (pn := pn) (t₂ ++ [l₂]) p <+: ProjectTrace (pn := pn) (t₁ ++ [l₁]) p
  ∨
  (
    ∃ (q : Pid) (t₁' t₂' : List Label) (m₁ m₂ : Label),
      (
        t₁' ++ [m₁] <+: t₁
        ∧ t₂' ++ [m₂] <+: t₂
        ∧ B.matching m₁ m₂
        ∧ ProjectTrace (pn := pn) t₁' q = ProjectTrace (pn := pn) t₂' q
      )
  )
  := by
    -- check whether p ∈ pn l₁
    by_cases hp₁ : p ∈ pn l₁
    · -- p ∈ pn l₁
      -- t₁ and t₂ have a longest prefix t₀
      sorry
    · -- p ∉ pn l₁
      -- then projection of t₁ trivially prefixes that of t₂
      apply Or.inl
      have _ : ProjectTrace (pn := pn) (t₁ ++ [l₁]) p = ProjectTrace (pn := pn) t₁ p := by
        simpa [ProjectTrace]
      have _ : ProjectTrace (pn := pn) t₂ p <+: ProjectTrace (pn := pn) (t₂ ++ [l₂]) p := by
        simp [ProjectTrace]
      grind

end Helpers2

theorem ifSmurfThenTracesLuc
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
  intro s t₁ t₂ p ⟨⟨s₁, ht₁⟩, ⟨s₂, ht₂⟩⟩
  induction hn : t₁.length + t₂.length using Nat.strong_induction_on generalizing
      s t₁ t₂ s₁ s₂ with
  | _ n ih =>
  -- check emptiness of t₁
  rcases List.eq_nil_or_concat t₁ with rfl | ⟨t₁', l₁, rfl⟩
  · -- t₁ empty, projection trivially prefix of that of t₂
    apply Or.inl
    simp [ProjectTrace]
  -- t₁ nonempty
  -- check emptiness of t₂
  rcases List.eq_nil_or_concat t₂ with rfl | ⟨t₂', l₂, rfl⟩
  · -- t₂ empty, projection trivially prefix of that of t₁
    apply Or.inr
    apply Or.inl
    simp [ProjectTrace]
  -- neither empty: t₁ = t₁' :: l₁, t₂ = t₂' :: l₂
  -- apply induction hypothesis to t₁' and t₂'
  obtain ⟨u₁, ht₁', hlast₁⟩ := mtr_split_last
    (l := t₁') (a := l₁) (by simpa using ht₁)
  obtain ⟨u₂, ht₂', hlast₂⟩ := mtr_split_last
    (l := t₂') (a := l₂) (by simpa using ht₂)
  simp only [List.concat_eq_append] at ht₁ ht₂ hn ⊢
  have hlen : t₁'.length + t₂'.length < n := by grind
  rcases ih (t₁'.length + t₂'.length) hlen
      (s₁ := u₁) (s₂ := u₂) ht₁' ht₂' rfl with h1 | h2 | h3
  · -- the projection of t₁' on p is a prefix of that of t₂
    -- outsource to helper function
    have hlem := prefixCase hpn₀ hpn₁ hpn₂ h s p t₁' t₂' l₁ l₂ ht₁' ht₂' hlast₁ hlast₂ h1
    rcases hlem with hlem₁ | hlem₂ | hlem₃
    · grind
    · grind
    · apply Or.inr
      apply Or.inr
      obtain ⟨q, x₁, x₂, m₁, m₂, hx₁, hx₂, hm, hp⟩ := hlem₃
      have _ : x₁ ++ [m₁] <+: t₁' ++ [l₁] := by grind
      have _ : x₂ ++ [m₂] <+: t₂' ++ [l₂] := by grind
      exists q, x₁, x₂, m₁, m₂
  · -- the projection of t₂' on p is a prefix of that of t₁
    -- case is symmetric to the previous case
    have hlem := prefixCase hpn₀ hpn₁ hpn₂ h s p t₂' t₁' l₂ l₁ ht₂' ht₁' hlast₂ hlast₁ h2
    rcases hlem with hlem₁ | hlem₂ | hlem₃
    · grind
    · grind
    · apply Or.inr
      apply Or.inr
      obtain ⟨q, x₂, x₁, m₂, m₁, hx₂, hx₁, hm, hp⟩ := hlem₃
      have _ : x₁ ++ [m₁] <+: t₁' ++ [l₁] := by grind
      have _ : x₂ ++ [m₂] <+: t₂' ++ [l₂] := by grind
      have _ : B.matching m₁ m₂ := by
        exact Std.Symm.symm (r := B.matching) (a := m₂) (b := m₁) hm
      have _ : ProjectTrace (pn := pn) x₁ q = ProjectTrace (pn := pn) x₂ q := by grind
      exists q, x₁, x₂, m₁, m₂
  · -- t₁' and t₂' have a divergence witness
    -- this witness then also holds for t₁ and t₂
    obtain ⟨q, x₁, x₂, m₁, m₂, hx₁, hx₂, hm, hproj⟩ := h3
    apply Or.inr
    apply Or.inr
    exact ⟨q, x₁, x₂, m₁, m₂,
      hx₁.trans (List.prefix_append t₁' [l₁]),
      hx₂.trans (List.prefix_append t₂' [l₂]),
      hm, hproj⟩

end Cslib.Concurrency
