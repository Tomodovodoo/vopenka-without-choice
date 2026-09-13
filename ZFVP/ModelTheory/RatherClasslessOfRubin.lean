import ZFVP.ModelTheory.MaximallyCompatibleFilters
import ZFVP.SetTheory.Rank

/-! Enayat's Remark 5.14 from "Models of set theory: extensions and dead ends": a model satisfying
the two clauses of his Definition 5.13 is rather classless.

The argument runs through Keisler's tree of classes. A node is a Kuratowski pair `⟨s, α⟩ₖ` with `α`
an ordinal and `s ⊆ V_α`, and `⟨s, α⟩ₖ` lies below `⟨t, β⟩ₖ` when `α ⊆ β` and `s = t ∩ V_α`. Both
the carrier and the order are definable without parameters. A class `X` of the model gives a
branch: the nodes `⟨X ∩ V_α, α⟩ₖ`. That branch is a maximally compatible filter of the tree, hence
also a maximal filter in the inclusion sense, and clause (a) of
Definition 5.13, applied to the poset of ordinals, produces a cofinal `ω₁`-chain inside it. Clause
(b) then makes the branch definable, and `X` is recovered from it by
`X x ↔ ∃ p, branch p ∧ x ∈ kpair.π₁ p`.

Enayat prints the tree with the strict order; the non-strict order is used here, which is what
`IsPartialOrderOn` asks for. Clause (b) is taken in the form that concludes definability of the
maximal filter rather than codedness: a cofinal `ω₁`-chain of nodes of the tree is a proper class,
so it cannot be coded, and codedness would make the hypothesis vacuous for this application. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The tree of classes -/

/-- A node of the tree: a Kuratowski pair `⟨s, α⟩ₖ` with `α` an ordinal and `s ⊆ V_α`. -/
def classTree (p : V) : Prop :=
  ∃ α, IsOrdinal α ∧ p = ⟨kpair.π₁ p, α⟩ₖ ∧ kpair.π₁ p ⊆ hierarchy α

/-- The tree order: `⟨s, α⟩ₖ ≤ ⟨t, β⟩ₖ` when `α ⊆ β` and `s` is the part of `t` of rank below
`α`. -/
def classLe (p q : V) : Prop :=
  classTree p ∧ classTree q ∧ kpair.π₂ p ⊆ kpair.π₂ q ∧
    kpair.π₁ p = kpair.π₁ q ∩ hierarchy (kpair.π₂ p)

instance classTree_definable : ℒₛₑₜ-predicate[V] classTree := by
  unfold classTree
  definability

instance classLe_definable : ℒₛₑₜ-relation[V] (classLe (V := V)) := by
  unfold classLe
  definability

theorem classTree_kpair {s α : V} (hα : IsOrdinal α) (hs : s ⊆ hierarchy α) :
    classTree (⟨s, α⟩ₖ : V) :=
  ⟨α, hα, by simp, by simpa using hs⟩

theorem classTree.snd_ordinal {p : V} (h : classTree p) : IsOrdinal (kpair.π₂ p) := by
  obtain ⟨α, hα, hp, _⟩ := h
  have : kpair.π₂ p = α := by rw [hp]; simp
  rw [this]; exact hα

theorem classTree.eta {p : V} (h : classTree p) : (⟨kpair.π₁ p, kpair.π₂ p⟩ₖ : V) = p := by
  obtain ⟨α, _, hp, _⟩ := h
  have h2 : kpair.π₂ p = α := by rw [hp]; simp
  rw [h2]; exact hp.symm

theorem classTree.fst_subset {p : V} (h : classTree p) :
    kpair.π₁ p ⊆ hierarchy (kpair.π₂ p) := by
  obtain ⟨α, _, hp, hsub⟩ := h
  have h2 : kpair.π₂ p = α := by rw [hp]; simp
  rw [h2]; exact hsub

/-- The tree order is a partial order on the nodes of the tree. -/
theorem isPartialOrderOn_classTree : IsPartialOrderOn (classTree (V := V)) classLe := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    refine ⟨hp, hp, subset_refl _, ?_⟩
    apply mem_ext
    intro x
    simp only [mem_inter_iff]
    exact ⟨fun hx ↦ ⟨hx, hp.fst_subset x hx⟩, fun h ↦ h.1⟩
  · rintro p q r hp hq hr ⟨-, -, hpq, hpq'⟩ ⟨-, -, hqr, hqr'⟩
    refine ⟨hp, hr, subset_trans hpq hqr, ?_⟩
    have := hp.snd_ordinal
    have := hq.snd_ordinal
    apply mem_ext
    intro x
    rw [hpq', hqr']
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨⟨hx, -⟩, hx2⟩
      exact ⟨hx, hx2⟩
    · rintro ⟨hx, hx2⟩
      exact ⟨⟨hx, hierarchy_mono hpq x hx2⟩, hx2⟩
  · rintro p q hp hq ⟨-, -, hpq, hpq'⟩ ⟨-, -, hqp, -⟩
    have hsnd : kpair.π₂ p = kpair.π₂ q := subset_antisymm hpq hqp
    have hfst : kpair.π₁ p = kpair.π₁ q := by
      rw [hpq']
      apply mem_ext
      intro x
      simp only [mem_inter_iff, and_iff_left_iff_imp]
      intro hx
      rw [hsnd]
      exact hq.fst_subset x hx
    rw [← hp.eta, ← hq.eta, hfst, hsnd]

/-! ### The poset of ordinals -/

/-- The ordinals under inclusion form a directed poset with no maximum element. Private, because
`ZFVP.ModelTheory.RubinDefinableFilters` states the same fact under the same name and files that
import both modules would see a clash. -/
private theorem isDirectedNoMaxOn_isOrdinal :
    IsDirectedNoMaxOn (IsOrdinal (V := V)) (· ⊆ ·) := by
  refine ⟨⟨∅, inferInstance⟩, ?_, ?_⟩
  · intro α β hα hβ
    have := hα
    have := hβ
    rcases IsOrdinal.subset_or_supset (α := α) (β := β) with h | h
    · exact ⟨β, hβ, h, subset_refl _⟩
    · exact ⟨α, hα, subset_refl _, h⟩
  · rintro ⟨m, hm, hmax⟩
    have := hm
    have h := hmax (succ m) inferInstance
    exact mem_irrefl m (h m (mem_succ_self m))

/-! ### The branch of a class -/

/-- The nodes of the tree that record initial segments of `X`. -/
def classBranch (X : V → Prop) (p : V) : Prop :=
  classTree p ∧ ∀ x, x ∈ kpair.π₁ p ↔ (x ∈ hierarchy (kpair.π₂ p) ∧ X x)

/-- The node of the branch of `X` at the ordinal `α`, using that `X` is a class. -/
noncomputable def classBranchNode {X : V → Prop} (hX : IsClass V X) (α : V) : V :=
  ⟨Classical.choose (hX (hierarchy α)), α⟩ₖ

theorem mem_classBranchNode_fst {X : V → Prop} (hX : IsClass V X) (α x : V) :
    x ∈ kpair.π₁ (classBranchNode hX α) ↔ (x ∈ hierarchy α ∧ X x) := by
  simp only [classBranchNode, kpair.π₁_kpair]
  exact Classical.choose_spec (hX (hierarchy α)) x

@[simp] theorem classBranchNode_snd {X : V → Prop} (hX : IsClass V X) (α : V) :
    kpair.π₂ (classBranchNode hX α) = α := by
  simp [classBranchNode]

theorem classBranch_classBranchNode {X : V → Prop} (hX : IsClass V X) {α : V}
    (hα : IsOrdinal α) : classBranch X (classBranchNode hX α) := by
  have hsub : Classical.choose (hX (hierarchy α)) ⊆ hierarchy α := by
    intro x hx
    exact ((Classical.choose_spec (hX (hierarchy α)) x).mp hx).1
  refine ⟨classTree_kpair hα hsub, ?_⟩
  intro x
  rw [mem_classBranchNode_fst hX α x, classBranchNode_snd]

/-- Two nodes of the branch of `X` are comparable as soon as their ordinals are. -/
theorem classLe_of_classBranch {X : V → Prop} {p q : V} (hp : classBranch X p)
    (hq : classBranch X q) (h : kpair.π₂ p ⊆ kpair.π₂ q) : classLe p q := by
  have := hp.1.snd_ordinal
  have := hq.1.snd_ordinal
  refine ⟨hp.1, hq.1, h, ?_⟩
  apply mem_ext
  intro x
  rw [mem_inter_iff, hp.2 x, hq.2 x]
  constructor
  · rintro ⟨hx1, hx2⟩
    exact ⟨⟨hierarchy_mono h x hx1, hx2⟩, hx1⟩
  · rintro ⟨⟨-, hx2⟩, hx1⟩
    exact ⟨hx1, hx2⟩

/-- A node of the branch of `X` is the branch node at its own ordinal. -/
theorem eq_classBranchNode {X : V → Prop} (hX : IsClass V X) {p : V} (hp : classBranch X p) :
    p = classBranchNode hX (kpair.π₂ p) := by
  have hfst : kpair.π₁ p = kpair.π₁ (classBranchNode hX (kpair.π₂ p)) := by
    apply mem_ext
    intro x
    rw [hp.2 x, mem_classBranchNode_fst]
  have := hp.1.eta
  rw [← this, hfst, classBranchNode]
  simp [classBranchNode]

/-- The branch of a class is a filter of the tree. -/
theorem isFilterOn_classBranch {X : V → Prop} (_hX : IsClass V X) :
    IsFilterOn (classTree (V := V)) classLe (classBranch X) := by
  refine ⟨fun p hp ↦ hp.1, ?_⟩
  intro p q hp hq
  have := hp.1.snd_ordinal
  have := hq.1.snd_ordinal
  rcases IsOrdinal.subset_or_supset (α := kpair.π₂ p) (β := kpair.π₂ q) with h | h
  · exact ⟨q, hq, classLe_of_classBranch hp hq h, (isPartialOrderOn_classTree).1 q hq.1⟩
  · exact ⟨p, hp, (isPartialOrderOn_classTree).1 p hp.1, classLe_of_classBranch hq hp h⟩

/-- The branch of a class is a maximally compatible filter of the tree: a node `q` of the tree
compatible with every node of the branch is compatible with the branch node `b` at the same
ordinal, and a common upper bound of `q` and `b` forces `kpair.π₁ q = kpair.π₁ b`, so `q = b`. -/
theorem isMaximallyCompatibleOn_classBranch {X : V → Prop} (hX : IsClass V X) :
    IsMaximallyCompatibleOn (classTree (V := V)) classLe (classBranch X) := by
  refine ⟨isFilterOn_classBranch hX, ?_⟩
  intro q hqt hcomp
  have := hqt.snd_ordinal
  set b : V := classBranchNode hX (kpair.π₂ q) with hb
  have hbbranch : classBranch X b := classBranch_classBranchNode hX hqt.snd_ordinal
  obtain ⟨u, -, hbu, hqu⟩ := hcomp b hbbranch
  have hsnd : kpair.π₂ b = kpair.π₂ q := classBranchNode_snd hX _
  have hfst : kpair.π₁ q = kpair.π₁ b := by
    rw [hqu.2.2.2, hbu.2.2.2, hsnd]
  have : q = b := by
    rw [← hqt.eta, ← hbbranch.1.eta, hfst, hsnd]
  rw [this]
  exact hbbranch

/-- The branch of a class is a maximal filter of the tree. -/
theorem isMaximalFilterOn_classBranch {X : V → Prop} (hX : IsClass V X) :
    IsMaximalFilterOn (classTree (V := V)) classLe (classBranch X) :=
  (isMaximallyCompatibleOn_classBranch hX).isMaximalFilterOn

/-! ### The main step -/

/-- Enayat's Remark 5.14: the two clauses of his Definition 5.13 imply that the model is rather
classless. Clause (b) is taken with definability of the maximal filter as its conclusion. -/
theorem ratherClassless_of_rubin_clauses {V : Type*} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (ha : ∀ (P : V → Prop) (le : V → V → Prop), (ℒₛₑₜ-predicate[V] P) →
      (ℒₛₑₜ-relation[V] le) → IsPartialOrderOn P le → IsDirectedNoMaxOn P le →
        HasCofinalOmegaOneChainOn le P)
    (hb : ∀ (P : V → Prop) (le : V → V → Prop), (ℒₛₑₜ-predicate[V] P) →
      (ℒₛₑₜ-relation[V] le) → IsPartialOrderOn P le → ∀ F : V → Prop,
        IsMaximallyCompatibleOn P le F → HasCofinalOmegaOneChainOn le F → ℒₛₑₜ-predicate[V] F) :
    IsRatherClassless V := by
  intro X hX
  -- A cofinal `ω₁`-chain of ordinals, from clause (a) applied to the ordinals under inclusion.
  obtain ⟨α, hαord, hαmono, hαcof⟩ :=
    ha (IsOrdinal (V := V)) (· ⊆ ·) inferInstance subset_definable
      (isPartialOrderOn_subset _) isDirectedNoMaxOn_isOrdinal
  -- The corresponding chain of branch nodes is cofinal in the branch of `X`.
  have hchain : HasCofinalOmegaOneChainOn (classLe (V := V)) (classBranch X) := by
    refine ⟨fun i ↦ classBranchNode hX (α i), fun i ↦ classBranch_classBranchNode hX (hαord i),
      ?_, ?_⟩
    · intro i i' hii'
      obtain ⟨hle, hne⟩ := hαmono i i' hii'
      refine ⟨classLe_of_classBranch (classBranch_classBranchNode hX (hαord i))
        (classBranch_classBranchNode hX (hαord i')) (by simpa using hle), ?_⟩
      intro heq
      apply hne
      have := congrArg kpair.π₂ heq
      simpa using this
    · intro p hp
      have := hp.1.snd_ordinal
      obtain ⟨i, hi⟩ := hαcof (kpair.π₂ p) hp.1.snd_ordinal
      exact ⟨i, classLe_of_classBranch hp (classBranch_classBranchNode hX (hαord i))
        (by simpa using hi)⟩
  -- Clause (b) makes the branch definable.
  have hbranch : ℒₛₑₜ-predicate[V] (classBranch X) :=
    hb (classTree (V := V)) classLe inferInstance inferInstance isPartialOrderOn_classTree
      (classBranch X) (isMaximallyCompatibleOn_classBranch hX) hchain
  -- `X` is read off from the branch.
  have := hbranch
  have hdef : ℒₛₑₜ-predicate[V] (fun x ↦ ∃ p, classBranch X p ∧ x ∈ kpair.π₁ p) := by
    definability
  apply Language.Definable.of_iff hdef
  intro v
  constructor
  · intro hx
    refine ⟨classBranchNode hX (succ (rank (v 0))), classBranch_classBranchNode hX inferInstance,
      ?_⟩
    rw [mem_classBranchNode_fst]
    exact ⟨(mem_hierarchy_iff_rank_mem (v 0) (succ (rank (v 0)))).mpr (mem_succ_self _), hx⟩
  · rintro ⟨p, hp, hmem⟩
    exact ((hp.2 (v 0)).mp hmem).2

end ZFVP
