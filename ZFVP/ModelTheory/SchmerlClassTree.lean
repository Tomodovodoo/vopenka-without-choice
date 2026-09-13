import ZFVP.ModelTheory.SchmerlDefinableBranchBound
import ZFVP.SetTheory.Rank

/-! Keisler's class tree in an arbitrary (possibly ill-founded) model of ZF.
Its rank order is the model's external order of ordinals. This supplies the
actual ranked tree to which cofinal-rank specialization is applied.
-/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

variable (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A node records a subset of one cumulative-hierarchy level. -/
structure ClassTreeNode where
  level : SetTheory.Ordinal V
  slice : V
  subset : slice ⊆ hierarchy level.val

namespace ClassTreeNode

variable {V}

@[ext] theorem ext {a b : ClassTreeNode V} (hlevel : a.level = b.level)
    (hsection : a.slice = b.slice) : a = b := by
  cases a
  cases b
  cases hlevel
  cases hsection
  rfl

instance : LE (ClassTreeNode V) where
  le a b := a.level ≤ b.level ∧ a.slice = b.slice ∩ hierarchy a.level.val

theorem le_def (a b : ClassTreeNode V) :
    a ≤ b ↔ a.level ≤ b.level ∧ a.slice = b.slice ∩ hierarchy a.level.val := Iff.rfl

theorem le_refl_node (a : ClassTreeNode V) : a ≤ a := by
  refine ⟨le_rfl, ?_⟩
  apply mem_ext
  intro x
  rw [mem_inter_iff]
  exact ⟨fun hx ↦ ⟨hx, a.subset x hx⟩, fun hx ↦ hx.1⟩

theorem le_of_common_above {a b c : ClassTreeNode V} (hac : a ≤ c) (hbc : b ≤ c)
    (hab : a.level ≤ b.level) : a ≤ b := by
  refine ⟨hab, ?_⟩
  apply mem_ext
  intro x
  rw [hac.2, hbc.2]
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨hx, hxa⟩
    exact ⟨⟨hx, hierarchy_mono hab x hxa⟩, hxa⟩
  · rintro ⟨⟨hx, _⟩, hxa⟩
    exact ⟨hx, hxa⟩

instance : PartialOrder (ClassTreeNode V) where
  le_refl := le_refl_node
  le_trans a b c hab hbc := by
    refine ⟨hab.1.trans hbc.1, ?_⟩
    apply mem_ext
    intro x
    rw [hab.2, hbc.2]
    simp only [mem_inter_iff]
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩,
      fun h ↦ ⟨⟨h.1, hierarchy_mono hab.1 x h.2⟩, h.2⟩⟩
  le_antisymm a b hab hba := by
    have hl : a.level = b.level := le_antisymm hab.1 hba.1
    apply ext hl
    rw [hab.2]
    apply mem_ext
    intro x
    rw [mem_inter_iff]
    exact ⟨fun h ↦ h.1, fun hx ↦ ⟨hx, hl.symm ▸ b.subset x hx⟩⟩

theorem tree : IsTreeOrder (ClassTreeNode V) := by
  intro a b c hac hbc
  rcases le_total a.level b.level with hab | hba
  · exact Or.inl (le_of_common_above hac hbc hab)
  · exact Or.inr (le_of_common_above hbc hac hba)

theorem level_strictMono : StrictMono (ClassTreeNode.level (V := V)) := by
  intro a b hab
  refine lt_of_le_of_ne hab.le.1 ?_
  intro hl
  apply hab.ne
  apply le_antisymm hab.le
  exact le_of_common_above (le_refl_node b) hab.le hl.ge

/-- Restrict a node's section to an earlier ordinal level. -/
noncomputable def atLevel (b : ClassTreeNode V) (α : SetTheory.Ordinal V) : ClassTreeNode V where
  level := α
  slice := b.slice ∩ hierarchy α.val
  subset := fun _ hx ↦ (mem_inter_iff.mp hx).2

theorem atLevel_le (b : ClassTreeNode V) {α : SetTheory.Ordinal V} (hα : α ≤ b.level) :
    b.atLevel α ≤ b := ⟨hα, rfl⟩

/-- The actual class tree is ranked by the model's ordinal order. -/
noncomputable def rankedTree : RankedTree (ClassTreeNode V) (SetTheory.Ordinal V) where
  tree := tree
  rank := ClassTreeNode.level
  strictMono := level_strictMono
  onto α := ⟨⟨α, ∅, empty_subset _⟩, rfl⟩
  predecessor b α hα := ⟨b.atLevel α,
    lt_of_le_of_ne (b.atLevel_le hα.le) (fun heq ↦ hα.ne (congrArg ClassTreeNode.level heq)), rfl⟩

/-- Code a node by its Kuratowski pair inside the model. -/
noncomputable def code (a : ClassTreeNode V) : V := ⟨a.slice, a.level.val⟩ₖ

theorem code_injective : Function.Injective (code (V := V)) := by
  intro a b hab
  have hs : a.slice = b.slice := by simpa only [code, kpair.π₁_kpair] using congrArg kpair.π₁ hab
  have hl : a.level.val = b.level.val := by simpa only [code, kpair.π₂_kpair] using congrArg kpair.π₂ hab
  exact ext (SetTheory.Ordinal.ext hl) hs

noncomputable def codeEmbedding : ClassTreeNode V ↪ V := ⟨code, code_injective⟩

theorem slice_subset_of_le {a b : ClassTreeNode V} (hab : a ≤ b) : a.slice ⊆ b.slice := by
  intro x hx
  rw [hab.2] at hx
  exact (mem_inter_iff.mp hx).1

end ClassTreeNode

/-- Amenability: every restriction of the class to an internal set has an internal code. -/
def IsAmenableClass (X : V → Prop) : Prop :=
  ∀ a : V, ∃ b : V, ∀ x, x ∈ b ↔ x ∈ a ∧ X x

variable {V}

/-- The class recovered by taking the union of a branch's sections. -/
def classOfBranch (B : Set (ClassTreeNode V)) (x : V) : Prop :=
  ∃ a ∈ B, x ∈ a.slice

theorem classOfBranch_section {B : Set (ClassTreeNode V)}
    (hB : (ClassTreeNode.rankedTree (V := V)).IsBranch B)
    {a : ClassTreeNode V} (ha : a ∈ B) {x : V} (hx : x ∈ hierarchy a.level.val) :
    classOfBranch B x ↔ x ∈ a.slice := by
  constructor
  · rintro ⟨b, hb, hxb⟩
    rcases hB.1.total ha hb with hab | hba
    · rw [hab.2]
      exact mem_inter_iff.mpr ⟨hxb, hx⟩
    · exact ClassTreeNode.slice_subset_of_le hba x hxb
  · intro hxa
    exact ⟨a, ha, hxa⟩

/-- Every cofinal branch of the class tree determines an amenable class. -/
theorem classOfBranch_amenable {B : Set (ClassTreeNode V)}
    (hB : (ClassTreeNode.rankedTree (V := V)).IsBranch B) :
    IsAmenableClass V (classOfBranch B) := by
  intro s
  obtain ⟨α, hα, hsα⟩ := hierarchy_bound_exists s
  obtain ⟨a, ha, hlevel⟩ := hB.2 ⟨α, hα⟩
  have hval : a.level.val = α := congrArg SetTheory.Ordinal.val hlevel
  refine ⟨s ∩ a.slice, fun x ↦ ?_⟩
  rw [mem_inter_iff]
  constructor
  · rintro ⟨hxs, hxa⟩
    exact ⟨hxs, a, ha, hxa⟩
  · rintro ⟨hxs, hX⟩
    refine ⟨hxs, (classOfBranch_section hB ha ?_).mp hX⟩
    rw [hval]
    exact hsα x hxs

/-- The branch associated to a class consists of all its bounded sections. -/
def branchOfClass (X : V → Prop) : Set (ClassTreeNode V) :=
  {a | ∀ x, x ∈ a.slice ↔ x ∈ hierarchy a.level.val ∧ X x}

theorem branchOfClass_le {X : V → Prop} {a b : ClassTreeNode V}
    (ha : a ∈ branchOfClass X) (hb : b ∈ branchOfClass X) (hab : a.level ≤ b.level) :
    a ≤ b := by
  refine ⟨hab, ?_⟩
  apply mem_ext
  intro x
  rw [mem_inter_iff, ha x, hb x]
  exact ⟨fun h ↦ ⟨⟨hierarchy_mono hab x h.1, h.2⟩, h.1⟩,
    fun h ↦ ⟨h.2, h.1.2⟩⟩

/-- Amenable classes give cofinal branches of Keisler's tree. -/
theorem branchOfClass_isBranch {X : V → Prop} (hX : IsAmenableClass V X) :
    (ClassTreeNode.rankedTree (V := V)).IsBranch (branchOfClass X) := by
  refine ⟨?_, ?_⟩
  · intro a ha b hb _
    rcases le_total a.level b.level with hab | hba
    · exact Or.inl (branchOfClass_le ha hb hab)
    · exact Or.inr (branchOfClass_le hb ha hba)
  · intro α
    obtain ⟨s, hs⟩ := hX (hierarchy α.val)
    exact ⟨⟨α, s, fun x hx ↦ ((hs x).mp hx).1⟩, hs, rfl⟩

theorem mem_branchOfClass_classOfBranch {B : Set (ClassTreeNode V)}
    (hB : (ClassTreeNode.rankedTree (V := V)).IsBranch B) {a : ClassTreeNode V}
    (ha : a ∈ B) : a ∈ branchOfClass (classOfBranch B) := by
  intro x
  constructor
  · intro hx
    exact ⟨a.subset x hx, a, ha, hx⟩
  · rintro ⟨hx, hclass⟩
    exact (classOfBranch_section hB ha hx).mp hclass

/-- Passing from a branch to its class and back recovers the branch. -/
theorem branchOfClass_classOfBranch {B : Set (ClassTreeNode V)}
    (hB : (ClassTreeNode.rankedTree (V := V)).IsBranch B) :
    branchOfClass (classOfBranch B) = B := by
  apply Set.Subset.antisymm
  · intro a ha
    obtain ⟨b, hb, hlevel⟩ := hB.2 a.level
    change b.level = a.level at hlevel
    have hbclass := mem_branchOfClass_classOfBranch hB hb
    have heq : a = b := by
      apply ClassTreeNode.ext hlevel.symm
      apply mem_ext
      intro x
      rw [ha x, hbclass x, hlevel]
    exact heq ▸ hb
  · exact fun _ ha ↦ mem_branchOfClass_classOfBranch hB ha

/-- Passing from an amenable class to its branch and back recovers the class. -/
theorem classOfBranch_branchOfClass {X : V → Prop} (hX : IsAmenableClass V X) :
    classOfBranch (branchOfClass X) = X := by
  funext x
  apply propext
  constructor
  · rintro ⟨a, ha, hxa⟩
    exact ((ha x).mp hxa).2
  · intro hx
    obtain ⟨α, hα, hxα⟩ := hierarchy_bound_exists x
    let : IsOrdinal α := hα
    have hxstage : x ∈ hierarchy (succ α) := by
      rw [hierarchy_succ, mem_power_iff]
      exact hxα
    obtain ⟨a, ha, hlevel⟩ := (branchOfClass_isBranch hX).2 (IsOrdinal.toOrdinal (succ α))
    have hval : a.level.val = succ α := congrArg SetTheory.Ordinal.val hlevel
    exact ⟨a, ha, (ha x).mpr ⟨hval.symm ▸ hxstage, hx⟩⟩

/-- The image of a definable class branch is definable in the original model. -/
theorem branchOfClass_image_definable {X : V → Prop} (hX : ℒₛₑₜ-predicate[V] X) :
    ℒₛₑₜ-predicate[V] (fun p ↦ p ∈ ClassTreeNode.code '' branchOfClass X) := by
  let : ℒₛₑₜ-predicate[V] X := hX
  have hd : ℒₛₑₜ-predicate[V] (fun p ↦ ∃ s α, IsOrdinal α ∧ s ⊆ hierarchy α ∧
      p = ⟨s, α⟩ₖ ∧ ∀ x, x ∈ s ↔ x ∈ hierarchy α ∧ X x) := by definability
  apply Language.DefinablePred.of_iff hd
  intro p
  constructor
  · rintro ⟨a, ha, hap⟩
    exact ⟨a.slice, a.level.val, a.level.ordinal, a.subset, hap.symm, ha⟩
  · rintro ⟨s, α, hα, hs, hp, hclass⟩
    exact ⟨⟨⟨α, hα⟩, s, hs⟩, hclass, hp.symm⟩

/-- Rather classlessness makes every branch of the actual class tree definable. -/
theorem classTree_branches_definable
    (hclasses : ∀ X : V → Prop, IsAmenableClass V X → ℒₛₑₜ-predicate[V] X)
    {B : Set (ClassTreeNode V)} (hB : (ClassTreeNode.rankedTree (V := V)).IsBranch B) :
    ℒₛₑₜ-predicate[V] (fun p ↦ p ∈ ClassTreeNode.code '' B) := by
  have hdef := branchOfClass_image_definable (hclasses _ (classOfBranch_amenable hB))
  rwa [branchOfClass_classOfBranch hB] at hdef

/-- The class tree of a rather classless aleph-one model meets the branch-cardinality
hypothesis of the corrected Schmerl specialization forcing. -/
theorem classTree_branch_bound
    (hclasses : ∀ X : V → Prop, IsAmenableClass V X → ℒₛₑₜ-predicate[V] X)
    (hcard : Cardinal.mk V ≤ Cardinal.aleph 1) :
    Cardinal.mk {B : Set (ClassTreeNode V) //
      (ClassTreeNode.rankedTree (V := V)).IsBranch B} ≤ Cardinal.aleph 1 :=
  cardinal_branches_le_aleph_one ClassTreeNode.rankedTree ClassTreeNode.codeEmbedding
    (fun _ hB ↦ classTree_branches_definable hclasses hB) hcard

/-- Definability of a coded branch transfers to its union class. -/
theorem classOfBranch_definable {B : Set (ClassTreeNode V)}
    (hB : ℒₛₑₜ-predicate[V] (fun p ↦ p ∈ ClassTreeNode.code '' B)) :
    ℒₛₑₜ-predicate[V] (classOfBranch B) := by
  let P : V → Prop := fun p ↦ p ∈ ClassTreeNode.code '' B
  let : ℒₛₑₜ-predicate[V] P := hB
  have hd : ℒₛₑₜ-predicate[V] (fun x ↦ ∃ p, P p ∧ x ∈ kpair.π₁ p) := by
    apply Language.Definable.exs
    apply Language.Definable.and
    · exact Language.DefinablePred.comp (P := P) (by definability)
    · definability
  apply Language.DefinablePred.of_iff hd
  intro x
  constructor
  · rintro ⟨a, ha, hx⟩
    exact ⟨ClassTreeNode.code a, ⟨a, ha, rfl⟩, by simpa only [ClassTreeNode.code, kpair.π₁_kpair]⟩
  · rintro ⟨p, ⟨a, ha, rfl⟩, hx⟩
    exact ⟨a, ha, by simpa only [ClassTreeNode.code, kpair.π₁_kpair] using hx⟩

/-- Keisler's equivalence for the actual class tree, including both directions. -/
theorem ratherClassless_iff_classTree_branches_definable :
    (∀ X : V → Prop, IsAmenableClass V X → ℒₛₑₜ-predicate[V] X) ↔
      ∀ B : Set (ClassTreeNode V), (ClassTreeNode.rankedTree (V := V)).IsBranch B →
        ℒₛₑₜ-predicate[V] (fun p ↦ p ∈ ClassTreeNode.code '' B) := by
  constructor
  · exact fun h _ hB ↦ classTree_branches_definable h hB
  · intro h X hX
    have hd := classOfBranch_definable (h _ (branchOfClass_isBranch hX))
    rwa [classOfBranch_branchOfClass hX] at hd

end ZFVP.Schmerl
