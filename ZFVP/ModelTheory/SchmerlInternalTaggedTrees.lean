import ZFVP.ModelTheory.SchmerlInternalBranchNames

/-! Actual tagged sums of internal ranked trees and their full cofinal branches. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def internalTaggedTree (J D : V) : V :=
  ⋃ˢ repl (fun j ↦ ({j} : V) ×ˢ (D ‘ j)) (by definability) J

theorem mem_internalTaggedTree (J D p : V) : p ∈ internalTaggedTree J D ↔
    ∃ j ∈ J, ∃ x ∈ D ‘ j, p = ⟨j, x⟩ₖ := by
  simp only [internalTaggedTree, mem_sUnion_iff, repl_spec]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, hp⟩
    obtain ⟨k, hk, x, hx, hp⟩ := mem_prod_iff.mp hp
    have he : k = j := mem_singleton_iff.mp hk
    subst k
    exact ⟨j, hj, x, hx, hp⟩
  · rintro ⟨j, hj, x, hx, rfl⟩
    exact ⟨_, ⟨j, hj, rfl⟩, kpair_mem_iff.mpr ⟨by simp, hx⟩⟩

theorem pair_mem_internalTaggedTree {J D j x : V} :
    ⟨j, x⟩ₖ ∈ internalTaggedTree J D ↔ j ∈ J ∧ x ∈ D ‘ j := by
  rw [mem_internalTaggedTree]
  constructor
  · rintro ⟨k, hk, y, hy, he⟩
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact ⟨hk, hy⟩
  · exact fun h ↦ ⟨j, h.1, x, h.2, rfl⟩

instance internalTaggedTree_definable : ℒₛₑₜ-function₂[V] internalTaggedTree := by
  have hh : ℒₛₑₜ-relation₃[V] (fun T J D ↦ ∀ p, p ∈ T ↔
      ∃ j ∈ J, ∃ x ∈ D ‘ j, p = ⟨j, x⟩ₖ) := by definability
  apply Language.Definable.of_iff hh
  intro v
  rw [mem_ext_iff]
  simp only [mem_internalTaggedTree]
  rfl

noncomputable def internalTaggedTreeOrder (J D S : V) : V :=
  {p ∈ internalTaggedTree J D ×ˢ internalTaggedTree J D ;
    kpair.π₁ (kpair.π₁ p) = kpair.π₁ (kpair.π₂ p) ∧
      ⟨kpair.π₂ (kpair.π₁ p), kpair.π₂ (kpair.π₂ p)⟩ₖ ∈ S ‘ (kpair.π₁ (kpair.π₁ p))}

theorem internalTaggedTreeOrder_subset (J D S : V) :
    internalTaggedTreeOrder J D S ⊆ internalTaggedTree J D ×ˢ internalTaggedTree J D :=
  fun _ hp ↦ (mem_sep_iff.mp hp).1

theorem pair_mem_internalTaggedTreeOrder {J D S j k x y : V} :
    ⟨⟨j, x⟩ₖ, ⟨k, y⟩ₖ⟩ₖ ∈ internalTaggedTreeOrder J D S ↔
      (j ∈ J ∧ x ∈ D ‘ j) ∧ (k ∈ J ∧ y ∈ D ‘ k) ∧ j = k ∧ ⟨x, y⟩ₖ ∈ S ‘ j := by
  simp only [internalTaggedTreeOrder, mem_sep_iff, kpair_mem_iff,
    pair_mem_internalTaggedTree, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

theorem same_pair_mem_internalTaggedTreeOrder {J D S j x y : V}
    (hj : j ∈ J) (hx : x ∈ D ‘ j) (hy : y ∈ D ‘ j) :
    ⟨⟨j, x⟩ₖ, ⟨j, y⟩ₖ⟩ₖ ∈ internalTaggedTreeOrder J D S ↔ ⟨x, y⟩ₖ ∈ S ‘ j := by
  simp only [pair_mem_internalTaggedTreeOrder, hj, hx, hy, true_and]

attribute [local irreducible] internalTaggedTree

instance internalTaggedTreeOrder_definable : ℒₛₑₜ-function₃[V] internalTaggedTreeOrder := by
  have hh : ℒₛₑₜ-relation₄[V] (fun R J D S ↦ ∀ p, p ∈ R ↔
      p ∈ internalTaggedTree J D ×ˢ internalTaggedTree J D ∧
      kpair.π₁ (kpair.π₁ p) = kpair.π₁ (kpair.π₂ p) ∧
      ⟨kpair.π₂ (kpair.π₁ p), kpair.π₂ (kpair.π₂ p)⟩ₖ ∈ S ‘ (kpair.π₁ (kpair.π₁ p))) := by definability
  apply Language.Definable.of_iff hh
  intro v
  rw [mem_ext_iff]
  simp only [internalTaggedTreeOrder, mem_sep_iff]
  rfl

noncomputable def internalTaggedTreeRank (J D r : V) : V :=
  definableGraph (internalTaggedTree J D) (fun p ↦ (r ‘ (kpair.π₁ p)) ‘ (kpair.π₂ p)) (by definability)

theorem internalTaggedTreeRank_value {J D r j x : V} (hj : j ∈ J) (hx : x ∈ D ‘ j) :
    (internalTaggedTreeRank J D r) ‘ ⟨j, x⟩ₖ = (r ‘ j) ‘ x := by
  rw [internalTaggedTreeRank, value_definableGraph _ _ _ (pair_mem_internalTaggedTree.mpr ⟨hj, hx⟩)]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]

instance internalTaggedTreeRank_isFunction (J D r : V) : IsFunction (internalTaggedTreeRank J D r) :=
  inferInstanceAs (IsFunction (definableGraph _ _ _))

theorem domain_internalTaggedTreeRank (J D r : V) :
    domain (internalTaggedTreeRank J D r) = internalTaggedTree J D := domain_definableGraph _ _ _

theorem internalTaggedTree_ranked {J D S κ r : V}
    (hT : ∀ j ∈ J, InternalRankedTree (D ‘ j) (S ‘ j) κ (r ‘ j)) :
    InternalRankedTree (internalTaggedTree J D) (internalTaggedTreeOrder J D S) κ (internalTaggedTreeRank J D r) := by
  refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨j, hj, x, hx, rfl⟩ := (mem_internalTaggedTree _ _ _).mp hp
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using function_value_mem (hT j hj).rank_function hx
  · intro p hp q hq hpq
    obtain ⟨j, hj, x, hx, rfl⟩ := (mem_internalTaggedTree _ _ _).mp hp
    obtain ⟨k, hk, y, hy, rfl⟩ := (mem_internalTaggedTree _ _ _).mp hq
    obtain ⟨_, _, he, hxy⟩ := pair_mem_internalTaggedTreeOrder.mp hpq
    subst k
    rw [internalTaggedTreeRank_value hj hx, internalTaggedTreeRank_value hj hy]
    exact (hT j hj).rank_monotone x hx y hy hxy
  · intro p hp q hq s hs hps hqs
    obtain ⟨j, hj, x, hx, rfl⟩ := (mem_internalTaggedTree _ _ _).mp hp
    obtain ⟨k, hk, y, hy, rfl⟩ := (mem_internalTaggedTree _ _ _).mp hq
    obtain ⟨l, hl, z, hz, rfl⟩ := (mem_internalTaggedTree _ _ _).mp hs
    obtain ⟨_, _, he, hxz⟩ := pair_mem_internalTaggedTreeOrder.mp hps
    obtain ⟨_, _, he', hyz⟩ := pair_mem_internalTaggedTreeOrder.mp hqs
    subst l
    subst k
    exact ((hT j hj).below_linear x hx y hy z hz hxz hyz).imp
      (same_pair_mem_internalTaggedTreeOrder hj hx hy).mpr
      (same_pair_mem_internalTaggedTreeOrder hj hy hx).mpr

theorem internalTaggedTree_poset {J D S : V} (hS : ∀ j ∈ J, IsForcingPoset (D ‘ j) (S ‘ j)) :
    IsForcingPoset (internalTaggedTree J D) (internalTaggedTreeOrder J D S) := by
  refine ⟨⟨internalTaggedTreeOrder_subset _ _ _, ?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨j, hj, x, hx, rfl⟩ := (mem_internalTaggedTree _ _ _).mp hp
    exact (same_pair_mem_internalTaggedTreeOrder hj hx hx).mpr ((hS j hj).1.2.1 x hx)
  · intro p hp q hq s hs hpq hqs
    obtain ⟨j, hj, x, hx, rfl⟩ := (mem_internalTaggedTree _ _ _).mp hp
    obtain ⟨k, hk, y, hy, rfl⟩ := (mem_internalTaggedTree _ _ _).mp hq
    obtain ⟨l, hl, z, hz, rfl⟩ := (mem_internalTaggedTree _ _ _).mp hs
    obtain ⟨_, _, he, hxy⟩ := pair_mem_internalTaggedTreeOrder.mp hpq
    obtain ⟨_, _, he', hyz⟩ := pair_mem_internalTaggedTreeOrder.mp hqs
    subst k
    subst l
    exact (same_pair_mem_internalTaggedTreeOrder hj hx hz).mpr ((hS j hj).1.2.2 x hx y hy z hz hxy hyz)
  · intro p hp q hq hpq hqp
    obtain ⟨j, hj, x, hx, rfl⟩ := (mem_internalTaggedTree _ _ _).mp hp
    obtain ⟨k, hk, y, hy, rfl⟩ := (mem_internalTaggedTree _ _ _).mp hq
    obtain ⟨_, _, he, hxy⟩ := pair_mem_internalTaggedTreeOrder.mp hpq
    subst k
    have hyx := (same_pair_mem_internalTaggedTreeOrder hj hy hx).mp hqp
    rw [(hS j hj).2 x hx y hy hxy hyx]

theorem internalTaggedTree_rank_injective {J D S r : V}
    (hinj : ∀ j ∈ J, ∀ x ∈ D ‘ j, ∀ y ∈ D ‘ j,
      ⟨x, y⟩ₖ ∈ S ‘ j → (r ‘ j) ‘ x = (r ‘ j) ‘ y → x = y) :
    ∀ p ∈ internalTaggedTree J D, ∀ q ∈ internalTaggedTree J D,
      ⟨p, q⟩ₖ ∈ internalTaggedTreeOrder J D S →
      (internalTaggedTreeRank J D r) ‘ p = (internalTaggedTreeRank J D r) ‘ q → p = q := by
  intro p hp q hq hpq heq
  obtain ⟨j, hj, x, hx, rfl⟩ := (mem_internalTaggedTree _ _ _).mp hp
  obtain ⟨k, hk, y, hy, rfl⟩ := (mem_internalTaggedTree _ _ _).mp hq
  obtain ⟨_, _, he, hxy⟩ := pair_mem_internalTaggedTreeOrder.mp hpq
  subst k
  rw [internalTaggedTreeRank_value hj hx, internalTaggedTreeRank_value hj hy] at heq
  rw [hinj j hj x hx y hy hxy heq]

theorem tagged_branch {J D S κ r j B : V} (hj : j ∈ J)
    (hB : IsInternalCofinalBranch (D ‘ j) (S ‘ j) κ (r ‘ j) B) :
    IsInternalCofinalBranch (internalTaggedTree J D) (internalTaggedTreeOrder J D S) κ
      (internalTaggedTreeRank J D r) (({j} : V) ×ˢ B) := by
  have hmem (p : V) : p ∈ ({j} : V) ×ˢ B ↔ ∃ x ∈ B, p = ⟨j, x⟩ₖ := by
    simp only [mem_prod_iff, mem_singleton_iff, exists_eq_left]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := (hmem p).mp hp
    exact pair_mem_internalTaggedTree.mpr ⟨hj, hB.1 x hx⟩
  · intro p hp q hq
    obtain ⟨x, hx, rfl⟩ := (hmem p).mp hp
    obtain ⟨y, hy, rfl⟩ := (hmem q).mp hq
    exact (hB.2.1 x hx y hy).imp
      (same_pair_mem_internalTaggedTreeOrder hj (hB.1 x hx) (hB.1 y hy)).mpr
      (same_pair_mem_internalTaggedTreeOrder hj (hB.1 y hy) (hB.1 x hx)).mpr
  · intro i hi
    obtain ⟨x, hx, hix⟩ := hB.2.2.1 i hi
    exact ⟨⟨j, x⟩ₖ, (hmem _).mpr ⟨x, hx, rfl⟩, by rw [internalTaggedTreeRank_value hj (hB.1 x hx)]; exact hix⟩
  · intro p hp q hq hpq
    obtain ⟨k, hk, x, hx, rfl⟩ := (mem_internalTaggedTree _ _ _).mp hp
    obtain ⟨y, hy, rfl⟩ := (hmem q).mp hq
    obtain ⟨_, _, he, hxy⟩ := pair_mem_internalTaggedTreeOrder.mp hpq
    subst k
    exact (hmem _).mpr ⟨x, hB.2.2.2 x hx y hy hxy, rfl⟩

noncomputable def taggedBranchProjection (D j B : V) : V := {x ∈ D ‘ j ; ⟨j, x⟩ₖ ∈ B}

theorem tagged_branch_projection {J D S κ r j x B : V}
    (hB : IsInternalCofinalBranch (internalTaggedTree J D) (internalTaggedTreeOrder J D S) κ
      (internalTaggedTreeRank J D r) B) (hx : ⟨j, x⟩ₖ ∈ B) :
    j ∈ J ∧ IsInternalCofinalBranch (D ‘ j) (S ‘ j) κ (r ‘ j) (taggedBranchProjection D j B) ∧
      B = ({j} : V) ×ˢ taggedBranchProjection D j B := by
  have hj := (pair_mem_internalTaggedTree.mp (hB.1 _ hx)).1
  have htag : ∀ p ∈ B, ∃ y ∈ D ‘ j, p = ⟨j, y⟩ₖ := by
    intro p hp
    obtain ⟨k, hk, y, hy, rfl⟩ := (mem_internalTaggedTree _ _ _).mp (hB.1 p hp)
    have he : j = k := by
      rcases hB.2.1 _ hx _ hp with h | h
      · exact (pair_mem_internalTaggedTreeOrder.mp h).2.2.1
      · exact (pair_mem_internalTaggedTreeOrder.mp h).2.2.1.symm
    subst k
    exact ⟨y, hy, rfl⟩
  have heq : B = ({j} : V) ×ˢ taggedBranchProjection D j B := by
    ext p
    constructor
    · intro hp
      obtain ⟨y, hy, rfl⟩ := htag p hp
      exact kpair_mem_iff.mpr ⟨by simp, mem_sep_iff.mpr ⟨hy, hp⟩⟩
    · intro hp
      obtain ⟨k, hk, y, hy, rfl⟩ := mem_prod_iff.mp hp
      have he : k = j := mem_singleton_iff.mp hk
      subst k
      exact (mem_sep_iff.mp hy).2
  refine ⟨hj, ⟨fun _ hy ↦ (mem_sep_iff.mp hy).1, ?_, ?_, ?_⟩, heq⟩
  · intro y hy z hz
    have hy' := mem_sep_iff.mp hy
    have hz' := mem_sep_iff.mp hz
    exact (hB.2.1 _ hy'.2 _ hz'.2).imp
      (same_pair_mem_internalTaggedTreeOrder hj hy'.1 hz'.1).mp
      (same_pair_mem_internalTaggedTreeOrder hj hz'.1 hy'.1).mp
  · intro i hi
    obtain ⟨p, hp, hip⟩ := hB.2.2.1 i hi
    obtain ⟨y, hy, rfl⟩ := htag p hp
    exact ⟨y, mem_sep_iff.mpr ⟨hy, hp⟩, by rw [internalTaggedTreeRank_value hj hy] at hip; exact hip⟩
  · intro y hy z hz hyz
    have hz' := mem_sep_iff.mp hz
    exact mem_sep_iff.mpr ⟨hy, hB.2.2.2 _ (pair_mem_internalTaggedTree.mpr ⟨hj, hy⟩) _ hz'.2
      ((same_pair_mem_internalTaggedTreeOrder hj hy hz'.1).mpr hyz)⟩

theorem tagged_branch_decomposition {J D S κ r B : V} (hκ : IsNonempty κ)
    (hB : IsInternalCofinalBranch (internalTaggedTree J D) (internalTaggedTreeOrder J D S) κ
      (internalTaggedTreeRank J D r) B) :
    ∃ j ∈ J, ∃ C, IsInternalCofinalBranch (D ‘ j) (S ‘ j) κ (r ‘ j) C ∧ B = ({j} : V) ×ˢ C := by
  obtain ⟨i, hi⟩ := hκ
  obtain ⟨p, hp, _⟩ := hB.2.2.1 i hi
  obtain ⟨j, _, x, _, rfl⟩ := (mem_internalTaggedTree _ _ _).mp (hB.1 p hp)
  have hh := tagged_branch_projection hB hp
  exact ⟨j, hh.1, taggedBranchProjection D j B, hh.2⟩

end ZFVP.Schmerl
