import ZFVP.SetTheory.Telescoping
import ZFVP.SetTheory.MaximalAntichains

/-! Trees with nonempty body under inclusion, positive trees (level density bounded below), the
random conditions, and the relation between compatibility, intersections of bodies and levels. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The inclusion order: `⟨p, q⟩ ∈ R` iff `p ⊆ q`; a subtree is a stronger condition. -/
noncomputable def inclusionOrder (P : V) : V := {s ∈ P ×ˢ P ; kpair.π₁ s ⊆ kpair.π₂ s}

instance inclusionOrder_definable : ℒₛₑₜ-function₁[V] inclusionOrder := by
  have h : ℒₛₑₜ-relation[V] (fun R P ↦ ∀ s, s ∈ R ↔ s ∈ P ×ˢ P ∧ kpair.π₁ s ⊆ kpair.π₂ s) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = inclusionOrder (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [inclusionOrder, mem_sep_iff]

theorem pair_mem_inclusionOrder (P p q : V) : ⟨p, q⟩ₖ ∈ inclusionOrder P ↔ p ∈ P ∧ q ∈ P ∧ p ⊆ q := by
  simp only [inclusionOrder, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

theorem inclusionOrder_preorder (P : V) : IsForcingPreorder P (inclusionOrder P) := by
  refine ⟨fun s hs ↦ (mem_sep_iff.mp hs).1, fun p hp ↦ ?_, fun p hp q hq r hr hpq hqr ↦ ?_⟩
  · exact (pair_mem_inclusionOrder _ _ _).mpr ⟨hp, hp, fun x hx ↦ hx⟩
  · obtain ⟨-, -, h1⟩ := (pair_mem_inclusionOrder _ _ _).mp hpq
    obtain ⟨-, -, h2⟩ := (pair_mem_inclusionOrder _ _ _).mp hqr
    exact (pair_mem_inclusionOrder _ _ _).mpr ⟨hp, hr, fun x hx ↦ h2 x (h1 x hx)⟩

theorem inclusionOrder_top {P X : V} (hP : ∀ p ∈ P, p ⊆ X) (hX : X ∈ P) :
    IsForcingTop P (inclusionOrder P) X :=
  ⟨hX, fun p hp ↦ (pair_mem_inclusionOrder _ _ _).mpr ⟨hp, hX, hP p hp⟩⟩

theorem tree_inter {T T' : V} (hT : IsTree T) (hT' : IsTree T') : IsTree (T ∩ T') :=
  ⟨fun s hs ↦ hT.1 s (mem_inter_iff.mp hs).1, fun s hs n hn ↦
    mem_inter_iff.mpr ⟨hT.2 s (mem_inter_iff.mp hs).1 n hn, hT'.2 s (mem_inter_iff.mp hs).2 n hn⟩⟩

theorem binarySequences_isTree : IsTree (binarySequences V) := by
  refine ⟨fun s hs ↦ hs, fun s hs n hn ↦ ?_⟩
  obtain ⟨k, hk, hsk⟩ := (mem_binarySequences_iff _).mp hs
  rw [domain_eq_of_mem_function hsk] at hn
  have : IsOrdinal k := IsOrdinal.nat hk
  exact (mem_binarySequences_iff _).mpr ⟨n, IsTransitive.ω.transitive k hk n hn,
    function_restrict_mem hsk (IsOrdinal.toIsTransitive.transitive n hn)⟩

/-- Trees with nonempty body. -/
noncomputable def bodyTrees (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V :=
  {T ∈ ℘ (binarySequences V) ; IsTree T ∧ ∃ x, x ∈ treeBody T}

theorem mem_bodyTrees_iff (T : V) : T ∈ bodyTrees V ↔ IsTree T ∧ ∃ x, x ∈ treeBody T := by
  unfold bodyTrees
  rw [mem_sep_iff, mem_power_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.1.1, h⟩⟩

theorem bodyTrees_compatible_iff {T T' : V} (hT : T ∈ bodyTrees V) (hT' : T' ∈ bodyTrees V) :
    ForcingCompatible (bodyTrees V) (inclusionOrder (bodyTrees V)) T T' ↔
      ∃ x, x ∈ treeBody T ∧ x ∈ treeBody T' := by
  constructor
  · rintro ⟨r, hr, hrT, hrT'⟩
    obtain ⟨-, x, hx⟩ := (mem_bodyTrees_iff r).mp hr
    obtain ⟨-, -, h1⟩ := (pair_mem_inclusionOrder _ _ _).mp hrT
    obtain ⟨-, -, h2⟩ := (pair_mem_inclusionOrder _ _ _).mp hrT'
    exact ⟨x, treeBody_mono h1 x hx, treeBody_mono h2 x hx⟩
  · rintro ⟨x, hx, hx'⟩
    have hr : T ∩ T' ∈ bodyTrees V := (mem_bodyTrees_iff _).mpr
      ⟨tree_inter ((mem_bodyTrees_iff T).mp hT).1 ((mem_bodyTrees_iff T').mp hT').1,
        x, by rw [treeBody_inter]; exact mem_inter_iff.mpr ⟨hx, hx'⟩⟩
    exact ⟨T ∩ T', hr, (pair_mem_inclusionOrder _ _ _).mpr ⟨hr, hT, fun z hz ↦ (mem_inter_iff.mp hz).1⟩,
      (pair_mem_inclusionOrder _ _ _).mpr ⟨hr, hT', fun z hz ↦ (mem_inter_iff.mp hz).2⟩⟩

/-- Positive trees: level density bounded below by `2^{-m}` at every level. -/
def IsPositiveTree (T : V) : Prop :=
  IsTree T ∧ ∃ m ∈ (ω : V), ∀ M ∈ (ω : V), ¬ levelSet T M ×ˢ (((2 : ℕ) : V) ^ m) ≤# ((2 : ℕ) : V) ^ M

instance isPositiveTree_definable : ℒₛₑₜ-predicate[V] IsPositiveTree := by
  unfold IsPositiveTree levelSet
  definability

theorem isPositiveTree_levels_nonempty {T : V} (h : IsPositiveTree T) :
    ∀ M ∈ (ω : V), ∃ s ∈ T, s ∈ ((2 : ℕ) : V) ^ M := by
  intro M hM
  obtain ⟨-, m, -, hbig⟩ := h
  by_contra hne
  apply hbig M hM
  refine cardLE_of_subset (fun z hz ↦ ?_)
  obtain ⟨s, hs, -, -, -⟩ := mem_prod_iff.mp hz
  obtain ⟨hsT, hsM⟩ := (mem_levelSet_iff _ _ _).mp hs
  exact (hne ⟨s, hsT, hsM⟩).elim

theorem isPositiveTree_body_nonempty {T : V} (h : IsPositiveTree T) : ∃ x, x ∈ treeBody T :=
  exists_branch_of_levels h.1 (isPositiveTree_levels_nonempty h)

theorem isPositiveTree_mem_bodyTrees {T : V} (h : IsPositiveTree T) : T ∈ bodyTrees V :=
  (mem_bodyTrees_iff T).mpr ⟨h.1, isPositiveTree_body_nonempty h⟩

theorem isPositiveTree_mono {T T' : V} (hT' : IsTree T') (hsub : T ⊆ T') (h : IsPositiveTree T) :
    IsPositiveTree T' := by
  obtain ⟨-, m, hm, hbig⟩ := h
  refine ⟨hT', m, hm, fun M hM hle ↦ hbig M hM ?_⟩
  exact (prod_cardLE_prod (cardLE_of_subset (levelSet_mono hsub M)) (CardLE.refl _)).trans hle

/-- A tree which is not positive has null body. -/
theorem isNull_treeBody_of_not_positive {T : V} (hT : IsTree T) (h : ¬ IsPositiveTree T) :
    IsNull (treeBody T) := by
  have hsmall : ∀ m ∈ (ω : V), ∃ M ∈ (ω : V), levelSet T M ×ˢ (((2 : ℕ) : V) ^ m) ≤# ((2 : ℕ) : V) ^ M := by
    intro m hm
    by_contra hcon
    push Not at hcon
    exact h ⟨hT, m, hm, hcon⟩
  refine isNull_of_small_covers (fun m hm ↦ ?_)
  obtain ⟨M, hM, hle⟩ := hsmall m hm
  refine ⟨levelSet T M, levelSet_subset_binarySequences hM, levelSet_finite hM, ⟨M, hM, ?_, ?_⟩, ?_⟩
  · intro s hs
    rw [domain_eq_of_mem_function ((mem_levelSet_iff _ _ _).mp hs).2]
  · rw [shadow_levelSet]
    exact hle
  · intro x hx
    refine ⟨x ↾ M, restrict_mem_levelSet hx hM, ?_⟩
    rw [domain_eq_of_mem_function ((mem_levelSet_iff _ _ _).mp (restrict_mem_levelSet hx hM)).2]

theorem isPositiveTree_of_not_null {T : V} (hT : IsTree T) (h : ¬ IsNull (treeBody T)) : IsPositiveTree T :=
  by_contra (fun h' ↦ h (isNull_treeBody_of_not_positive hT h'))

/-- The random conditions: positive trees. -/
noncomputable def randomConditions (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V :=
  {T ∈ ℘ (binarySequences V) ; IsPositiveTree T}

theorem mem_randomConditions_iff (T : V) : T ∈ randomConditions V ↔ IsPositiveTree T := by
  unfold randomConditions
  rw [mem_sep_iff, mem_power_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.1.1, h⟩⟩

theorem randomConditions_subset_bodyTrees : randomConditions V ⊆ bodyTrees V :=
  fun T hT ↦ isPositiveTree_mem_bodyTrees ((mem_randomConditions_iff T).mp hT)

theorem two_cardLE_function_power_one : ((2 : ℕ) : V) ≤# ((2 : ℕ) : V) ^ succ (∅ : V) := by
  refine cardLE_of_injective_map (fun i ↦ insert ⟨∅, i⟩ₖ ∅) (by definability) ?_ ?_
  · intro i hi
    exact function_append_mem (empty_mem_power_empty _) hi
  · intro i _ i' _ h
    have : ⟨∅, i⟩ₖ ∈ insert ⟨∅, i'⟩ₖ (∅ : V) := by rw [← h]; exact mem_insert.mpr (Or.inl rfl)
    rcases mem_insert.mp this with h' | h'
    · exact (kpair_inj h').2
    · exact (not_mem_empty h').elim

theorem fullTree_positive : IsPositiveTree (binarySequences V) := by
  refine ⟨binarySequences_isTree, succ ∅, ω_succ_closed zero_mem_ω, fun M hM hle ↦ ?_⟩
  have hlev : levelSet (binarySequences V) M = ((2 : ℕ) : V) ^ M := by
    apply mem_ext
    intro s
    rw [mem_levelSet_iff]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨(mem_binarySequences_iff _).mpr ⟨M, hM, h⟩, h⟩⟩
  rw [hlev] at hle
  have h1 : (((2 : ℕ) : V) ^ M) ×ˢ ((2 : ℕ) : V) ≤# ((2 : ℕ) : V) ^ M :=
    (prod_cardLE_prod (CardLE.refl _) two_cardLE_function_power_one).trans hle
  have hsing : IsInternallyFinite ({∅} : V) := internallyFinite_subset internallyFinite_two (fun x hx ↦ by
    rw [mem_singleton_iff] at hx
    rw [hx]
    exact (mem_two_iff _).mpr (Or.inl rfl))
  have hfin : IsInternallyFinite ((((2 : ℕ) : V) ^ M) ×ˢ ({∅} : V)) :=
    internallyFinite_prod (internallyFinite_two_pow hM) hsing
  have h2 : ((2 : ℕ) : V) ^ M ≤# (((2 : ℕ) : V) ^ M) ×ˢ ({∅} : V) := by
    refine cardLE_of_injective_map (fun u ↦ ⟨u, ∅⟩ₖ) (by definability) ?_ ?_
    · intro u hu
      exact kpair_mem_iff.mpr ⟨hu, mem_singleton_iff.mpr rfl⟩
    · intro u _ u' _ h
      exact (kpair_inj h).1
  have hfresh : ⟨zeroSequence M, succ ∅⟩ₖ ∉ (((2 : ℕ) : V) ^ M) ×ˢ ({∅} : V) := by
    intro h
    exact succ_empty_ne_empty (mem_singleton_iff.mp (kpair_mem_iff.mp h).2)
  have hsub : insert ⟨zeroSequence M, succ ∅⟩ₖ ((((2 : ℕ) : V) ^ M) ×ˢ ({∅} : V)) ⊆
      (((2 : ℕ) : V) ^ M) ×ˢ ((2 : ℕ) : V) := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact kpair_mem_iff.mpr ⟨zeroSequence_mem_power M, (mem_two_iff _).mpr (Or.inr rfl)⟩
    · obtain ⟨u, hu, t, ht, rfl⟩ := mem_prod_iff.mp hz
      rw [mem_singleton_iff] at ht
      rw [ht]
      exact kpair_mem_iff.mpr ⟨hu, (mem_two_iff _).mpr (Or.inl rfl)⟩
  exact not_insert_fresh_cardLE hfin hfresh (((cardLE_of_subset hsub).trans h1).trans h2)

theorem randomConditions_top :
    IsForcingTop (randomConditions V) (inclusionOrder (randomConditions V)) (binarySequences V) :=
  inclusionOrder_top (fun T hT ↦ ((mem_randomConditions_iff T).mp hT).1.1)
    ((mem_randomConditions_iff _).mpr fullTree_positive)

theorem randomConditions_compatible_iff {T T' : V} (hT : T ∈ randomConditions V) (hT' : T' ∈ randomConditions V) :
    ForcingCompatible (randomConditions V) (inclusionOrder (randomConditions V)) T T' ↔
      IsPositiveTree (T ∩ T') := by
  have hTt := ((mem_randomConditions_iff T).mp hT).1
  have hT't := ((mem_randomConditions_iff T').mp hT').1
  constructor
  · rintro ⟨r, hr, hrT, hrT'⟩
    obtain ⟨-, -, h1⟩ := (pair_mem_inclusionOrder _ _ _).mp hrT
    obtain ⟨-, -, h2⟩ := (pair_mem_inclusionOrder _ _ _).mp hrT'
    exact isPositiveTree_mono (tree_inter hTt hT't) (fun z hz ↦ mem_inter_iff.mpr ⟨h1 z hz, h2 z hz⟩)
      ((mem_randomConditions_iff r).mp hr)
  · intro h
    have hr : T ∩ T' ∈ randomConditions V := (mem_randomConditions_iff _).mpr h
    exact ⟨T ∩ T', hr, (pair_mem_inclusionOrder _ _ _).mpr ⟨hr, hT, fun z hz ↦ (mem_inter_iff.mp hz).1⟩,
      (pair_mem_inclusionOrder _ _ _).mpr ⟨hr, hT', fun z hz ↦ (mem_inter_iff.mp hz).2⟩⟩

/-- Trees with disjoint bodies have disjoint levels from some level on. -/
theorem exists_disjoint_level {T T' : V} (hT : IsTree T) (hT' : IsTree T')
    (h : ∀ x, x ∈ treeBody T → x ∈ treeBody T' → False) :
    ∃ M ∈ (ω : V), ∀ s, s ∉ levelSet (T ∩ T') M :=
  exists_empty_level_of_treeBody_empty (tree_inter hT hT') (fun x hx ↦ by
    rw [treeBody_inter] at hx
    exact h x (mem_inter_iff.mp hx).1 (mem_inter_iff.mp hx).2)

theorem levelSet_empty_mono {T M M' : V} (hT : IsTree T) (hM : M ∈ (ω : V))
    (hMM' : M ⊆ M') (h : ∀ s, s ∉ levelSet T M) : ∀ s, s ∉ levelSet T M' := by
  intro s hs
  obtain ⟨hsT, hsM'⟩ := (mem_levelSet_iff _ _ _).mp hs
  apply h (s ↾ M)
  exact (mem_levelSet_iff _ _ _).mpr ⟨tree_restrict_mem hT hsT hM (by rw [domain_eq_of_mem_function hsM']; exact hMM'),
    function_restrict_mem hsM' hMM'⟩

end ZFVP
