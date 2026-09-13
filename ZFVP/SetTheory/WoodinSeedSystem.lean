import ZFVP.SetTheory.WoodinSeedSystemBasics

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem constantProduct_mem_function {X B a : V} (ha : a ∈ B) : X ×ˢ {a} ∈ B ^ X := by
  apply mem_function.intro
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp hz
    have he := mem_singleton_iff.mp hy
    subst y
    exact kpair_mem_iff.mpr ⟨hx, ha⟩
  · intro x hx
    refine ⟨a, kpair_mem_iff.mpr ⟨hx, by simp⟩, ?_⟩
    intro y hy
    exact mem_singleton_iff.mp (kpair_mem_iff.mp hy).2

theorem woodinSeed_functions {θ P π E t : V} [IsOrdinal θ]
    (h : IsFunctionalSplitForcingSystem θ P π E) (ht : ∀ i ∈ θ, t ‘ i ∈ P ‘ i) :
    IsFunctionalSplitForcingSystem (woodinSourceIndex θ) (woodinInsertSeed θ P {∅})
      (woodinSeedProjections θ P π) (woodinSeedSections θ E t) := by
  constructor
  · intro i hi j hj hij
    let := IsOrdinal.of_mem hj
    rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
    · rw [woodinSeedProjections, woodinSeedMatrix_zero hj, woodinSeedProjectionColumn,
        value_definableGraph _ _ _ hj, woodinInsertSeed_zero]
      exact constantProduct_mem_function (by simp)
    · let := IsOrdinal.of_mem ha
      have hjn := woodinSourceIndex_subset_nonzero hij
      have hrj := (woodinRecursiveIndex_mem_iff hjn).mpr hj
      rw [woodinSeedProjections, woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hj
        (woodinSourceIndex_nonzero a), woodinRecursiveIndex_sourceIndex,
        woodinInsertSeed_at_sourceIndex ha, woodinInsertSeed_nonzero hj hjn]
      exact h.projection a ha _ hrj (woodinSourceIndex_subset_recursive hij)
  · intro i hi j hj hij
    let := IsOrdinal.of_mem hj
    rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
    · rw [woodinSeedSections, woodinSeedMatrix_zero hj, woodinSeedSectionColumn,
        value_definableGraph _ _ _ hj, woodinInsertSeed_zero]
      exact constantProduct_mem_function (woodinSeed_top_mem ht j hj)
    · let := IsOrdinal.of_mem ha
      have hjn := woodinSourceIndex_subset_nonzero hij
      have hrj := (woodinRecursiveIndex_mem_iff hjn).mpr hj
      rw [woodinSeedSections, woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hj
        (woodinSourceIndex_nonzero a), woodinRecursiveIndex_sourceIndex,
        woodinInsertSeed_at_sourceIndex ha, woodinInsertSeed_nonzero hj hjn]
      exact h.sectionMap a ha _ hrj (woodinSourceIndex_subset_recursive hij)

theorem woodinSeed_order {θ P R π E t : V} [IsOrdinal θ]
    (h : IsOrderedSplitForcingSystem θ P R π E) (ht : IsToppedSplitForcingSystem θ P R π E t) :
    IsOrderedSplitForcingSystem (woodinSourceIndex θ) (woodinInsertSeed θ P {∅})
      (woodinInsertSeed θ R (({∅} : V) ×ˢ {∅})) (woodinSeedProjections θ P π)
      (woodinSeedSections θ E t) := by
  constructor
  · intro i hi
    rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
    · rw [woodinInsertSeed_zero, woodinInsertSeed_zero]
      exact singletonForcing_preorder ∅
    · rw [woodinInsertSeed_at_sourceIndex ha, woodinInsertSeed_at_sourceIndex ha]
      exact h.preorder a ha
  · intro i hi j hj hij p hp q hq hpq
    let := IsOrdinal.of_mem hj
    rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
    · rw [woodinSeedProjections_zero_value hj hp, woodinSeedProjections_zero_value hj hq,
        woodinInsertSeed_zero]
      simp
    · let := IsOrdinal.of_mem ha
      have hjn := woodinSourceIndex_subset_nonzero hij
      have hrj := (woodinRecursiveIndex_mem_iff hjn).mpr hj
      rw [woodinInsertSeed_nonzero hj hjn] at hp hq hpq
      rw [woodinSeedProjections, woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hj
        (woodinSourceIndex_nonzero a), woodinRecursiveIndex_sourceIndex,
        woodinInsertSeed_at_sourceIndex ha]
      exact h.projMono a ha _ hrj (woodinSourceIndex_subset_recursive hij) p hp q hq hpq
  · intro i hi j hj hij p hp q hq
    let := IsOrdinal.of_mem hj
    rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
    · rw [woodinInsertSeed_zero] at hq
      have he := mem_singleton_iff.mp hq
      subst q
      rw [woodinSeedSections_zero_value hj, woodinSeedProjections_zero_value hj hp,
        woodinInsertSeed_zero]
      constructor
      · intro _
        simp
      · intro _
        exact ((woodinSeed_tops ht).top j hj).2 p hp
    · let := IsOrdinal.of_mem ha
      have hjn := woodinSourceIndex_subset_nonzero hij
      have hrj := (woodinRecursiveIndex_mem_iff hjn).mpr hj
      rw [woodinInsertSeed_nonzero hj hjn] at hp
      rw [woodinInsertSeed_at_sourceIndex ha] at hq
      rw [woodinSeedProjections, woodinSeedSections,
        woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hj (woodinSourceIndex_nonzero a),
        woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hj (woodinSourceIndex_nonzero a),
        woodinRecursiveIndex_sourceIndex, woodinInsertSeed_at_sourceIndex ha,
        woodinInsertSeed_nonzero hj hjn]
      exact h.below a ha _ hrj (woodinSourceIndex_subset_recursive hij) p hp q hq

noncomputable def woodinSeedLiftMap (Q : V) : V :=
  definableGraph (Q ×ˢ ({∅} : V)) kpair.π₁ (by definability)

instance woodinSeedLiftMap_definable : ℒₛₑₜ-function₁[V] woodinSeedLiftMap := by
  have hd : ℒₛₑₜ-relation (fun M Q : V ↦ ∀ z, z ∈ M ↔
    ∃ p ∈ Q ×ˢ ({∅} : V), z = ⟨p, kpair.π₁ p⟩ₖ) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = woodinSeedLiftMap (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [woodinSeedLiftMap, mem_definableGraph_iff]

theorem woodinSeedLiftMap_value {Q p : V} (hp : p ∈ Q) :
    (woodinSeedLiftMap Q) ‘ ⟨p, ∅⟩ₖ = p := by
  rw [woodinSeedLiftMap, value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hp, by simp⟩),
    kpair.π₁_kpair]

noncomputable def woodinSeedLiftColumn (θ Q : V) : V :=
  definableGraph (woodinSourceIndex θ) (fun j ↦ woodinSeedLiftMap (Q ‘ j)) (by definability)

noncomputable def woodinSeedLifts (θ P L : V) : V :=
  woodinSeedMatrix θ L (woodinSeedLiftColumn θ (woodinInsertSeed θ P {∅}))

theorem woodinSeedLifts_zero_value {θ P L j p : V} [IsOrdinal θ]
    (hj : j ∈ woodinSourceIndex θ) (hp : p ∈ (woodinInsertSeed θ P {∅}) ‘ j) :
    ((woodinSeedLifts θ P L) ‘ ⟨∅, j⟩ₖ) ‘ ⟨p, ∅⟩ₖ = p := by
  rw [woodinSeedLifts, woodinSeedMatrix_zero hj, woodinSeedLiftColumn,
    value_definableGraph _ _ _ hj, woodinSeedLiftMap_value hp]

theorem woodinSeed_lifts {θ P R π E L t : V} [IsOrdinal θ]
    (h : IsForcingIterationSystem θ P R π E L t) :
    IsCoherentForcingLift (woodinSourceIndex θ) (woodinInsertSeed θ P {∅})
      (woodinInsertSeed θ R (({∅} : V) ×ˢ {∅})) (woodinSeedProjections θ P π)
      (woodinSeedLifts θ P L) := by
  constructor
  · intro i hi j hj hij p hp q hq hpq
    let := IsOrdinal.of_mem hj
    rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
    · rw [woodinInsertSeed_zero] at hq
      have he := mem_singleton_iff.mp hq
      subst q
      rw [woodinSeedLifts_zero_value hj hp, woodinSeedProjections_zero_value hj hp]
      exact ⟨hp, ((woodinSeed_order h.order h.tops).preorder j hj).2.1 p hp, rfl⟩
    · let := IsOrdinal.of_mem ha
      have hjn := woodinSourceIndex_subset_nonzero hij
      have hrj := (woodinRecursiveIndex_mem_iff hjn).mpr hj
      rw [woodinInsertSeed_nonzero hj hjn] at hp
      rw [woodinInsertSeed_at_sourceIndex ha] at hq
      rw [woodinSeedProjections, woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hj
        (woodinSourceIndex_nonzero a), woodinRecursiveIndex_sourceIndex,
        woodinInsertSeed_at_sourceIndex ha] at hpq
      rw [woodinSeedLifts, woodinSeedProjections,
        woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hj (woodinSourceIndex_nonzero a),
        woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hj (woodinSourceIndex_nonzero a),
        woodinRecursiveIndex_sourceIndex, woodinInsertSeed_nonzero hj hjn, woodinInsertSeed_nonzero hj hjn]
      exact h.lifts.lift a ha _ hrj (woodinSourceIndex_subset_recursive hij) p hp q hq hpq
  · intro i hi j hj k hk hij hjk p hp q hq hpq
    let := IsOrdinal.of_mem hj
    let := IsOrdinal.of_mem hk
    rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
    · rw [woodinInsertSeed_zero] at hq
      have he := mem_singleton_iff.mp hq
      subst q
      rw [woodinSeedLifts_zero_value hk hp,
        woodinSeedLifts_zero_value hj (woodinSeed_projMaps h.split j hj k hk hjk p hp)]
    · let := IsOrdinal.of_mem ha
      have hjn := woodinSourceIndex_subset_nonzero hij
      have hik : woodinSourceIndex a ⊆ k := fun x hx ↦ hjk x (hij x hx)
      have hkn := woodinSourceIndex_subset_nonzero hik
      have hrj := (woodinRecursiveIndex_mem_iff hjn).mpr hj
      have hrk := (woodinRecursiveIndex_mem_iff hkn).mpr hk
      have hrecjk : woodinRecursiveIndex j ⊆ woodinRecursiveIndex k :=
        woodinSourceIndex_subset_iff.mp (by
          simpa only [woodinSourceIndex_recursiveIndex j hjn,
            woodinSourceIndex_recursiveIndex k hkn] using hjk)
      rw [woodinInsertSeed_nonzero hk hkn] at hp
      rw [woodinInsertSeed_at_sourceIndex ha] at hq
      rw [woodinSeedProjections, woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hk
        (woodinSourceIndex_nonzero a), woodinRecursiveIndex_sourceIndex,
        woodinInsertSeed_at_sourceIndex ha] at hpq
      rw [woodinSeedProjections, woodinSeedLifts,
        woodinSeedMatrix_positive hj hk hjn,
        woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hk (woodinSourceIndex_nonzero a),
        woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hj (woodinSourceIndex_nonzero a),
        woodinRecursiveIndex_sourceIndex]
      exact h.lifts.commute a ha _ hrj _ hrk (woodinSourceIndex_subset_recursive hij) hrecjk p hp q hq hpq

theorem woodinSeed_compatible {θ P R π E L t : V} [IsOrdinal θ]
    (h : IsForcingIterationSystem θ P R π E L t) :
    IsSectionCompatibleForcingLift (woodinSourceIndex θ) (woodinInsertSeed θ P {∅})
      (woodinInsertSeed θ R (({∅} : V) ×ˢ {∅})) (woodinSeedProjections θ P π)
      (woodinSeedSections θ E t) (woodinSeedLifts θ P L) := by
  constructor
  intro i hi k hk j hj hik hkj p hp q hq hpq
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hk
  rcases woodinSourceIndex_cases hi with rfl | ⟨a, ha, rfl⟩
  · rw [woodinInsertSeed_zero] at hq
    have he := mem_singleton_iff.mp hq
    subst q
    rw [woodinSeedLifts_zero_value hj
        (woodinSeed_secMaps h.split (fun a ha ↦ (h.tops.top a ha).1) k hk j hj hkj p hp),
      woodinSeedLifts_zero_value hk hp]
  · let := IsOrdinal.of_mem ha
    have hkn := woodinSourceIndex_subset_nonzero hik
    have hij : woodinSourceIndex a ⊆ j := fun x hx ↦ hkj x (hik x hx)
    have hjn := woodinSourceIndex_subset_nonzero hij
    have hrj := (woodinRecursiveIndex_mem_iff hjn).mpr hj
    have hrk := (woodinRecursiveIndex_mem_iff hkn).mpr hk
    have hreckj : woodinRecursiveIndex k ⊆ woodinRecursiveIndex j :=
      woodinSourceIndex_subset_iff.mp (by
        simpa only [woodinSourceIndex_recursiveIndex j hjn,
          woodinSourceIndex_recursiveIndex k hkn] using hkj)
    rw [woodinInsertSeed_nonzero hk hkn] at hp
    rw [woodinInsertSeed_at_sourceIndex ha] at hq
    rw [woodinSeedProjections, woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hk
      (woodinSourceIndex_nonzero a), woodinRecursiveIndex_sourceIndex,
      woodinInsertSeed_at_sourceIndex ha] at hpq
    rw [woodinSeedSections, woodinSeedLifts,
      woodinSeedMatrix_positive hk hj hkn,
      woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hk (woodinSourceIndex_nonzero a),
      woodinSeedMatrix_positive (woodinSourceIndex_mem_iff.mpr ha) hj (woodinSourceIndex_nonzero a),
      woodinRecursiveIndex_sourceIndex]
    exact h.compatible.compatible a ha _ hrk _ hrj (woodinSourceIndex_subset_recursive hik) hreckj
      p hp q hq hpq

theorem woodinSeed_system {θ P R π E L t : V} [IsOrdinal θ]
    (h : IsForcingIterationSystem θ P R π E L t) :
    IsForcingIterationSystem (woodinSourceIndex θ) (woodinInsertSeed θ P {∅})
      (woodinInsertSeed θ R (({∅} : V) ×ˢ {∅})) (woodinSeedProjections θ P π)
      (woodinSeedSections θ E t) (woodinSeedLifts θ P L) (woodinInsertSeed θ t ∅) :=
  ⟨woodinSeed_split h.split h.tops, woodinSeed_order h.order h.tops,
    woodinSeed_functions h.functions (fun a ha ↦ (h.tops.top a ha).1),
    woodinSeed_tops h.tops, woodinSeed_lifts h, woodinSeed_compatible h⟩

end ZFVP
