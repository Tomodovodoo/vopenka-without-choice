import ZFVP.SetTheory.ClassForcingAlgebra
import ZFVP.ModelTheory.ClassForcingTowerAtoms

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace DefinableForcingTower

variable (T : DefinableForcingTower V)

theorem name_condition_common_bound (σ τ : T.Name) {p : V} (hp : T.Condition p) :
    ∃ i : V, IsOrdinal i ∧ IsForcingName (T.boundedConditions i) σ.val ∧
      IsForcingName (T.boundedConditions i) τ.val ∧ p ∈ T.boundedConditions i := by
  obtain ⟨i, hi, hσ, hτ⟩ := T.name_common_bound σ τ
  obtain ⟨j, q, hj, hq, rfl⟩ := hp
  have := hi
  have := hj
  have : IsOrdinal (i ∪ j) := ordinal_union_ordinal _ _
  exact ⟨i ∪ j, inferInstance,
    hσ.mono (T.boundedConditions_mono (subset_union_left _ _)),
    hτ.mono (T.boundedConditions_mono (subset_union_left _ _)),
    T.tagged_mem_boundedConditions (subset_union_right _ _) hq⟩

variable [Countable V]

theorem forcesEqual_downward (σ τ : V) : T.ClassDownward (T.ForcesEqual σ τ) := by
  intro p hp q hq hqp
  obtain ⟨i, hi, hσ, hτ, hp⟩ := hp
  obtain ⟨j, a, hj, ha, rfl⟩ := hq
  have := hi
  have := hj
  have : IsOrdinal (i ∪ j) := ordinal_union_ordinal _ _
  have hσ' := hσ.mono (T.boundedConditions_mono (subset_union_left i j))
  have hτ' := hτ.mono (T.boundedConditions_mono (subset_union_left i j))
  have hp' := T.boundedConditions_mono (subset_union_left i j) p
    (atomicEquality_subset _ _ _ _ p hp)
  have hq' := T.tagged_mem_boundedConditions (subset_union_right i j) ha
  apply (T.forcesEqual_at_iff hσ' hτ' hq').mpr
  apply (atomicEquality_regular (T.bounded_preorder (i ∪ j)) σ τ).2.1 p
    ((T.forcesEqual_at_iff hσ' hτ' hp').mp ⟨i, hi, hσ, hτ, hp⟩) _ hq'
  exact (T.pair_mem_boundedOrder _ _ _).mpr ⟨hq', hp', hqp⟩

theorem forcesMember_downward (σ τ : V) : T.ClassDownward (T.ForcesMember σ τ) := by
  intro p hp q hq hqp
  obtain ⟨i, hi, hσ, hτ, hp⟩ := hp
  obtain ⟨j, a, hj, ha, rfl⟩ := hq
  have := hi
  have := hj
  have : IsOrdinal (i ∪ j) := ordinal_union_ordinal _ _
  have hσ' := hσ.mono (T.boundedConditions_mono (subset_union_left i j))
  have hτ' := hτ.mono (T.boundedConditions_mono (subset_union_left i j))
  have hp' := T.boundedConditions_mono (subset_union_left i j) p
    (atomicMembership_subset _ _ _ _ p hp)
  have hq' := T.tagged_mem_boundedConditions (subset_union_right i j) ha
  apply (T.forcesMember_at_iff hσ' hτ' hq').mpr
  apply (atomicMembership_regular (T.bounded_preorder (i ∪ j)) σ τ).2.1 p
    ((T.forcesMember_at_iff hσ' hτ' hp').mp ⟨i, hi, hσ, hτ, hp⟩) _ hq'
  exact (T.pair_mem_boundedOrder _ _ _).mpr ⟨hq', hp', hqp⟩

/-- Atomic equality is regular in the actual class tower. -/
theorem forcesEqual_regular (σ τ : T.Name) : T.ClassRegular (T.ForcesEqual σ.val τ.val) := by
  refine ⟨fun _ hp ↦ T.forcesEqual_condition hp, T.forcesEqual_downward _ _, ?_⟩
  intro p hp
  obtain ⟨i, hi, hσ, hτ, hpP⟩ := T.name_condition_common_bound σ τ hp.1
  have := hi
  apply (T.forcesEqual_at_iff hσ hτ hpP).mpr
  by_contra hn
  obtain ⟨q, hq, hqp⟩ := exists_forcingNegation_of_not_mem hpP hn
    (atomicEquality_regular (T.bounded_preorder i) σ.val τ.val).2.2
  have hqP := forcingNegation_subset _ _ _ q hq
  have hqC := T.boundedConditions_condition hqP
  obtain ⟨r, hr, hrq⟩ := hp.2 q hqC ((T.pair_mem_boundedOrder _ _ _).mp hqp).2.2
  obtain ⟨H, hH, hrH⟩ := T.exists_generic (T.forcesEqual_condition hr)
  have hqH := hH.1.2.2.1 r hrH q hqC hrq
  have hval := (T.equal_truth hH σ τ).mpr ⟨r, hrH, hr⟩
  have hs := (T.ofClassName_eq_iff_at hH σ τ (i := i) hσ hτ).mp hval
  have hmeet := (forcingQuotientMk_eq_iff _ _ _ _ _ _ _).mp hs
  exact (genericMeets_negation (T.bounded_preorder i) (T.boundedFilter_generic hH i)
    (atomicEquality_subset _ _ _ _) (atomicEquality_regular (T.bounded_preorder i) σ.val τ.val).2.1).mp
    ⟨q, ⟨hqP, hqH⟩, hq⟩ hmeet

/-- Atomic membership is regular in the actual class tower. -/
theorem forcesMember_regular (σ τ : T.Name) : T.ClassRegular (T.ForcesMember σ.val τ.val) := by
  refine ⟨fun _ hp ↦ T.forcesMember_condition hp, T.forcesMember_downward _ _, ?_⟩
  intro p hp
  obtain ⟨i, hi, hσ, hτ, hpP⟩ := T.name_condition_common_bound σ τ hp.1
  have := hi
  apply (T.forcesMember_at_iff hσ hτ hpP).mpr
  by_contra hn
  obtain ⟨q, hq, hqp⟩ := exists_forcingNegation_of_not_mem hpP hn
    (atomicMembership_regular (T.bounded_preorder i) σ.val τ.val).2.2
  have hqP := forcingNegation_subset _ _ _ q hq
  have hqC := T.boundedConditions_condition hqP
  obtain ⟨r, hr, hrq⟩ := hp.2 q hqC ((T.pair_mem_boundedOrder _ _ _).mp hqp).2.2
  obtain ⟨H, hH, hrH⟩ := T.exists_generic (T.forcesMember_condition hr)
  have hqH := hH.1.2.2.1 r hrH q hqC hrq
  have hval := (T.member_truth hH σ τ).mpr ⟨r, hrH, hr⟩
  have hmeet := (T.ofClassName_mem_iff_at hH σ τ (i := i) hσ hτ).mp hval
  exact (genericMeets_negation (T.bounded_preorder i) (T.boundedFilter_generic hH i)
    (atomicMembership_subset _ _ _ _) (atomicMembership_regular (T.bounded_preorder i) σ.val τ.val).2.1).mp
    ⟨q, ⟨hqP, hqH⟩, hq⟩ hmeet

end DefinableForcingTower
end ZFVP
