import ZFVP.ModelTheory.ClassForcingTowerModel
import ZFVP.ModelTheory.DefinableClassGenericExistence
import ZFVP.SetTheory.AtomicForcingDictionary

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace DefinableForcingTower

variable (T : DefinableForcingTower V)

attribute [local aesop safe (rule_sets := [Definability])] Language.DefinableFunction₄.comp

def ForcesEqual (σ τ p : V) : Prop :=
  ∃ i : V, IsOrdinal i ∧ IsForcingName (T.boundedConditions i) σ ∧
    IsForcingName (T.boundedConditions i) τ ∧
    p ∈ atomicEquality (T.boundedConditions i) (T.boundedOrder i) σ τ

def ForcesMember (σ τ p : V) : Prop :=
  ∃ i : V, IsOrdinal i ∧ IsForcingName (T.boundedConditions i) σ ∧
    IsForcingName (T.boundedConditions i) τ ∧
    p ∈ atomicMembership (T.boundedConditions i) (T.boundedOrder i) σ τ

instance forcesEqual_definable : ℒₛₑₜ-relation₃ T.ForcesEqual := by
  let : ℒₛₑₜ-function₄[V] atomicEquality := atomicEqualityFormula_defined.to_definable
  unfold ForcesEqual
  definability

instance forcesMember_definable : ℒₛₑₜ-relation₃ T.ForcesMember := by
  let : ℒₛₑₜ-function₄[V] atomicMembership := atomicMembershipFormula_defined.to_definable
  unfold ForcesMember
  definability

theorem name_common_bound (σ τ : T.Name) : ∃ i : V, IsOrdinal i ∧
    IsForcingName (T.boundedConditions i) σ.val ∧
    IsForcingName (T.boundedConditions i) τ.val := by
  have := σ.property.bound_ordinal T
  have := τ.property.bound_ordinal T
  let i := taggedNameStageBound σ.val ∪ taggedNameStageBound τ.val
  have : IsOrdinal i := ordinal_union_ordinal _ _
  exact ⟨i, inferInstance,
    (σ.property.bounded T).mono (T.boundedConditions_mono (subset_union_left _ _)),
    (τ.property.bounded T).mono (T.boundedConditions_mono (subset_union_right _ _))⟩

theorem forcesEqual_condition {σ τ p : V} (hp : T.ForcesEqual σ τ p) : T.Condition p := by
  obtain ⟨i, hi, _, _, hp⟩ := hp
  have := hi
  exact T.boundedConditions_condition (atomicEquality_subset _ _ _ _ p hp)

theorem forcesMember_condition {σ τ p : V} (hp : T.ForcesMember σ τ p) : T.Condition p := by
  obtain ⟨i, hi, _, _, hp⟩ := hp
  have := hi
  exact T.boundedConditions_condition (atomicMembership_subset _ _ _ _ p hp)

variable {G : Set V} (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)

theorem equal_truth (σ τ : T.Name) :
    T.ofClassName hG σ = T.ofClassName hG τ ↔ ∃ p ∈ G, T.ForcesEqual σ.val τ.val p := by
  constructor
  · intro he
    obtain ⟨i, hi, hσ, hτ⟩ := T.name_common_bound σ τ
    have := hi
    have hstage := (T.ofClassName_eq_iff_at hG σ τ hσ hτ).mp he
    obtain ⟨p, hpG, hp⟩ := (forcingQuotientMk_eq_iff _ _ _ _ _ _ _).mp hstage
    exact ⟨p, hpG.2, i, hi, hσ, hτ, hp⟩
  · rintro ⟨p, hpG, i, hi, hσ, hτ, hp⟩
    have := hi
    apply (T.ofClassName_eq_iff_at hG σ τ hσ hτ).mpr
    exact (forcingQuotientMk_eq_iff _ _ _ _ _ _ _).mpr
      ⟨p, ⟨atomicEquality_subset _ _ _ _ p hp, hpG⟩, hp⟩

theorem member_truth (σ τ : T.Name) :
    T.ofClassName hG σ ∈ T.ofClassName hG τ ↔ ∃ p ∈ G, T.ForcesMember σ.val τ.val p := by
  constructor
  · intro hm
    obtain ⟨i, hi, hσ, hτ⟩ := T.name_common_bound σ τ
    have := hi
    obtain ⟨p, hpG, hp⟩ := (T.ofClassName_mem_iff_at hG σ τ hσ hτ).mp hm
    exact ⟨p, hpG.2, i, hi, hσ, hτ, hp⟩
  · rintro ⟨p, hpG, i, hi, hσ, hτ, hp⟩
    have := hi
    apply (T.ofClassName_mem_iff_at hG σ τ hσ hτ).mpr
    exact ⟨p, ⟨atomicMembership_subset _ _ _ _ p hp, hpG⟩, hp⟩

omit hG in
theorem forcesEqual_at_iff [Countable V] {σ τ p i : V} [IsOrdinal i]
    (hσ : IsForcingName (T.boundedConditions i) σ)
    (hτ : IsForcingName (T.boundedConditions i) τ) (hp : p ∈ T.boundedConditions i) :
    T.ForcesEqual σ τ p ↔ p ∈ atomicEquality (T.boundedConditions i) (T.boundedOrder i) σ τ := by
  constructor
  · intro he
    by_contra hn
    obtain ⟨q, hq, hqp⟩ := exists_forcingNegation_of_not_mem hp hn
      (atomicEquality_regular (T.bounded_preorder i) σ τ).2.2
    have hqP := forcingNegation_subset _ _ _ q hq
    obtain ⟨H, hH, hqH⟩ := T.exists_generic (T.boundedConditions_condition hqP)
    have hpH := hH.1.2.2.1 q hqH p (T.boundedConditions_condition hp)
      ((T.pair_mem_boundedOrder _ _ _).mp hqp).2.2
    let σn : T.Name := ⟨σ, T.isName_of_bounded (θ := i) hσ⟩
    let τn : T.Name := ⟨τ, T.isName_of_bounded (θ := i) hτ⟩
    have hval := (T.equal_truth hH σn τn).mpr ⟨p, hpH, he⟩
    have hs := (T.ofClassName_eq_iff_at hH σn τn (i := i) hσ hτ).mp hval
    have hmeet := (forcingQuotientMk_eq_iff _ _ _ _ _ _ _).mp hs
    exact (genericMeets_negation (T.bounded_preorder i) (T.boundedFilter_generic hH i)
      (atomicEquality_subset _ _ _ _) (atomicEquality_regular (T.bounded_preorder i) σ τ).2.1).mp
      ⟨q, ⟨hqP, hqH⟩, hq⟩ hmeet
  · exact fun he ↦ ⟨i, inferInstance, hσ, hτ, he⟩

omit hG in
theorem forcesMember_at_iff [Countable V] {σ τ p i : V} [IsOrdinal i]
    (hσ : IsForcingName (T.boundedConditions i) σ)
    (hτ : IsForcingName (T.boundedConditions i) τ) (hp : p ∈ T.boundedConditions i) :
    T.ForcesMember σ τ p ↔ p ∈ atomicMembership (T.boundedConditions i) (T.boundedOrder i) σ τ := by
  constructor
  · intro hm
    by_contra hn
    obtain ⟨q, hq, hqp⟩ := exists_forcingNegation_of_not_mem hp hn
      (atomicMembership_regular (T.bounded_preorder i) σ τ).2.2
    have hqP := forcingNegation_subset _ _ _ q hq
    obtain ⟨H, hH, hqH⟩ := T.exists_generic (T.boundedConditions_condition hqP)
    have hpH := hH.1.2.2.1 q hqH p (T.boundedConditions_condition hp)
      ((T.pair_mem_boundedOrder _ _ _).mp hqp).2.2
    let σn : T.Name := ⟨σ, T.isName_of_bounded (θ := i) hσ⟩
    let τn : T.Name := ⟨τ, T.isName_of_bounded (θ := i) hτ⟩
    have hval := (T.member_truth hH σn τn).mpr ⟨p, hpH, hm⟩
    have hmeet := (T.ofClassName_mem_iff_at hH σn τn (i := i) hσ hτ).mp hval
    exact (genericMeets_negation (T.bounded_preorder i) (T.boundedFilter_generic hH i)
      (atomicMembership_subset _ _ _ _) (atomicMembership_regular (T.bounded_preorder i) σ τ).2.1).mp
      ⟨q, ⟨hqP, hqH⟩, hq⟩ hmeet
  · exact fun hm ↦ ⟨i, inferInstance, hσ, hτ, hm⟩

end DefinableForcingTower
end ZFVP
