import ZFVP.ModelTheory.ClassForcingPretameness
import ZFVP.SetTheory.Collection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

/-- A set of tagged conditions is contained in a bounded part of the tower.
The ordinal bound is computed from its rank and requires no choice. -/
theorem conditionSet_rank_bound {B c : V} (hcB : c ∈ B) (hc : T.Condition c) :
    c ∈ T.boundedConditions (rank B) := by
  obtain ⟨i, p, hi, hp, rfl⟩ := hc
  let := hi
  have hiB : i ∈ rank B := by
    have h := IsOrdinal.toIsTransitive.mem_trans (rank_kpair_left_lt i p) (rank_mem hcB)
    simpa only [rank_of_ordinal i] using h
  exact T.tagged_mem_boundedConditions
    (IsOrdinal.toIsTransitive.transitive _ hiB) hp

/-- Collection bounds all positive instances of a definable witness search
on a set of inputs. No witness function, and hence no internal choice, is used. -/
theorem classConditionWitnessBound (I S : V) (A : V → V → V → Prop)
    (hA : ℒₛₑₜ-relation₃ A) :
    ∃ θ : V, IsOrdinal θ ∧ ∀ i ∈ I, ∀ p ∈ S,
      (∃ q, T.Condition q ∧ A i p q) →
        ∃ q ∈ T.boundedConditions θ, A i p q := by
  let J : V := {z ∈ I ×ˢ S ; ∃ q, T.Condition q ∧ A (kpair.π₁ z) (kpair.π₂ z) q}
  obtain ⟨B, hB⟩ := collection J
    (fun z q ↦ T.Condition q ∧ A (kpair.π₁ z) (kpair.π₂ z) q) (by definability)
    (fun z hz ↦ (mem_sep_iff.mp hz).2)
  refine ⟨rank B, inferInstance, ?_⟩
  intro i hi p hp hex
  have hz : ⟨i, p⟩ₖ ∈ J := by
    simpa only [J, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair] using ⟨⟨hi, hp⟩, hex⟩
  obtain ⟨q, hqB, hqC, hq⟩ := hB ⟨i, p⟩ₖ hz
  exact ⟨q, T.conditionSet_rank_bound hqB hqC, by simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using hq⟩

/-- A fixed bounded set of inputs admits witnesses from one later set stage
for every member of a set-indexed family of dense classes. This does not
assert that the dense classes are definable in an intermediate extension. -/
theorem denseClasses_stageWitnessBound (D : V → V → Prop)
    (hDdef : ℒₛₑₜ-relation D) (I j : V) [IsOrdinal j]
    (hD : ∀ i ∈ I, ClassForcingDense T.Condition T.LE (D i)) :
    ∃ k : V, IsOrdinal k ∧ j ⊆ k ∧ ∀ i ∈ I, ∀ p ∈ T.boundedConditions j,
      ∃ q ∈ T.boundedConditions k, D i q ∧ T.LE q p := by
  obtain ⟨θ, hθ, hθB⟩ := T.classConditionWitnessBound I (T.boundedConditions j)
    (fun i p q ↦ D i q ∧ T.LE q p) (by definability)
  let := hθ
  have : IsOrdinal (j ∪ θ) := ordinal_union_ordinal _ _
  refine ⟨j ∪ θ, inferInstance, subset_union_left _ _, ?_⟩
  intro i hi p hp
  obtain ⟨q, hq, hqp⟩ := (hD i hi).2 p (T.boundedConditions_condition hp)
  obtain ⟨r, hr, hri, hrp⟩ := hθB i hi p hp ⟨q, (hD i hi).1 q hq, hq, hqp⟩
  exact ⟨r, T.boundedConditions_mono (subset_union_right _ _) r hr, hri, hrp⟩

/-- The bound also covers every strengthening in a fixed base forcing.
This extra quantifier makes the resulting set usable in every base generic. -/
theorem denseClasses_projectedWitnessBound (D : V → V → Prop)
    (hDdef : ℒₛₑₜ-relation D) (I S i : V) [IsOrdinal i]
    (hD : ∀ a ∈ I, ClassForcingDense T.Condition T.LE (D a)) :
    ∃ k : V, IsOrdinal k ∧ ∀ a ∈ I, ∀ c ∈ S, T.Condition c →
      ∀ r ∈ T.P i, ⟨r, T.projectCondition i c⟩ₖ ∈ T.R i →
        ∃ q ∈ T.boundedConditions k, D a q ∧ T.LE q c ∧ T.LE q ⟨i, r⟩ₖ := by
  obtain ⟨k, hk, hbound⟩ := T.classConditionWitnessBound I (S ×ˢ T.P i)
    (fun a z q ↦ D a q ∧ T.LE q (kpair.π₁ z) ∧ T.LE q ⟨i, kpair.π₂ z⟩ₖ)
    (by definability)
  refine ⟨k, hk, ?_⟩
  intro a ha c hcS hc r hr hrc
  obtain ⟨d, hd, hdc, hdr⟩ := T.lift_stage_condition hc hr hrc
  obtain ⟨q, hqa, hqd⟩ := (hD a ha).2 d hd
  have hex : ∃ q, T.Condition q ∧ D a q ∧ T.LE q c ∧ T.LE q ⟨i, r⟩ₖ :=
    ⟨q, (hD a ha).1 q hqa, hqa, T.le_trans hqd hdc, T.le_trans hqd hdr⟩
  have hz : ⟨c, r⟩ₖ ∈ S ×ˢ T.P i := kpair_mem_iff.mpr ⟨hcS, hr⟩
  simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using
    hbound a ha ⟨c, r⟩ₖ hz (by simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using hex)

/-- A bounded witness table satisfying the ground projection condition is
met in every base generic containing the input projection. All dense sets
used here belong to the ground model. -/
theorem projectedWitnessBound_meets_generic (D : V → Prop)
    (hDdef : ℒₛₑₜ-predicate D) {i k c : V} [IsOrdinal i] [IsOrdinal k]
    (hb : ∀ r ∈ T.P i, ⟨r, T.projectCondition i c⟩ₖ ∈ T.R i →
      ∃ q ∈ T.boundedConditions k, D q ∧ T.LE q c ∧ T.LE q ⟨i, r⟩ₖ)
    {G : Set V} (hG : IsExternalForcingGeneric (T.P i) (T.R i) G)
    (hcG : T.projectCondition i c ∈ G) :
    ∃ q ∈ T.boundedConditions k, D q ∧ T.LE q c ∧ T.projectCondition i q ∈ G := by
  let E : V := {r ∈ T.P i ; ∃ q ∈ T.boundedConditions k,
    D q ∧ T.LE q c ∧ T.projectCondition i q = r}
  have hE : ForcingDenseBelow (T.P i) (T.R i) E (T.projectCondition i c) := by
    refine ⟨fun r hr ↦ (mem_sep_iff.mp hr).1, ?_⟩
    intro r hr hrc
    obtain ⟨q, hq, hDq, hqc, hqr⟩ := hb r hr hrc
    have hqC := T.boundedConditions_condition hq
    refine ⟨T.projectCondition i q, ?_, (T.below_stage_iff hqC hr).mp hqr⟩
    exact mem_sep_iff.mpr ⟨T.projectCondition_mem hqC, q, hq, hDq, hqc, rfl⟩
  obtain ⟨r, hrG, hrE⟩ := externalForcingGeneric_meets_denseBelow (T.order i inferInstance) hG hcG hE
  obtain ⟨q, hq, hDq, hqc, hqr⟩ := (mem_sep_iff.mp hrE).2
  exact ⟨q, hq, hDq, hqc, hqr.symm ▸ hrG⟩

end DefinableForcingTower
end ZFVP
