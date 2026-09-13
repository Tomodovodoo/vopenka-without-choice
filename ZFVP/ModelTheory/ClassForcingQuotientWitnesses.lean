import ZFVP.ModelTheory.ClassForcingQuotientFamily
import ZFVP.ModelTheory.ClassForcingDenseRestriction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

theorem boundedQuotient_preorder (A : ForcingContext V) {i K : V}
    [IsOrdinal i] [IsOrdinal K] (hP : A.P = T.P i) :
    IsForcingPreorder (T.boundedQuotient A i K) (T.boundedQuotientOrder A i K) := by
  apply A.projectionQuotient_preorder
  · rw [hP]
    exact T.boundedProjection_maps i K
  · exact T.bounded_preorder K

/-- Ground witness bounds give an actual transition between two nested
quotient carriers, meeting a checked ground set of witnesses. -/
theorem boundedQuotient_witnessStep (A : ForcingContext V) {i j k K I a : V}
    [IsOrdinal i] [IsOrdinal j] [IsOrdinal k] [IsOrdinal K]
    (hP : A.P = T.P i) (hjK : j ⊆ K) (hkK : k ⊆ K)
    (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D) (ha : a ∈ I)
    (hbound : ∀ c ∈ T.boundedConditions j,
      ∀ r ∈ T.P i, ⟨r, T.projectCondition i c⟩ₖ ∈ T.R i →
        ∃ q ∈ T.boundedConditions k, D a q ∧ T.LE q c ∧ T.LE q ⟨i, r⟩ₖ)
    (hR : A.R = T.R i) :
    ∀ c ∈ T.boundedQuotient A i j, ∃ d ∈ T.boundedQuotient A i k,
      d ∈ (A.check (T.boundedDenseFamily D hDdef I K)) ‘ (A.check a) ∧
      ⟨d, c⟩ₖ ∈ forcingSeparativeOrder (T.boundedQuotient A i K) (T.boundedQuotientOrder A i K) := by
  intro c hc
  have hm : T.boundedProjection i j ∈ A.P ^ T.boundedConditions j := by
    rw [hP]; exact T.boundedProjection_maps i j
  obtain ⟨q, hq, _, rfl⟩ := (A.mem_projectionQuotient_iff hm c).mp hc
  have hqG := ((T.check_mem_boundedQuotient_iff A hP).mp hc).2
  have hG : IsExternalForcingGeneric (T.P i) (T.R i) A.G := by
    rw [← hP, ← hR]; exact A.generic
  obtain ⟨d, hd, hDd, hdq, hdG⟩ := T.projectedWitnessBound_meets_generic
    (D a) (by definability) (hbound q hq) hG hqG
  have hdQ := (T.check_mem_boundedQuotient_iff A hP).mpr ⟨hd, hdG⟩
  have hdK := T.boundedConditions_mono hkK d hd
  have hqK := T.boundedConditions_mono hjK q hq
  have hdQK := T.boundedQuotient_mono A hP hkK _ hdQ
  have hqQK := T.boundedQuotient_mono A hP hjK _ hc
  refine ⟨A.check d, hdQ, ?_, ?_⟩
  · have hf := T.boundedDenseFamily_function D hDdef I K
    let := IsFunction.of_mem hf
    rw [A.check_value (by rw [domain_eq_of_mem_function hf]; exact ha), A.check_mem_iff]
    exact (T.mem_boundedDenseFamily D hDdef ha d).mpr ⟨hdK, hDd⟩
  · apply forcingOrder_subset_separative (T.boundedQuotient_preorder A hP)
    apply (A.projectionQuotientOrder_pair_iff _ _ _ _ _).mpr
    exact ⟨A.check_kpair _ _ ▸ (A.check_mem_iff _ _).mpr
      ((T.pair_mem_boundedOrder K d q).mpr ⟨hdK, hqK, hdq⟩), hdQK, hqQK⟩

end DefinableForcingTower
namespace ForcingContext

noncomputable def checkedFamilyAlong (A : ForcingContext V) (F : V) (α e : A.Model) : A.Model :=
  definableGraph α (fun β ↦ (A.check F) ‘ (e ‘ β)) (by definability)

theorem checkedFamilyAlong_value (A : ForcingContext V) (F : V) {α e β : A.Model}
    (hβ : β ∈ α) : (A.checkedFamilyAlong F α e) ‘ β = (A.check F) ‘ (e ‘ β) :=
  value_definableGraph _ _ _ hβ

end ForcingContext
end ZFVP
