import ZFVP.ModelTheory.ClassForcingStagedChoices

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

theorem denseClasses_stagedChoices (A : ForcingContext V) {I i j α c : V}
    [IsOrdinal i] [IsOrdinal j] [IsOrdinal α] (hP : A.P = T.P i) (hR : A.R = T.R i)
    (hij : i ⊆ j) (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D)
    (hD : ∀ a ∈ I, ClassForcingDense T.Condition T.LE (D a))
    (hc : c ∈ T.boundedConditions j) (hcG : T.projectCondition i c ∈ A.G)
    (hDC : InternalDependentChoiceAt (A.check α))
    (hclosed : ∀ K : V, IsOrdinal K → i ⊆ K →
      IsForcingClosedThrough (A.projectionQuotient (T.P K) (T.projection i K))
        (forcingSeparativeOrder (A.projectionQuotient (T.P K) (T.projection i K))
          (A.projectionQuotientOrder (T.P K) (T.R K) (T.projection i K))) (A.check α))
    (e : A.Model) (he : e ∈ (A.check I) ^ (A.check α)) :
    let K := T.witnessStageSchedule D hDdef I i j α
    let X := T.boundedQuotient A i K
    let S := forcingSeparativeOrder X (T.boundedQuotientOrder A i K)
    ∃ f, f ∈ X ^ (A.check α) ∧
      (∀ β ∈ A.check α, f ‘ β ∈ (A.check (T.boundedDenseFamily D hDdef I K)) ‘ (e ‘ β)) ∧
      ∃ q ∈ X, ⟨q, A.check c⟩ₖ ∈ S ∧ ∀ β ∈ A.check α, ⟨q, f ‘ β⟩ₖ ∈ S := by
  let F := T.witnessStageSchedule D hDdef I i j
  have hord (β : V) [IsOrdinal β] : IsOrdinal (F β) := T.witnessStageSchedule_ordinal D hDdef I i j β
  have hbase (β : V) [IsOrdinal β] : i ⊆ F β :=
    subset_trans hij (T.witnessStageSchedule_base_subset D hDdef I i j β)
  apply T.quotient_stagedChoices A hP hR D hDdef F
    (T.witnessStageSchedule_definable D hDdef I i j)
    (fun β hβ _ ↦ @hord β hβ) (fun β hβ _ ↦ @hbase β hβ)
    (fun β γ hβ hγ hβγ _ ↦ by
      let := hβ
      let := hγ
      exact T.witnessStageSchedule_mono_le D hDdef I i j hβγ)
    (fun β hβ ↦ by
      have : IsOrdinal β := IsOrdinal.of_mem hβ
      exact T.witnessStageSchedule_successor D hDdef I i j β hD)
    (by simpa only [F, T.witnessStageSchedule_zero] using hc) hcG hDC ?_ e he
  intro β hβ hβα
  let := hβ
  exact hclosed (F β) (hord β) (hbase β) (A.check β) inferInstance
    ((A.checkEmbedding.subset_iff β α).mpr hβα)

end DefinableForcingTower
end ZFVP
