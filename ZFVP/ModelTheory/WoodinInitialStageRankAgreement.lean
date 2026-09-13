import ZFVP.ModelTheory.WoodinSuccessorStepRankAgreement
import ZFVP.ModelTheory.WoodinInitialStage
import ZFVP.ModelTheory.WoodinSeedRankAgreement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem TransitiveZF.woodinSeedStage_val (U : V) [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hseed : (woodinSeedCardinal : SetDomain U).val = (woodinSeedCardinal : V)) :
    (woodinSeedStage : SetDomain U).val = (woodinSeedStage : V) := by
  simp only [woodinSeedStage, woodinStageCode_val, singleton_val, prod_val, empty_val, hseed]

theorem IsWoodinSupercompact.eventually_rank_woodinInitialStage_eq {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    ∃ η ∈ δ, ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      (woodinInitialStage : SetDomain (hierarchy ξ)).val = (woodinInitialStage : V) := by
  let := hδ.1.1
  obtain ⟨α, hαδ, hseed⟩ := hδ.eventually_rank_woodinSeedCardinal_eq hAC
  have hκδ : woodinStageCardinal (woodinSeedStage : V) ∈ δ := by
    simpa [woodinSeedStage] using woodinSeedCardinal_lt hδ
  obtain ⟨β, hβδ, _, hstep⟩ := hδ.eventually_rank_woodinSuccessorStep_eq
    woodinSeedStage_stage woodinSeedStage_small hκδ
  let := IsOrdinal.of_mem hαδ
  let := IsOrdinal.of_mem hβδ
  let : IsOrdinal (α ∪ β) := ordinal_union_ordinal α β
  refine ⟨α ∪ β, ordinal_union_mem hαδ hβδ, ?_⟩
  intro ξ hηξ hξ
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let := hierarchy_transitive ξ
  have hαξ : α ∈ ξ := ordinal_mem_of_subset_mem (subset_union_left α β) hηξ
  have hβξ : β ∈ ξ := ordinal_mem_of_subset_mem (subset_union_right α β) hηξ
  exact hstep ξ hβξ hξ woodinSeedStage
    (TransitiveZF.woodinSeedStage_val (hierarchy ξ) (hseed ξ hαξ hξ))

end ZFVP
