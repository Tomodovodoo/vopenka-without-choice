import ZFVP.ModelTheory.WoodinSingletonPrefixCutoff
import ZFVP.ModelTheory.WoodinInitialStage
import ZFVP.ModelTheory.WoodinSeedRankAgreement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinInitialStage_cardinal :
    woodinStageCardinal (woodinInitialStage : V) =
      woodinRestorationCutoff (woodinSeedCardinal : V) := by
  simp only [woodinInitialStage, woodinSeedStage, woodinSuccessorStep_code,
    woodinSuccessorAt, woodinStageCardinal_code, woodinPrefixCutoff_singleton]

theorem IsWoodinSupercompact.eventually_rank_woodinInitialStage_cardinal_eq {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    ∃ η ∈ δ, ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      (woodinStageCardinal (woodinInitialStage : SetDomain (hierarchy ξ))).val =
        woodinStageCardinal (woodinInitialStage : V) := by
  let := hδ.1.1
  obtain ⟨α, hαδ, hseed⟩ := hδ.eventually_rank_woodinSeedCardinal_eq hAC
  obtain ⟨β, hβδ, _, hcut⟩ := hδ.eventually_rank_woodinRestorationCutoff_eq
    woodinSeedCardinal_regular (woodinSeedCardinal_lt hδ) woodinSeedCardinal_DC
  let := IsOrdinal.of_mem hαδ
  let := IsOrdinal.of_mem hβδ
  let : IsOrdinal (α ∪ β) := ordinal_union_ordinal α β
  refine ⟨α ∪ β, ordinal_union_mem hαδ hβδ, ?_⟩
  intro ξ hηξ hξ
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  have hαξ : α ∈ ξ := ordinal_mem_of_subset_mem (subset_union_left α β) hηξ
  have hβξ : β ∈ ξ := ordinal_mem_of_subset_mem (subset_union_right α β) hηξ
  rw [woodinInitialStage_cardinal, woodinInitialStage_cardinal]
  exact hcut ξ hβξ hξ woodinSeedCardinal (hseed ξ hαξ hξ)

end ZFVP
