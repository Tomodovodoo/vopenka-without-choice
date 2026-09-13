import ZFVP.ModelTheory.TransitiveZFSuccessorColumns
import ZFVP.ModelTheory.WoodinSuccessorRankThreshold

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSuccessorRankThreshold.code_agreement {η ξ s K k : V}
    (h : IsWoodinSuccessorRankThreshold (woodinIterationStage s K k) η)
    (hηξ : η ∈ ξ) (hξ : IsChoicelessInaccessible ξ) :
    letI := hξ.1
    letI := rankDomain_nonempty hξ.2.1
    letI := hξ.rankCriterion.models_zf
    ∀ s' K' k' : SetDomain (hierarchy ξ), s'.val = s → K'.val = K → k'.val = k →
      (woodinIterationSuccessor k' s' K').val = woodinIterationSuccessor k s K ∧
        (woodinIterationCardinalNext k' s' K').val = woodinIterationCardinalNext k s K := by
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let := hierarchy_transitive ξ
  intro s' K' k' hs hK hk
  have hstage : (woodinIterationStage s' K' k').val = woodinIterationStage s K k := by
    rw [TransitiveZF.woodinIterationStage_val, hs, hK, hk]
  have hstep := h.agreement hηξ hξ (woodinIterationStage s' K' k') hstage
  have he : (woodinSuccessorStep (woodinIterationStage s' K' k')).val =
      woodinSuccessorStep (woodinIterationStage s'.val K'.val k'.val) := by
    simpa only [hs, hK, hk] using hstep
  constructor
  · simpa only [hs, hK, hk] using TransitiveZF.woodinIterationSuccessor_val (hierarchy ξ) k' s' K' he
  · simpa only [hs, hK, hk] using TransitiveZF.woodinIterationCardinalNext_val (hierarchy ξ) k' s' K' he

theorem IsWoodinSupercompact.eventually_rank_woodinSuccessorCode_eq {δ s K k : V}
    (hδ : IsWoodinSupercompact δ) (hX : IsWoodinStage (woodinIterationStage s K k))
    (hsmall : IsWoodinStageSmall (woodinIterationStage s K k)) (hκ : K ‘ k ∈ δ) :
    ∃ η ∈ δ, ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      ∀ s' K' k' : SetDomain (hierarchy ξ), s'.val = s → K'.val = K → k'.val = k →
        (woodinIterationSuccessor k' s' K').val = woodinIterationSuccessor k s K ∧
          (woodinIterationCardinalNext k' s' K').val = woodinIterationCardinalNext k s K := by
  have hκ' : woodinStageCardinal (woodinIterationStage s K k) ∈ δ := by
    simpa only [woodinIterationStage, woodinStageCardinal_code] using hκ
  obtain ⟨η, hηδ, ht⟩ := hδ.woodinSuccessorRankThreshold_exists hX hsmall hκ'
  exact ⟨η, hηδ, fun ξ hηξ hξ ↦ ht.code_agreement hηξ hξ⟩

end ZFVP
