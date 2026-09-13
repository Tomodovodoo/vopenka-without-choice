import ZFVP.ModelTheory.WoodinInitialStageRankAgreement
import ZFVP.ModelTheory.TransitiveZFIterationHistory

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem TransitiveZF.woodinInitialCode_val (U : V) [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hstage : (woodinInitialStage : SetDomain U).val = (woodinInitialStage : V)) :
    (woodinInitialCode : SetDomain U).val = (woodinInitialCode : V) ∧
      (woodinInitialCardinals : SetDomain U).val = (woodinInitialCardinals : V) := by
  constructor
  · simp only [woodinInitialCode, forcingInitialCode_val U, woodinStagePoset_val U,
      woodinStageOrder_val U, woodinStageTop_val U, hstage]
  · simp only [woodinInitialCardinals, forcingFamilyNext_val U, empty_val U,
      woodinStageCardinal_val U, hstage]

theorem IsWoodinSupercompact.eventually_rank_woodinInitialCode_eq {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    ∃ η ∈ δ, ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      (woodinInitialCode : SetDomain (hierarchy ξ)).val = (woodinInitialCode : V) ∧
        (woodinInitialCardinals : SetDomain (hierarchy ξ)).val = (woodinInitialCardinals : V) := by
  obtain ⟨η, hηδ, hall⟩ := hδ.eventually_rank_woodinInitialStage_eq hAC
  refine ⟨η, hηδ, ?_⟩
  intro ξ hηξ hξ
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let := hierarchy_transitive ξ
  exact TransitiveZF.woodinInitialCode_val (hierarchy ξ) (hall ξ hηξ hξ)

end ZFVP
