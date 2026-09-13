import ZFVP.ModelTheory.RankLeastDCFailure
import ZFVP.SetTheory.WoodinSmallDCFailure
import ZFVP.SetTheory.ChoicelessInaccessibleRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.eventually_rank_woodinSeedCardinal_eq {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    ∃ η ∈ δ, ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      (woodinSeedCardinal : SetDomain (hierarchy ξ)).val = (woodinSeedCardinal : V) := by
  let κ : V := woodinSeedCardinal
  have hk := woodinSeedCardinal_spec hAC
  obtain ⟨B, hBδ, hc, hD, hκB, ht, hr, hf⟩ :=
    hδ.small_dependentChoice_failure_certificate (woodinSeedCardinal_lt hδ) hk.2.1
  let := hδ.1.1
  have hcκ : B ^ κ ⊆ B := fun f hff ↦ hr.function_mem hc hD hκB
    ((hierarchy_transitive (succ κ)).transitive κ (ordinal_mem_hierarchy_iff.mpr (mem_succ_self κ)))
    ⟨κ, hκB⟩ hff
  have hshort := closedContainer_shortFunctions ht hr hκB hcκ
  refine ⟨rank B, (mem_hierarchy_iff_rank_mem _ _).mp hBδ, ?_⟩
  intro ξ hξB hξ
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  have hBV : B ∈ hierarchy ξ := (mem_hierarchy_iff_rank_mem _ _).mpr hξB
  have hκV := (hierarchy_transitive ξ).mem_trans hκB hBV
  exact rank_woodinSeedCardinal_eq hξ.rankCriterion.2.2.1 ⟨κ, hκV⟩ ⟨B, hBV⟩ hk hf hshort

end ZFVP
