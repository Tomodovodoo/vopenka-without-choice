import ZFVP.ModelTheory.WoodinEndpointDirect
import ZFVP.SetTheory.ForcingDirectLimitFiltration

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinIteration_endpoint_poset {δ : V} (hδ : IsWoodinSupercompact δ)
    (hAC : ¬InternalChoice V) :
    (forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ δ =
      forcingDirectLimit δ (forcingCodeP (woodinIterationPrefix δ))
        (forcingCodeπ (woodinIterationPrefix δ)) (forcingCodeE (woodinIterationPrefix δ))
        (forcingCodeUniverse (woodinIterationPrefix δ)) := by
  rw [woodinIteration_endpoint_direct hδ hAC, kpair.π₁_kpair]
  exact forcingThreadCode_poset _ _ _

theorem woodinIteration_endpoint_section {δ i : V} (hδ : IsWoodinSupercompact δ)
    (hAC : ¬InternalChoice V) (hi : i ∈ δ) :
    (forcingCodeE (kpair.π₁ (woodinIterationRec δ))) ‘ ⟨i, δ⟩ₖ =
      forcingThreadSection δ (forcingCodeP (woodinIterationPrefix δ))
        (forcingCodeπ (woodinIterationPrefix δ)) (forcingCodeE (woodinIterationPrefix δ)) i := by
  rw [woodinIteration_endpoint_direct hδ hAC, kpair.π₁_kpair]
  simp only [forcingDirectCode, forcingThreadCode, forcingIterationCodeNext,
    forcingCodeE_code, forcingMatrixNext_column hi, forcingLimitSectionColumn_value hi]

/-- The endpoint carrier is exactly the union of the earlier section ranges. -/
theorem woodinIteration_endpoint_mem_iff {δ p : V} (hδ : IsWoodinSupercompact δ)
    (hAC : ¬InternalChoice V) :
    p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec δ))) ‘ δ ↔
      ∃ i ∈ δ, p ∈ range ((forcingCodeE (kpair.π₁ (woodinIterationRec δ))) ‘ ⟨i, δ⟩ₖ) := by
  let := hδ.inaccessible.1
  have h := (woodinIterationExit hδ hAC).2.2.1
  rw [woodinIteration_endpoint_poset hδ hAC,
    mem_forcingDirectLimit_iff_section_range h.code.system.split h.code.subset_universe]
  apply exists_congr
  intro i
  apply and_congr_right
  intro hi
  rw [woodinIteration_endpoint_section hδ hAC hi]

theorem woodinIteration_endpoint_ranges_increasing {δ i j : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V)
    (hi : i ∈ δ) (hj : j ∈ δ) (hij : i ⊆ j) :
    range ((forcingCodeE (kpair.π₁ (woodinIterationRec δ))) ‘ ⟨i, δ⟩ₖ) ⊆
      range ((forcingCodeE (kpair.π₁ (woodinIterationRec δ))) ‘ ⟨j, δ⟩ₖ) := by
  let := hδ.inaccessible.1
  have h := (woodinIterationExit hδ hAC).2.2.1
  rw [woodinIteration_endpoint_section hδ hAC hi, woodinIteration_endpoint_section hδ hAC hj]
  exact forcingThreadSection_range_mono h.code.system.split hi hj hij h.code.subset_universe

end ZFVP
