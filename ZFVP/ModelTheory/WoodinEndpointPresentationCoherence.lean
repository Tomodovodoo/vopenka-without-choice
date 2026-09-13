import ZFVP.ModelTheory.WoodinLocalPresentation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The actual endpoint carriers agree under external rank restriction. -/
theorem woodinStageCarrier_endpoint_restrict {δ ε z : V}
    (hδ : IsWoodinSupercompact δ) (hε : IsWoodinSupercompact ε)
    (hAC : ¬InternalChoice V) (hδε : δ ⊆ ε) :
    z ∈ woodinStageCarrier δ ↔ z ∈ woodinStageCarrier ε ∧ z ∈ hierarchy δ := by
  let := hδ.inaccessible.1
  let := hε.inaccessible.1
  simp only [woodinStageCarrier, woodinIteration_stage_conditions_local_rank hδ hAC,
    woodinIteration_stage_conditions_local_rank hε hAC]
  exact ⟨fun h ↦ ⟨⟨hierarchy_mono hδε z h.1, h.2⟩, h.1⟩,
    fun h ↦ ⟨h.2, h.1.2⟩⟩

theorem woodinStageCarrier_endpoint_mono {δ ε : V}
    (hδ : IsWoodinSupercompact δ) (hε : IsWoodinSupercompact ε)
    (hAC : ¬InternalChoice V) (hδε : δ ⊆ ε) :
    woodinStageCarrier δ ⊆ woodinStageCarrier ε :=
  fun _ hz ↦ ((woodinStageCarrier_endpoint_restrict hδ hε hAC hδε).mp hz).1

/-- The endpoint order is preserved and reflected by literal inclusion of codes. -/
theorem woodinLocalOrderOn_endpoint_agrees {δ ε z w : V}
    (hδ : IsWoodinSupercompact δ) (hε : IsWoodinSupercompact ε)
    (hAC : ¬InternalChoice V) (hδε : δ ⊆ ε)
    (hz : z ∈ woodinStageCarrier δ) (hw : w ∈ woodinStageCarrier δ) :
    ⟨z, w⟩ₖ ∈ woodinLocalOrderOn (woodinStageCarrier δ) ↔
      ⟨z, w⟩ₖ ∈ woodinLocalOrderOn (woodinStageCarrier ε) := by
  have hz' := woodinStageCarrier_endpoint_mono hδ hε hAC hδε z hz
  have hw' := woodinStageCarrier_endpoint_mono hδ hε hAC hδε w hw
  simp only [mem_woodinLocalOrderOn_iff, hz, hw, hz', hw', true_and]

/-- The smaller endpoint order is exactly the larger order restricted to its rank. -/
theorem woodinLocalOrderOn_endpoint_rank_restrict {δ ε z w : V}
    (hδ : IsWoodinSupercompact δ) (hε : IsWoodinSupercompact ε)
    (hAC : ¬InternalChoice V) (hδε : δ ⊆ ε) :
    ⟨z, w⟩ₖ ∈ woodinLocalOrderOn (woodinStageCarrier δ) ↔
      ⟨z, w⟩ₖ ∈ woodinLocalOrderOn (woodinStageCarrier ε) ∧
        z ∈ hierarchy δ ∧ w ∈ hierarchy δ := by
  simp only [mem_woodinLocalOrderOn_iff, woodinStageCarrier_endpoint_restrict hδ hε hAC hδε]
  tauto

end ZFVP
