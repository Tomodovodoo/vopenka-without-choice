import ZFVP.ModelTheory.WoodinSparseSourceInvariant

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ForcingCodeExtends.iterationQuotientClosedBelow_iff {θ η s z i j κ : V}
    (he : ForcingCodeExtends s z) (hs : IsForcingIterationCode θ s) (hz : IsForcingIterationCode η z)
    (hi : i ∈ θ) (hj : j ∈ θ) :
    IterationQuotientClosedBelow s i j κ ↔ IterationQuotientClosedBelow z i j κ := by
  unfold IterationQuotientClosedBelow
  rw [hs.tableP.value_of_subset hz.tableP he.subP hi,
    hs.tableR.value_of_subset hz.tableR he.subR hi,
    hs.tablet.value_of_subset hz.tablet he.subt hi,
    hs.tableP.value_of_subset hz.tableP he.subP hj,
    hs.tableR.value_of_subset hz.tableR he.subR hj,
    hs.tableπ.value_of_subset hz.tableπ he.subπ (kpair_mem_iff.mpr ⟨hi, hj⟩)]

variable {Ω θ j : V} [IsOrdinal θ]

theorem woodinSparsePrefixCode_extends_stage
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (hj : j ∈ θ) :
    ForcingCodeExtends (woodinSparseStageCode j) (woodinSparsePrefixCode θ) := by
  let := IsOrdinal.of_mem hj
  have hsub : succ j ⊆ θ := by
    intro k hk
    rcases mem_succ_iff.mp hk with rfl | hk
    · exact hj
    · exact IsOrdinal.toIsTransitive.mem_trans hk hj
  have he := woodinSparsePrefixCode_extends hΩ hAC hθ hsub
  rwa [← woodinSparseStageCode_eq_prefix hΩ hAC (hθ j hj)] at he

theorem woodinSparseStageCode_extends_previous
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (hj : j ∈ θ) :
    ForcingCodeExtends (woodinSparseStageCode j) (woodinSparseStageCode θ) :=
  (woodinSparsePrefixCode_extends_stage hΩ hAC hθ hj).trans (woodinSparseStageCode_extends hΩ hAC hθ)

theorem woodinIterationRec_old_cardinal
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (hj : j ∈ succ θ) :
    (kpair.π₂ (woodinIterationRec θ)) ‘ j = (kpair.π₂ (woodinIterationRec j)) ‘ j := by
  have he := woodinSparseSourceStageCardinals_value hΩ hAC hθ hj
  rwa [woodinSparseSourceStageCardinals, woodinSourceCardinals_stage hj] at he

theorem woodinIterationCardinalPrefix_value
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (hj : j ∈ θ) :
    (woodinIterationCardinalPrefix θ) ‘ j = (kpair.π₂ (woodinIterationRec j)) ‘ j := by
  have he := woodinSparseSourcePrefixCardinals_value hΩ hAC hθ hj
  rwa [woodinSparseSourcePrefixCardinals, woodinSourceCardinals_stage hj] at he

end ZFVP
