import ZFVP.ModelTheory.WoodinInverseStageBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinIteration.inverse_source {δ θ s K : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hδ : IsWoodinSupercompact δ) (hθ : θ ∈ δ) (h0 : ∅ ∈ θ)
    (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hγ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        (regularCardinalFormula.or limitOfRegularCardinalsFormula)
        (standardTuple ![checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K)]))
    (hDC : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        dependentChoiceAtFormula (standardTuple ![checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K)])) :
    IsWoodinIteration δ (succ θ) (woodinInverseSourceCode θ s K) (woodinInverseCardinalNext θ s K) := by
  obtain ⟨hcδ, hγc, hci, hcode, _, hforce⟩ := h.inverse_sourceStage hδ hθ h0 hlim hγ hDC
  let c := forcingInverseSourceCutoff θ s (woodinLimitCardinal K)
  let z := woodinInverseSourceCode θ s K
  let L := woodinInverseCardinalNext θ s K
  have hnew : L ‘ θ = c := forcingFamilyNext_new _ _ _
  have hold : ∀ i ∈ θ, L ‘ i = K ‘ i := fun _ hi ↦ forcingFamilyNext_old hi
  have hs : IsWoodinStage (woodinIterationStage z L θ) := by
    have ht : θ ∈ succ θ := mem_succ_self θ
    simp only [IsWoodinStage, woodinIterationStage, woodinStagePoset_code,
      woodinStageOrder_code, woodinStageTop_code, woodinStageCardinal_code, hnew]
    refine ⟨hcode.system.order.preorder θ ht, hcode.system.tops.top θ ht,
      forcingInverseSourceCutoff_ordinal _ _ _, ?_, ?_⟩
    · intro p hp
      have hh := hforce p hp
      rw [woodinStageCardinalFormula, forcingFormula_and, mem_inter_iff] at hh
      exact hh.1
    · intro p hp
      have hh := hforce p hp
      rw [woodinStageCardinalFormula, forcingFormula_and, mem_inter_iff] at hh
      exact hh.2
  refine ⟨hcode, forcingFamilyNext_table _ _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact hs
    · rw [woodinInverseSourceCode_old hi]
      exact h.stage i hi
  · intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact h.inverse_sourceStage_small hlim hγc
    · rw [woodinInverseSourceCode_old hi]
      exact h.small i hi
  · intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact hnew.symm ▸ hci
    · exact (hold i hi).symm ▸ h.inaccessible i hi
  · intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact hnew.symm ▸ hcδ
    · exact (hold i hi).symm ▸ h.bounded i hi
  · intro i hi j hj hij
    rcases mem_succ_iff.mp hj with rfl | hj
    · change (L ‘ i) ∈ (L ‘ j)
      rw [hnew, hold i hij]
      let := hci.1
      let := (h.inaccessible i hij).1
      let := h.limitCardinal_ordinal
      exact ordinal_mem_of_subset_mem (h.cardinal_subset_limit hij) hγc
    · have hi' : i ∈ θ := IsOrdinal.toIsTransitive.mem_trans hij hj
      change (L ‘ i) ∈ (L ‘ j)
      rw [hold i hi', hold j hj]
      exact h.increasing i hi' j hj hij

end ZFVP
