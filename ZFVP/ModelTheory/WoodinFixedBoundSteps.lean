import ZFVP.SetTheory.ForcingBoundCodeExtension
import ZFVP.ModelTheory.WoodinSuccessorBoundSections
import ZFVP.ModelTheory.WoodinLimitBoundTable

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinIteration.successor_bound_step_fixed {δ k s K η z B i I : V} [IsOrdinal k]
    (hδ : IsWoodinSupercompact δ) (h : IsWoodinIteration δ (succ k) s K)
    (hz : IsForcingIterationCode η z) (he : ForcingCodeExtends (woodinIterationSuccessor k s K) z)
    (hi : i ∈ succ k) (hI : I ∈ K ‘ i) (ht : IsIterationTable (succ k) B)
    (hb : IsCoherentForcingBound (succ k) (forcingCodeP z) (forcingCodeR z) (forcingCodeπ z) B i I)
    (hc : IsSectionCompatibleForcingBound (succ k) (forcingCodeP z) (forcingCodeR z) (forcingCodeπ z)
      (forcingCodeE z) B i I) :
    let C := woodinSuccessorBoundTable k s K B i I
    IsIterationTable (succ (succ k)) C ∧
    IsCoherentForcingBound (succ (succ k)) (forcingCodeP z) (forcingCodeR z) (forcingCodeπ z) C i I ∧
    IsSectionCompatibleForcingBound (succ (succ k)) (forcingCodeP z) (forcingCodeR z)
      (forcingCodeπ z) (forcingCodeE z) C i I ∧ B ⊆ C := by
  have hold := (woodinIterationSuccessor_extends h.code K).trans he
  have hb' := (hold.bound_iff h.code hz hi).mpr hb
  have hc' := (hold.bound_sectionCompatible_iff h.code hz hi).mpr hc
  have hnew := (h.successor hδ).code
  have hi' : i ∈ succ (succ k) := mem_succ_iff.mpr (Or.inr hi)
  refine ⟨forcingFamilyNext_table _ _ _, ?_, ?_, forcingFamilyNext_extends ht _⟩
  · exact (he.bound_iff hnew hz hi').mp (h.successor_bound_table hδ hi hI hb')
  · exact (he.bound_sectionCompatible_iff hnew hz hi').mp
      (h.successor_bound_table_sectionCompatible hδ hi hI hb' hc')

theorem IsWoodinIteration.limitBase_bound_step_fixed {δ θ s K η z B i I : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hlim : ∀ j ∈ θ, succ j ∈ θ) (h0 : ∅ ∈ θ)
    (hz : IsForcingIterationCode η z) (he : ForcingCodeExtends (woodinLimitBase θ s K) z)
    (hi : i ∈ θ) (hI : I ∈ K ‘ i) (ht : IsIterationTable θ B)
    (hb : IsCoherentForcingBound θ (forcingCodeP z) (forcingCodeR z) (forcingCodeπ z) B i I)
    (hc : IsSectionCompatibleForcingBound θ (forcingCodeP z) (forcingCodeR z) (forcingCodeπ z)
      (forcingCodeE z) B i I) :
    let C := woodinLimitBaseBoundTable θ s K B i I
    IsIterationTable (succ θ) C ∧
    IsCoherentForcingBound (succ θ) (forcingCodeP z) (forcingCodeR z) (forcingCodeπ z) C i I ∧
    IsSectionCompatibleForcingBound (succ θ) (forcingCodeP z) (forcingCodeR z)
      (forcingCodeπ z) (forcingCodeE z) C i I ∧ B ⊆ C := by
  classical
  have hold := (woodinLimitBase_extends h.code K).trans he
  have hb' := (hold.bound_iff h.code hz hi).mpr hb
  have hc' := (hold.bound_sectionCompatible_iff h.code hz hi).mpr hc
  have hnew := woodinLimitBase_valid (K := K) h.code h0
  have hi' : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  have hn := h.limitBase_bound_table hlim hi hI hb' hc'
  refine ⟨?_, (he.bound_iff hnew hz hi').mp hn.1,
    (he.bound_sectionCompatible_iff hnew hz hi').mp hn.2, ?_⟩
  · unfold woodinLimitBaseBoundTable
    split <;> exact forcingFamilyNext_table _ _ _
  · unfold woodinLimitBaseBoundTable
    split <;> exact forcingFamilyNext_extends ht _

end ZFVP
