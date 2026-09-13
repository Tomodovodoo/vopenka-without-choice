import ZFVP.ModelTheory.LowNameCoverageTransport
import ZFVP.ModelTheory.WoodinSparseGenericContext

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ η Q π : V} [IsOrdinal θ]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
  {G : Set V} (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec θ))) ‘ θ) G)

local notation "A" => woodinIterationGenericContext hΩ hAC hθ hG
local notation "B" => woodinSparseGenericContext hΩ hAC hθ hG

theorem woodinSparseGenericContext_low_name_coverage_of_local
    (hη : IsChoicelessInaccessible η)
    (hπ : π ∈ ((forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ) ^ Q)
    (hB : (forcingCodeP (woodinSparseStageCode θ)) ‘ θ ⊆ hierarchy η)
    (hcov : (A).HasLocalLowNameCoverage η Q π) :
    ∀ x ∈ hierarchy ((B).check η), ∃ τ : ForcingName (B).P,
      τ.val ∈ hierarchy η ∧ x = (B).ofName τ :=
  (A).low_name_coverage_of_local_equiv B hη hπ
    (woodinSparseRealizationMap_projection hΩ hAC hθ).maps hB
    (woodinSparseGenericModelEquiv hΩ hAC hθ hG)
    (woodinSparseGenericModelEquiv_mem hΩ hAC hθ hG)
    (woodinSparseGenericModelEquiv_check hΩ hAC hθ hG)
    (woodinSparseGenericModelEquiv_name hΩ hAC hθ hG) hcov

end ZFVP
