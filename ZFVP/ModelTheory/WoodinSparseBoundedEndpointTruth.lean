import ZFVP.ModelTheory.WoodinSparseBoundedEndpointComparison
import ZFVP.ModelTheory.WoodinSparseEndpointTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω : V} [IsOrdinal Ω]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G)
local notation "E" => woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG

/-- Bounded truth at the actual endpoint is witnessed by the strictly earlier
prefix definition, with no endpoint forcing set supplied to that definition. -/
theorem woodinSparse_endpoint_boundedPrefix_truth {n φ b : V}
    (hφ : IsBoundedFormulaCode n φ) (hb : b ∈ lowRankNameSet (E).P Ω ^ n) :
    MembershipSatisfies (hierarchy ((E).check Ω)) ((E).check n) ((E).check φ)
      ((E).sequenceValue b ((E).nameSequence_of_mem_function ((E).lowRankNameSet_names Ω) hb)) ↔
      ∃ p ∈ (E).G, WoodinSparseBoundedPrefixForces Ω n φ b p := by
  rw [woodinSparseGenericContext_endpoint_internalGenericTruth hΩ hAC hG
    (boundedFormulaFamily_subset _ hφ) hb]
  change (∃ p ∈ (E).G, p ∈ internalForcingSet (E).P (E).R (lowRankNameSet (E).P Ω) n φ b) ↔ _
  apply exists_congr
  intro p
  apply and_congr_right
  intro hp
  exact (woodinSparse_boundedPrefixForces_iff hΩ hAC hφ hb ((E).generic.1.1 p hp)).symm

end ZFVP
