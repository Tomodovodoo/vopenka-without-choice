import ZFVP.ModelTheory.WoodinSparseHomogeneityGlobalBuilder

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω δ p q : V} [IsOrdinal δ]
local notation "c" => woodinSparseStageCode Ω

theorem woodinSparseStage_relative_homogeneous
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hδ : δ ⊆ Ω)
    (hp : p ∈ (forcingCodeP c) ‘ Ω) (hq : q ∈ (forcingCodeP c) ‘ Ω)
    (hle : ⟨((forcingCodeπ c) ‘ ⟨δ,Ω⟩ₖ) ‘ p,((forcingCodeπ c) ‘ ⟨δ,Ω⟩ₖ) ‘ q⟩ₖ
      ∈ (forcingCodeR (woodinSparseStageCode δ)) ‘ δ) :
    ∃ f, IsForcingAutomorphism ((forcingCodeP c) ‘ Ω) ((forcingCodeR c) ‘ Ω) f ∧
      (∀ z ∈ (forcingCodeP c) ‘ Ω,
        ((forcingCodeπ c) ‘ ⟨δ,Ω⟩ₖ) ‘ (f ‘ z) = ((forcingCodeπ c) ‘ ⟨δ,Ω⟩ₖ) ‘ z) ∧
      ForcingCompatible ((forcingCodeP c) ‘ Ω) ((forcingCodeR c) ‘ Ω) (f ‘ p) q := by
  let := hΩ.inaccessible.1
  let a := woodinSparseEndpointThread Ω p
  let b := woodinSparseEndpointThread Ω q
  let G := woodinSparseHomogeneityRow δ a b
  have hG : ℒₛₑₜ-function₃ G := woodinSparseHomogeneityRow_definable δ a b
  have hδ' : δ ∈ succ Ω := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hδ)
  have hle' : ⟨a ‘ δ,b ‘ δ⟩ₖ ∈ (forcingCodeR c) ‘ δ := by
    rw [woodinSparseEndpointThread_value hδ', woodinSparseEndpointThread_value hδ',
      ← (woodinSparseStageCode_endpoint_row_values hΩ hAC hδ).2.1]
    exact hle
  let F := coherentAutomorphismWitnessBuilder G
  have hF : ℒₛₑₜ-function₁ F := coherentAutomorphismWitnessBuilder_definable G hG
  let H := automorphismWitnessMaps (coherentAutomorphismHistory F hF (succ Ω))
  let W := automorphismWitnessBounds (coherentAutomorphismHistory F hF (succ Ω))
  have hc := woodinSparseStageCode_endpoint_valid hΩ hAC
  have hh : IsCoherentAutomorphismWitnessHistory (succ Ω) c a b δ H W :=
    coherentAutomorphismWitnessRec_family_of_builder G hG hc
      (woodinSparseHomogeneityRow_spec hΩ hAC hδ hp hq hle') (subset_refl _)
  refine ⟨H ‘ Ω, hh.automorphism.iso Ω (mem_succ_self Ω), ?_, ?_⟩
  · intro z hz
    exact hh.relative_projection hc (mem_succ_self Ω) hδ' hδ hz
  · have h := hh.compatible (mem_succ_self Ω)
    have ha : a ‘ Ω = p := woodinSparseEndpointThread_self hΩ hAC hp
    have hb : b ‘ Ω = q := woodinSparseEndpointThread_self hΩ hAC hq
    rwa [ha,hb] at h

end ZFVP
