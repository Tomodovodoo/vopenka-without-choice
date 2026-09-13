import ZFVP.ModelTheory.WoodinSparseRetractions

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ i : V} [IsOrdinal θ] [IsOrdinal i]
local notation "RawP" => (forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ
local notation "RawR" => (forcingCodeR (kpair.π₁ (woodinIterationRec θ))) ‘ θ
local notation "RawPi" => (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i
local notation "RawRi" => (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i
local notation "RawProj" => (forcingCodeπ (kpair.π₁ (woodinIterationRec θ))) ‘ ⟨i, θ⟩ₖ
local notation "P" => (forcingCodeP (woodinSparseStageCode θ)) ‘ θ
local notation "R" => (forcingCodeR (woodinSparseStageCode θ)) ‘ θ
local notation "Pi" => (forcingCodeP (woodinSparseStageCode i)) ‘ i
local notation "Ri" => (forcingCodeR (woodinSparseStageCode i)) ‘ i
local notation "Proj" => (forcingCodeπ (woodinSparseStageCode θ)) ‘ ⟨i, θ⟩ₖ

theorem woodinSparseGeneric_projected
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hi : i ∈ θ) {G : Set V} (hG : IsExternalForcingFilter RawP RawR G) :
    woodinSparseGeneric i (forcingProjectionGeneric RawPi RawRi RawProj G) =
      forcingProjectionGeneric Pi Ri Proj (woodinSparseGeneric θ G) := by
  have hiΩ : i ⊆ Ω := fun x hx ↦ hθ x (IsOrdinal.toIsTransitive.mem_trans hx hi)
  have hraw := woodinIterationStage_projection_to_row hΩ hAC hθ hi
  have hsparse := woodinSparseStage_projection_to_row hΩ hAC hθ hi
  have hmi := woodinSparseRealizationMap_projection hΩ hAC hiΩ
  have hmt := woodinSparseRealizationMap_projection hΩ hAC hθ
  have hRi := (woodinSparseStageCode_valid hΩ hAC hiΩ).system.order.preorder i (mem_succ_self i)
  have hRt := (woodinSparseStageCode_valid hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ)
  have hrRi := (woodinIterationStageCode_valid_le hΩ hAC hiΩ).system.order.preorder i (mem_succ_self i)
  have hmaps : compose RawProj (woodinSparseRealizationMap i) =
      compose (woodinSparseRealizationMap θ) Proj := by
    have hf := compose_function hraw.maps hmi.maps
    have hg := compose_function hmt.maps hsparse.maps
    let := IsFunction.of_mem hf
    let := IsFunction.of_mem hg
    apply functions_eq_of_domain_values
    · rw [domain_eq_of_mem_function hf, domain_eq_of_mem_function hg]
    · intro p hp
      rw [domain_eq_of_mem_function hf] at hp
      rw [value_compose_of_mem_function hraw.maps hmi.maps hp,
        value_compose_of_mem_function hmt.maps hsparse.maps hp,
        woodinSparseStageCode_projection hΩ hAC hθ hi (function_value_mem hmt.maps hp),
        woodinSparseRealizationMap_restrict hΩ hAC hθ hi hp]
  unfold woodinSparseGeneric
  rw [forcingProjectionGeneric_comp hmi hraw hRi hrRi hG,
    forcingProjectionGeneric_comp hsparse hmt hRi hRt hG, hmaps]

end ZFVP
