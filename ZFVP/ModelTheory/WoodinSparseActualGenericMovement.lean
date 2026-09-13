import ZFVP.ModelTheory.WoodinSparseSourceRelativeHomogeneity
import ZFVP.ModelTheory.WoodinSparseSourceSubgeneric
import ZFVP.ModelTheory.RelativeAutomorphismGeneric

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "P[" θ "]" => (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ)
local notation "R[" θ "]" => (forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ)
local notation "π[" i "," θ "]" => (forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex θ⟩ₖ

theorem woodinSparseSource_move_generic {Ω δ t : V} [IsOrdinal δ] {G : Set V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hδ : δ ∈ Ω)
    (hG : IsExternalForcingGeneric P[Ω] R[Ω] G) (ht : t ∈ P[Ω])
    (htG : π[δ,Ω] ‘ t ∈ forcingProjectionGeneric P[δ] R[δ] π[δ,Ω] G) :
    ∃ f, IsForcingAutomorphism P[Ω] R[Ω] f ∧
      IsExternalForcingGeneric P[Ω] R[Ω] (forcingProjectionGeneric P[Ω] R[Ω] f G) ∧
      t ∈ forcingProjectionGeneric P[Ω] R[Ω] f G ∧
      forcingProjectionGeneric P[δ] R[δ] π[δ,Ω] (forcingProjectionGeneric P[Ω] R[Ω] f G) =
        forcingProjectionGeneric P[δ] R[δ] π[δ,Ω] G ∧
      forcingProjectionGeneric P[Ω] R[Ω] (converseGraph f) (forcingProjectionGeneric P[Ω] R[Ω] f G) = G := by
  let := hΩ.inaccessible.1
  have hsδ := IsOrdinal.toIsTransitive.transitive _ hδ
  have hR := (woodinSparseSourceStageCode_valid hΩ hAC (subset_refl Ω)).system.order.preorder
    (woodinSourceIndex Ω) (mem_succ_self _)
  have hS := (woodinSparseSourceStageCode_valid hΩ hAC hsδ).system.order.preorder
    (woodinSourceIndex δ) (mem_succ_self _)
  exact externalGeneric_relative_movement_of_homogeneity hR hS
    (woodinSparseSourceStage_splitProjection_to_row hΩ hAC (subset_refl Ω) hδ) hG ht htG
    (fun _ hp hle ↦ woodinSparseSource_relative_homogeneous hΩ hAC hsδ hp ht hle)

end ZFVP
