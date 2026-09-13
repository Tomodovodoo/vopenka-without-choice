import ZFVP.ModelTheory.WoodinSparseCapturedGenericImage

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparseSourceStage_old_row {θ i : V} [IsOrdinal θ] (hi : i ∈ succ θ) :
    (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex i) =
      (forcingCodeP (woodinSparseSourceStageCode i)) ‘ (woodinSourceIndex i) ∧
    (forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex i) =
      (forcingCodeR (woodinSparseSourceStageCode i)) ‘ (woodinSourceIndex i) := by
  let := IsOrdinal.of_mem hi
  rw [(woodinSparseSourceStageCode_row hi).1, (woodinSparseSourceStageCode_row hi).2,
    (woodinSparseSourceStageCode_row (mem_succ_self i)).1,
    (woodinSparseSourceStageCode_row (mem_succ_self i)).2]
  exact woodinSparseStage_old_row hi

theorem woodinSparseSourceStage_splitProjection_to_row {Ω θ i : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (hi : i ∈ θ) :
    IsForcingSplitProjection
      ((forcingCodeP (woodinSparseSourceStageCode i)) ‘ (woodinSourceIndex i))
      ((forcingCodeR (woodinSparseSourceStageCode i)) ‘ (woodinSourceIndex i))
      ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
      ((forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
      ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex θ⟩ₖ)
      ((forcingCodeE (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex θ⟩ₖ) := by
  let := IsOrdinal.of_mem hi
  have hi' := mem_succ_iff.mpr (Or.inr hi)
  rw [← (woodinSparseSourceStage_old_row hi').1, ← (woodinSparseSourceStage_old_row hi').2]
  have his : woodinSourceIndex i ∈ woodinSourceIndex θ := woodinSourceIndex_mem_iff.mpr hi
  exact (woodinSparseSourceStageCode_valid hΩ hAC hθ).system.splitProjection
    (mem_succ_iff.mpr (Or.inr his)) (mem_succ_self _) (IsOrdinal.toIsTransitive.transitive _ his)

theorem woodinSparseSourceStage_projectedFilter_subset {Ω θ i : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (hi : i ∈ θ)
    {G : Set V} (hG : IsExternalForcingFilter
      ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
      ((forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ)) G) :
    forcingProjectionGeneric
      ((forcingCodeP (woodinSparseSourceStageCode i)) ‘ (woodinSourceIndex i))
      ((forcingCodeR (woodinSparseSourceStageCode i)) ‘ (woodinSourceIndex i))
      ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex θ⟩ₖ) G ⊆ G := by
  let := IsOrdinal.of_mem hi
  have hsubi : i ⊆ Ω := fun x hx ↦ hθ x (IsOrdinal.toIsTransitive.mem_trans hx hi)
  intro p hp
  have hs := woodinSparseSourceStage_splitProjection_to_row hΩ hAC hθ hi
  have hm := (hs.generic_iff_section
    ((woodinSparseSourceStageCode_valid hΩ hAC hsubi).system.order.preorder _ (mem_succ_self _)) hG hp.1).mp hp
  rw [woodinSparseSourceStageCode_section hΩ hAC hθ hi (by
    rw [(woodinSparseSourceStage_old_row (mem_succ_iff.mpr (Or.inr hi))).1]
    exact hp.1)] at hm
  exact hm

theorem woodinSparseSourceStage_projection_mem_filter {Ω θ i p : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (hi : i ∈ θ)
    {G : Set V} (hG : IsExternalForcingFilter
      ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ))
      ((forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ)) G) (hp : p ∈ G) :
    ((forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex θ⟩ₖ) ‘ p ∈ G := by
  let := IsOrdinal.of_mem hi
  have hsubi : i ⊆ Ω := fun x hx ↦ hθ x (IsOrdinal.toIsTransitive.mem_trans hx hi)
  exact woodinSparseSourceStage_projectedFilter_subset hΩ hAC hθ hi hG
    ((woodinSparseSourceStage_splitProjection_to_row hΩ hAC hθ hi).projection.image_mem
      ((woodinSparseSourceStageCode_valid hΩ hAC hsubi).system.order.preorder _ (mem_succ_self _)) hG hp)

namespace ForcingContext

noncomputable def woodinSparseSourcePrefixContext (A : ForcingContext V)
    {Ω δ γ : V} [IsOrdinal δ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hδ : δ ⊆ Ω) (hγ : γ ∈ δ)
    (hP : A.P = (forcingCodeP (woodinSparseSourceStageCode δ)) ‘ (woodinSourceIndex δ))
    (hR : A.R = (forcingCodeR (woodinSparseSourceStageCode δ)) ‘ (woodinSourceIndex δ)) : ForcingContext V := by
  let := IsOrdinal.of_mem hγ
  have hγΩ : γ ⊆ Ω := fun x hx ↦ hδ x (IsOrdinal.toIsTransitive.mem_trans hx hγ)
  have hc := woodinSparseSourceStageCode_valid hΩ hAC hγΩ
  have ht := hc.system.tops.top (woodinSourceIndex γ) (mem_succ_self _)
  rw [woodinSparseSourceStageCode_top hΩ hAC hγΩ (mem_succ_self _)] at ht
  have hs := woodinSparseSourceStage_splitProjection_to_row hΩ hAC hδ hγ
  rw [← hP, ← hR] at hs
  exact ⟨_, _, ∅, forcingProjectionGeneric _ _
    ((forcingCodeπ (woodinSparseSourceStageCode δ)) ‘ ⟨woodinSourceIndex γ, woodinSourceIndex δ⟩ₖ) A.G,
    hc.system.order.preorder (woodinSourceIndex γ) (mem_succ_self _), ht,
    hs.projection.generic (hc.system.order.preorder (woodinSourceIndex γ) (mem_succ_self _)) A.generic⟩

theorem woodinSparseSourcePrefixContext_split (A : ForcingContext V)
    {Ω δ γ : V} [IsOrdinal δ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hδ : δ ⊆ Ω) (hγ : γ ∈ δ)
    (hP : A.P = (forcingCodeP (woodinSparseSourceStageCode δ)) ‘ (woodinSourceIndex δ))
    (hR : A.R = (forcingCodeR (woodinSparseSourceStageCode δ)) ‘ (woodinSourceIndex δ)) :
    IsForcingSplitProjection
      (A.woodinSparseSourcePrefixContext hΩ hAC hδ hγ hP hR).P
      (A.woodinSparseSourcePrefixContext hΩ hAC hδ hγ hP hR).R A.P A.R
      ((forcingCodeπ (woodinSparseSourceStageCode δ)) ‘ ⟨woodinSourceIndex γ, woodinSourceIndex δ⟩ₖ)
      ((forcingCodeE (woodinSparseSourceStageCode δ)) ‘ ⟨woodinSourceIndex γ, woodinSourceIndex δ⟩ₖ) := by
  have hs := woodinSparseSourceStage_splitProjection_to_row hΩ hAC hδ hγ
  rwa [← hP, ← hR] at hs

end ForcingContext
end ZFVP
