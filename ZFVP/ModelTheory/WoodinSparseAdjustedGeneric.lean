import ZFVP.ModelTheory.WoodinSparseCapturedMaster
import ZFVP.ModelTheory.ProjectionQuotientCheckedBound
import ZFVP.ModelTheory.RelativeAutomorphismGeneric
import ZFVP.ModelTheory.WoodinSparseFixedPointInclusion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "P[" θ "]" => (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ)
local notation "R[" θ "]" => (forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ)
local notation "π[" i "," θ "]" => (forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex θ⟩ₖ

theorem woodinSparseSourceStage_retraction_to_row {Ω θ i : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (hi : i ∈ θ) :
    IsForcingRetraction P[i] R[i] P[θ] R[θ] π[i,θ] := by
  apply (woodinSparseSourceStage_splitProjection_to_row hΩ hAC hθ hi).retraction_of_identity_section
  intro p hp
  apply woodinSparseSourceStageCode_section hΩ hAC hθ hi
  rwa [(woodinSparseSourceStage_old_row (mem_succ_iff.mpr (Or.inr hi))).1]

theorem woodinSparseSourceStage_projectedGeneric_comp {Ω θ j i : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hj : j ∈ θ) (hi : i ∈ j) {G : Set V} (hG : IsExternalForcingGeneric P[θ] R[θ] G) :
    forcingProjectionGeneric P[i] R[i] π[i,j] (forcingProjectionGeneric P[j] R[j] π[j,θ] G) =
      forcingProjectionGeneric P[i] R[i] π[i,θ] G := by
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hi
  have hjΩ : j ⊆ Ω := fun x hx ↦ hθ x (IsOrdinal.toIsTransitive.mem_trans hx hj)
  have hiΩ : i ⊆ Ω := fun x hx ↦ hjΩ x (IsOrdinal.toIsTransitive.mem_trans hx hi)
  have hiθ := IsOrdinal.toIsTransitive.mem_trans hi hj
  have ri := (woodinSparseSourceStageCode_valid hΩ hAC hiΩ).system.order.preorder _ (mem_succ_self _)
  have rj := (woodinSparseSourceStageCode_valid hΩ hAC hjΩ).system.order.preorder _ (mem_succ_self _)
  have a := woodinSparseSourceStage_retraction_to_row hΩ hAC hθ hj
  have b := woodinSparseSourceStage_retraction_to_row hΩ hAC hjΩ hi
  have c := woodinSparseSourceStage_retraction_to_row hΩ hAC hθ hiθ
  ext p
  rw [b.projectedGeneric_iff ri (a.projection.generic rj hG).1,
    a.projectedGeneric_iff rj hG.1, c.projectedGeneric_iff ri hG.1]
  exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, b.inclusion p h.2⟩, h.2⟩⟩

theorem woodinSparseSourceStage_projectedGeneric_eq_of_prefix_eq {Ω θ j i : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hj : j ∈ θ) (hi : i ∈ j) {G H : Set V}
    (hG : IsExternalForcingGeneric P[θ] R[θ] G) (hH : IsExternalForcingGeneric P[θ] R[θ] H)
    (h : forcingProjectionGeneric P[j] R[j] π[j,θ] G = forcingProjectionGeneric P[j] R[j] π[j,θ] H) :
    forcingProjectionGeneric P[i] R[i] π[i,θ] G = forcingProjectionGeneric P[i] R[i] π[i,θ] H := by
  rw [← woodinSparseSourceStage_projectedGeneric_comp hΩ hAC hθ hj hi hG,
    ← woodinSparseSourceStage_projectedGeneric_comp hΩ hAC hθ hj hi hH, h]

/-- The actual captured master gives a generic with the required image inclusion,
conditional only on ground relative homogeneity at the final endpoint. -/
theorem ForcingContext.woodinSparseSource_adjustedGeneric
    (E : ForcingContext V) {Ω f γ ξ κ δ : V} [IsOrdinal Ω] [IsOrdinal γ] [IsOrdinal ξ] [IsOrdinal δ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hξ : ξ ∈ Ω)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd γ (ω : V)))
      (hierarchy (ordinalAdd ξ (ω : V))) f)
    (hcode : ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ ∈
      hierarchy (ordinalAdd γ (ω : V)))
    (hcap : f ‘ ⟨woodinSparseSourceStageCode γ, woodinSparseSourceStageCardinals γ⟩ₖ =
      ⟨woodinSparseSourceStageCode ξ, woodinSparseSourceStageCardinals ξ⟩ₖ)
    (himage : f ‘ γ = ξ) (hfix : (kpair.π₂ (woodinIterationRec ξ)) ‘ ξ = ξ)
    (hκ : IsCriticalPoint (hierarchy (ordinalAdd γ (ω : V))) f κ)
    (hκγ : κ ∈ γ) (hgap : γ ∈ δ) (hδ : f ‘ κ = δ)
    (hP : E.P = P[Ω]) (hR : E.R = R[Ω])
    (hhom : ∀ t ∈ P[Ω], ∀ p ∈ P[Ω], ⟨π[δ,Ω] ‘ p, π[δ,Ω] ‘ t⟩ₖ ∈ R[δ] →
      ∃ a, IsForcingAutomorphism P[Ω] R[Ω] a ∧
        (∀ q ∈ P[Ω], π[δ,Ω] ‘ (a ‘ q) = π[δ,Ω] ‘ q) ∧ ForcingCompatible P[Ω] R[Ω] (a ‘ p) t) :
    ∃ a, ∃ ha : IsForcingAutomorphism E.P E.R a,
      forcingProjectionGeneric P[δ] R[δ] π[δ,Ω] (E.isomorphismImage ha E.order).G =
        forcingProjectionGeneric P[δ] R[δ] π[δ,Ω] E.G ∧
      (∀ p ∈ forcingProjectionGeneric P[γ] R[γ] π[γ,Ω] E.G,
        f ‘ p ∈ forcingProjectionGeneric P[ξ] R[ξ] π[ξ,Ω] (E.isomorphismImage ha E.order).G) ∧
      (∀ x y : E.Model, E.isomorphismImageEquiv ha E.order x ∈ E.isomorphismImageEquiv ha E.order y ↔ x ∈ y) ∧
      (∀ x : V, E.isomorphismImageEquiv ha E.order (E.check x) = (E.isomorphismImage ha E.order).check x) := by
  have hδξ : δ ∈ ξ := by
    rw [← hδ, ← himage]
    exact (he.value_mem_iff hκ.mem_domain (ordinal_subset_hierarchy _ _ (ordinalAdd_omega_gt γ))).mpr hκγ
  have hδΩ := IsOrdinal.toIsTransitive.mem_trans hδξ hξ
  have hγΩ := IsOrdinal.toIsTransitive.mem_trans hgap hδΩ
  have hsΩ := subset_refl Ω
  have hsξ := IsOrdinal.toIsTransitive.transitive _ hξ
  have hsδ := IsOrdinal.toIsTransitive.transitive _ hδΩ
  have hG : IsExternalForcingGeneric P[Ω] R[Ω] E.G := by simpa only [hP, hR] using E.generic
  let A := E.woodinSparseSourcePrefixContext hΩ hAC hsΩ hδΩ hP hR
  obtain ⟨t, ht, htA, hb⟩ := A.woodinSparseSource_capture_master hΩ hAC hξ he hcode hcap himage hfix hκ hκγ hgap hδ rfl rfl rfl
  have rd := (woodinSparseSourceStageCode_valid hΩ hAC hsδ).system.order.preorder _ (mem_succ_self _)
  have rx := (woodinSparseSourceStageCode_valid hΩ hAC hsξ).system.order.preorder _ (mem_succ_self _)
  have ro := (woodinSparseSourceStageCode_valid hΩ hAC hsΩ).system.order.preorder _ (mem_succ_self _)
  have dx := woodinSparseSourceStage_splitProjection_to_row hΩ hAC hsξ hδξ
  have xo := woodinSparseSourceStage_retraction_to_row hΩ hAC hsΩ hξ
  have do' := woodinSparseSourceStage_splitProjection_to_row hΩ hAC hsΩ hδΩ
  have htΩ := xo.inclusion t ht
  have htπ : π[δ,Ω] ‘ t = π[δ,ξ] ‘ t := by
    rw [woodinSparseSourceStageCode_projection hΩ hAC hsΩ hδΩ htΩ,
      woodinSparseSourceStageCode_projection hΩ hAC hsξ hδξ ht]
  obtain ⟨a, ha, haG, hta, hsame, _⟩ := externalGeneric_relative_movement_of_homogeneity
    ro rd do' hG htΩ (htπ.symm ▸ htA) (hhom t htΩ)
  have haE : IsForcingAutomorphism E.P E.R a := by simpa only [hP, hR] using ha
  have hH : (E.isomorphismImage haE E.order).G = forcingProjectionGeneric P[Ω] R[Ω] a E.G := by
    change forcingProjectionGeneric E.P E.R a E.G = _
    rw [hP, hR]
  refine ⟨a, haE, ?_, ?_, E.isomorphismImageEquiv_mem haE E.order, E.isomorphismImageEquiv_check haE E.order⟩
  · rw [hH]
    exact hsame
  · intro p hp
    rw [hH]
    have hpA : p ∈ forcingProjectionGeneric P[γ] R[γ] π[γ,δ] A.G := by
      change p ∈ forcingProjectionGeneric P[γ] R[γ] π[γ,δ] (forcingProjectionGeneric P[δ] R[δ] π[δ,Ω] E.G)
      rwa [woodinSparseSourceStage_projectedGeneric_comp hΩ hAC hsΩ hδΩ hgap hG]
    apply A.projectionQuotient_checked_bound_mem_generic rx dx (xo.projection.generic rx haG) ?_ ?_ (hb p hpA)
    · change forcingProjectionGeneric P[δ] R[δ] π[δ,ξ]
        (forcingProjectionGeneric P[ξ] R[ξ] π[ξ,Ω] (forcingProjectionGeneric P[Ω] R[Ω] a E.G)) = _
      rw [woodinSparseSourceStage_projectedGeneric_comp hΩ hAC hsΩ hξ hδξ haG]
      exact hsame
    · exact (xo.projectedGeneric_iff rx haG.1).mpr ⟨hta, ht⟩

end ZFVP
