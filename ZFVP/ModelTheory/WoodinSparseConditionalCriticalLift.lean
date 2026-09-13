import ZFVP.ModelTheory.WoodinSparseAdjustedGeneric
import ZFVP.ModelTheory.ForcingInternalLiftTransport
import ZFVP.ModelTheory.WoodinSparseArbitraryCriticalLift

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "P[" θ "]" => (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ)
local notation "R[" θ "]" => (forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ)
local notation "π[" i "," θ "]" => (forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex θ⟩ₖ

/-- The actual restricted complete-code capture lifts in the original endpoint
extension, conditional on ground relative homogeneity of the actual final forcing. -/
theorem ForcingContext.woodinSparseSource_exists_criticalLift_of_relativeHomogeneity
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
    ∃ g ∈ hierarchy (E.check Ω),
      IsCodedMembershipEmbedding (hierarchy (E.check γ)) (hierarchy (E.check ξ)) g ∧
      IsCriticalPoint (hierarchy (E.check γ)) g (E.check κ) ∧
      ∀ x ∈ hierarchy γ, g ‘ (E.check x) = E.check (f ‘ x) := by
  let := hierarchy_transitive (ordinalAdd ξ (ω : V))
  have hδξ : δ ∈ ξ := by
    rw [← hδ, ← himage]
    exact (he.value_mem_iff hκ.mem_domain (ordinal_subset_hierarchy _ _ (ordinalAdd_omega_gt γ))).mpr hκγ
  have hδΩ := IsOrdinal.toIsTransitive.mem_trans hδξ hξ
  have hγξ := IsOrdinal.toIsTransitive.mem_trans hgap hδξ
  have hγΩ := IsOrdinal.toIsTransitive.mem_trans hγξ hξ
  have hsγ := IsOrdinal.toIsTransitive.transitive _ hγΩ
  have hsξ := IsOrdinal.toIsTransitive.transitive _ hξ
  have hsΩ := subset_refl Ω
  obtain ⟨hfixγ, _, _, hinγ, _, _, _, _⟩ := woodinSparseSourceStageCode_capture_marked
    hΩ hAC hξ he hcode hcap himage hfix hκ hκγ (hδ.symm ▸ hgap)
  have hinξ := hfix ▸ ((woodinIterationExit hΩ hAC).2.1 ξ hξ).1.inaccessible ξ (mem_succ_self ξ)
  have hiγ := woodinSourceIndex_infinite (fun hh ↦ mem_asymm hh hinγ.2.1)
  have hiξ := woodinSourceIndex_infinite (fun hh ↦ mem_asymm hh hinξ.2.1)
  have hcp := woodinSparseSourceStageCode_capture_carrier hΩ hAC hsγ he hcode hcap (mem_succ_self (woodinSourceIndex γ))
  have hcp' : f ‘ P[γ] = P[ξ] := by simpa only [hiγ, hiξ, himage] using hcp
  rw [(woodinSparseSourceStageCode_row (mem_succ_self γ)).1,
    (woodinSparseSourceStageCode_row (mem_succ_self ξ)).1] at hcp'
  have hfixγΩ : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ := by
    rw [← woodinIterationRec_cardinal_eq_endpoint hΩ hAC (mem_succ_iff.mpr (Or.inr hγΩ))]
    exact hfixγ
  have hfixξΩ : (kpair.π₂ (woodinIterationRec Ω)) ‘ ξ = ξ := by
    rw [← woodinIterationRec_cardinal_eq_endpoint hΩ hAC (mem_succ_iff.mpr (Or.inr hξ))]
    exact hfix
  obtain ⟨a, ha, hsame, himg, _, _⟩ := E.woodinSparseSource_adjustedGeneric
    hΩ hAC hξ he hcode hcap himage hfix hκ hκγ hgap hδ hP hR hhom
  let H := E.isomorphismImage ha E.order
  have hHG : IsExternalForcingGeneric P[Ω] R[Ω] H.G := by
    have hh : IsExternalForcingGeneric E.P E.R H.G := H.generic
    simpa only [hP, hR] using hh
  have hEG : IsExternalForcingGeneric P[Ω] R[Ω] E.G := by
    simpa only [hP, hR] using E.generic
  have hsameγ := woodinSparseSourceStage_projectedGeneric_eq_of_prefix_eq hΩ hAC hsΩ hδΩ hgap hHG hEG hsame
  have htop : IsForcingTop E.P E.R (∅ : V) := by
    rw [hP, hR]
    have hh := (woodinSparseSourceStageCode_valid hΩ hAC hsΩ).system.tops.top (woodinSourceIndex Ω) (mem_succ_self _)
    rwa [woodinSparseSourceStageCode_top hΩ hAC hsΩ (mem_succ_self _)] at hh
  let B : ForcingContext V := ⟨E.P, E.R, ∅, H.G, E.order, htop, H.generic⟩
  have hBP : B.P = (forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω :=
    hP.trans (woodinSparseSourceStageCode_row (mem_succ_self Ω)).1
  have hBR : B.R = (forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω :=
    hR.trans (woodinSparseSourceStageCode_row (mem_succ_self Ω)).2
  have hback : forcingProjectionGeneric E.P E.R (converseGraph a) B.G = E.G :=
    E.isomorphismImage_pullback ha E.order
  apply E.exists_criticalLift_of_checkPreservingEquiv_symm B
    (E.isomorphismModelEquiv B ha hback)
    (E.isomorphismModelEquiv_mem_iff B ha hback)
    (E.isomorphismModelEquiv_check B ha hback)
  apply B.woodinSparseEndpoint_exists_restricted_criticalLift hΩ hAC hBP hBR rfl hγΩ hξ hγξ
    hfixγΩ hfixξΩ he hcp' ?_ hκ hκγ
  have hrowγ := woodinSparseSourceStageCode_row (mem_succ_self γ)
  have hrowξ := woodinSparseSourceStageCode_row (mem_succ_self ξ)
  have hπγ := (woodinSparseSourceStageCode_matrices (mem_succ_iff.mpr (Or.inr hγΩ)) (mem_succ_self Ω)).1
  have hπξ := (woodinSparseSourceStageCode_matrices (mem_succ_iff.mpr (Or.inr hξ)) (mem_succ_self Ω)).1
  intro p hp
  have hpH : p ∈ forcingProjectionGeneric P[γ] R[γ] π[γ,Ω] H.G := by
    simpa only [hrowγ.1, hrowγ.2, hπγ] using hp
  have hpE := hsameγ ▸ hpH
  have hm := himg p hpE
  simpa only [hrowξ.1, hrowξ.2, hπξ] using hm

end ZFVP
