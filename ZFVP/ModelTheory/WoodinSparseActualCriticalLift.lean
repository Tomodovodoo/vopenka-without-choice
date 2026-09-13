import ZFVP.ModelTheory.WoodinSparseActualGenericMovement
import ZFVP.ModelTheory.WoodinSparseConditionalCriticalLift

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "P[" θ "]" => (forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ)
local notation "R[" θ "]" => (forcingCodeR (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex θ)
local notation "π[" i "," θ "]" => (forcingCodeπ (woodinSparseSourceStageCode θ)) ‘ ⟨woodinSourceIndex i, woodinSourceIndex θ⟩ₖ

theorem ForcingContext.woodinSparseSource_adjustedGeneric_actual
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
    (hP : E.P = P[Ω]) (hR : E.R = R[Ω]) :
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
  apply E.woodinSparseSource_adjustedGeneric hΩ hAC hξ he hcode hcap himage hfix hκ hκγ hgap hδ hP hR
  intro t ht p hp hle
  exact woodinSparseSource_relative_homogeneous hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hδΩ) hp ht hle

theorem ForcingContext.woodinSparseSource_exists_criticalLift_actual
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
    (hP : E.P = P[Ω]) (hR : E.R = R[Ω]) :
    ∃ g ∈ hierarchy (E.check Ω),
      IsCodedMembershipEmbedding (hierarchy (E.check γ)) (hierarchy (E.check ξ)) g ∧
      IsCriticalPoint (hierarchy (E.check γ)) g (E.check κ) ∧
      ∀ x ∈ hierarchy γ, g ‘ (E.check x) = E.check (f ‘ x) := by
  have hδξ : δ ∈ ξ := by
    rw [← hδ, ← himage]
    exact (he.value_mem_iff hκ.mem_domain (ordinal_subset_hierarchy _ _ (ordinalAdd_omega_gt γ))).mpr hκγ
  have hδΩ := IsOrdinal.toIsTransitive.mem_trans hδξ hξ
  apply E.woodinSparseSource_exists_criticalLift_of_relativeHomogeneity hΩ hAC hξ he hcode hcap himage hfix hκ hκγ hgap hδ hP hR
  intro t ht p hp hle
  exact woodinSparseSource_relative_homogeneous hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hδΩ) hp ht hle

end ZFVP
