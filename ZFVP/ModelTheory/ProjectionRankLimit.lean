import ZFVP.ModelTheory.ProjectionHierarchyAgreement
import ZFVP.ModelTheory.ProjectionStagePreservation
import ZFVP.ModelTheory.WoodinRankStage

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- At a limit, each bounded rank and its enumeration come from an earlier
stage through a closed quotient. -/
theorem ForcingContext.projected_limit_rankEnumerations (B : ForcingContext V)
    {θ κ P R t K π E : V} [IsOrdinal θ] [IsOrdinal κ]
    (hlim : ∀ i ∈ θ, succ i ∈ θ) (hK : ∀ i ∈ θ, K ‘ i ∈ κ)
    (hR : ∀ i ∈ θ, IsForcingPreorder (P ‘ i) (R ‘ i))
    (ht : ∀ i ∈ θ, IsForcingTop (P ‘ i) (R ‘ i) (t ‘ i))
    (hπ : ∀ i ∈ θ, IsForcingSplitProjection (P ‘ i) (R ‘ i) B.P B.R (π ‘ i) (E ‘ i))
    (hs : ∀ i ∈ θ, ∀ p ∈ P ‘ i, p ∈ forcingFormula (P ‘ i) (R ‘ i)
      woodinStageCardinalFormula (standardTuple ![checkName (t ‘ i) (K ‘ i)]))
    (hc : ∀ i ∈ θ, ForcesProjectionQuotientClosedBelow (P ‘ i) (R ‘ i) (t ‘ i) B.P B.R (π ‘ i) (K ‘ i))
    (hrank : ∀ i ∈ θ, ForcesRankEnumerations (P ‘ i) (R ‘ i) (t ‘ i) i (K ‘ i)) :
    HasShortRankEnumerations (B.check θ) (B.check κ) := by
  intro α hα
  obtain ⟨β, hβ, rfl⟩ := (B.mem_check_iff θ α).mp hα
  let := IsOrdinal.of_mem hβ
  let i := succ β
  have hi : i ∈ θ := hlim β hβ
  let A : ForcingContext V := ⟨P ‘ i, R ‘ i, t ‘ i,
    forcingProjectionGeneric (P ‘ i) (R ‘ i) (π ‘ i) B.G,
    hR i hi, ht i hi, (hπ i hi).projection.generic (hR i hi) B.generic⟩
  have hgen : forcingProjectionGeneric A.P A.R (π ‘ i) B.G = A.G := rfl
  let j := A.projectionInclusion B (hπ i hi) hgen
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  have hstage : IsRegularCardinal (A.check (K ‘ i)) ∧
      ∀ γ ∈ A.check (K ‘ i), InternalDependentChoiceAt γ :=
    (Defined.eval_iff _).mp ((A.checked_unary_truth woodinStageCardinalFormula (K ‘ i)).mpr
      ⟨p, hp, hs i hi p (A.generic.1.1 p hp)⟩)
  let := hstage.1.1.1
  have hclosed := A.projectionQuotient_closedBelow_of_forced (hπ i hi).projection B.order (hc i hi)
  have hen := A.rankEnumerations_of_forced (hrank i hi)
  have hβi : A.check β ∈ A.check i := (A.check_mem_iff _ _).mpr (mem_succ_self β)
  have hsub : A.check β ⊆ A.check i := IsOrdinal.toIsTransitive.transitive _ hβi
  have heq := A.projectionInclusion_hierarchy_of_separative_closed B (hπ i hi) hgen
    hstage.2 hclosed (fun a ha ↦ hen a (hsub a ha))
  change j (hierarchy (A.check β)) = hierarchy (j (A.check β)) at heq
  rw [A.projectionInclusion_check B (hπ i hi) hgen] at heq
  obtain ⟨γ, hγ, e, he, her⟩ := hen (A.check β) hβi
  refine ⟨j γ, ?_, j e, ?_, ?_⟩
  · have hm := (j.mem_iff _ _).mpr hγ
    change j γ ∈ A.projectionInclusion B (hπ i hi) hgen (A.check (K ‘ i)) at hm
    rw [A.projectionInclusion_check B (hπ i hi) hgen] at hm
    exact IsOrdinal.toIsTransitive.mem_trans hm ((B.check_mem_iff _ _).mpr (hK i hi))
  · have hm := (j.function_iff e γ (hierarchy (A.check β))).mpr he
    rwa [heq] at hm
  · have hm := congrArg j her
    rwa [j.map_range, heq] at hm

end ZFVP
