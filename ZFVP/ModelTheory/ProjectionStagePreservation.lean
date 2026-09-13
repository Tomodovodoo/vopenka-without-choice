import ZFVP.ModelTheory.ProjectionRegularPreservation
import ZFVP.ModelTheory.SaturatedWoodinSuccessor
import ZFVP.ModelTheory.ForcingSingularDependentChoice
import ZFVP.ModelTheory.ProjectionQuotientClosureForcing
import ZFVP.SetTheory.HartogsLimitRegular

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem projected_stage_preservation (B : ForcingContext V) {P R one κ π E : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hπ : IsForcingSplitProjection P R B.P B.R π E)
    (hs : ∀ p ∈ P, p ∈ forcingFormula P R woodinStageCardinalFormula (standardTuple ![checkName one κ]))
    (hc : ForcesProjectionQuotientClosedBelow P R one B.P B.R π κ) :
    IsRegularCardinal (B.check κ) ∧ ∀ α ∈ B.check κ, InternalDependentChoiceAt α := by
  let A : ForcingContext V := ⟨P, R, one, forcingProjectionGeneric P R π B.G,
    hR, ht, hπ.projection.generic hR B.generic⟩
  have he : forcingProjectionGeneric A.P A.R π B.G = A.G := rfl
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  have hstage : IsRegularCardinal (A.check κ) ∧ ∀ α ∈ A.check κ, InternalDependentChoiceAt α :=
    (Defined.eval_iff _).mp ((A.formula_truth woodinStageCardinalFormula
      ![⟨checkName one κ, checkName_isName ht.1 κ⟩]).mpr ⟨p, hp, hs p (A.generic.1.1 p hp)⟩)
  let := hstage.1.1.1
  have hclosed := A.projectionQuotient_closedBelow_of_forced hπ.projection B.order hc
  have hreg := A.projectionInclusion_regular_of_separative_closed B hπ he hstage.1 hstage.2 hclosed
  have hDC := A.projectionInclusion_dependentChoiceBelow_of_separative_closed B hπ he hstage.2 hclosed
  rw [A.projectionInclusion_check B hπ he] at hreg hDC
  exact ⟨hreg, hDC⟩

/-- Closed final quotients preserve a cofinal family of old regulars and DC
below their supremum. At a ground singular limit this also gives DC at the supremum. -/
theorem projected_singular_limit_stage (B : ForcingContext V) {γ θ P R t K π E : V} [IsOrdinal γ]
    (hω : (ω : V) ⊆ γ) (hsucc : ∀ α ∈ γ, succ α ∈ γ)
    (hcf : internalCofinality γ ∈ γ)
    (hK : ∀ i ∈ θ, K ‘ i ∈ γ) (hcof : ∀ α ∈ γ, ∃ i ∈ θ, α ∈ K ‘ i)
    (hR : ∀ i ∈ θ, IsForcingPreorder (P ‘ i) (R ‘ i))
    (ht : ∀ i ∈ θ, IsForcingTop (P ‘ i) (R ‘ i) (t ‘ i))
    (hπ : ∀ i ∈ θ, IsForcingSplitProjection (P ‘ i) (R ‘ i) B.P B.R (π ‘ i) (E ‘ i))
    (hs : ∀ i ∈ θ, ∀ p ∈ P ‘ i, p ∈ forcingFormula (P ‘ i) (R ‘ i)
      woodinStageCardinalFormula (standardTuple ![checkName (t ‘ i) (K ‘ i)]))
    (hc : ∀ i ∈ θ, ForcesProjectionQuotientClosedBelow (P ‘ i) (R ‘ i) (t ‘ i)
      B.P B.R (π ‘ i) (K ‘ i)) :
    IsLimitOfRegularCardinals (B.check γ) ∧ InternalDependentChoiceAt (B.check γ) := by
  have hi (i : V) (hi : i ∈ θ) := B.projected_stage_preservation (hR i hi) (ht i hi)
    (hπ i hi) (hs i hi) (hc i hi)
  have hd : ∀ α ∈ B.check γ, InternalDependentChoiceAt α := by
    intro α hα
    obtain ⟨β, hβ, rfl⟩ := (B.mem_check_iff γ α).mp hα
    obtain ⟨i, hiθ, hβi⟩ := hcof β hβ
    exact (hi i hiθ).2 _ ((B.check_mem_iff _ _).mpr hβi)
  refine ⟨⟨inferInstance, ?_, ?_⟩, B.check_dependentChoiceAt_of_singular ?_ hsucc hcf hd⟩
  · have h := (B.checkEmbedding.subset_iff _ _).mpr hω
    change B.check ω ⊆ B.check γ at h
    rwa [show B.check ω = (ω : B.Model) from B.checkEmbedding.map_omega] at h
  · intro α hα
    obtain ⟨β, hβ, rfl⟩ := (B.mem_check_iff γ α).mp hα
    obtain ⟨i, hiθ, hβi⟩ := hcof β hβ
    exact ⟨B.check (K ‘ i), (B.check_mem_iff _ _).mpr (hK i hiθ),
      (hi i hiθ).1, (B.check_mem_iff _ _).mpr hβi⟩
  · exact hω ∅ (by simpa only [zero_def] using (show (0 : V) ∈ (ω : V) by simp))

end ForcingContext
end ZFVP
