import ZFVP.ModelTheory.DirectQuotientClosureTransfer
import ZFVP.ModelTheory.ProjectionRegularPreservation
import ZFVP.ModelTheory.WoodinCollapseForcesRestoration

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem directLimit_short_preservation (B : ForcingContext V)
    {θ P R π E U K t α : V} (hθ : IsChoicelessInaccessible θ)
    (h : IsSplitForcingSystem θ P π E)
    (hR : ∀ i ∈ θ, IsForcingPreorder (P ‘ i) (R ‘ i))
    (ht : ∀ i ∈ θ, IsForcingTop (P ‘ i) (R ‘ i) (t ‘ i))
    (hsplit : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j →
      IsForcingSplitProjection (P ‘ i) (R ‘ i) (P ‘ j) (R ‘ j) (π ‘ ⟨i, j⟩ₖ) (E ‘ ⟨i, j⟩ₖ))
    (hU : ∀ i ∈ θ, P ‘ i ⊆ U) (hsmall : ∀ i ∈ θ, P ‘ i ∈ hierarchy θ)
    (hK : ∀ i ∈ θ, K ‘ i ∈ θ) (hcof : ∀ β ∈ θ, ∃ i ∈ θ, β ∈ K ‘ i)
    (hDC : ∀ i ∈ θ, ∀ p ∈ P ‘ i, p ∈ forcingFormula (P ‘ i) (R ‘ i) dependentChoiceBelowFormula
      (standardTuple ![checkName (t ‘ i) (K ‘ i)]))
    (hc : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j →
      ForcesProjectionQuotientClosedBelow (P ‘ i) (R ‘ i) (t ‘ i) (P ‘ j) (R ‘ j) (π ‘ ⟨i, j⟩ₖ) (K ‘ i))
    (hBP : B.P = forcingDirectLimit θ P π E U)
    (hBR : B.R = forcingThreadOrder θ R (forcingDirectLimit θ P π E U)) (hα : α ∈ θ) :
    InternalDependentChoiceAt (B.check α) ∧
      ∀ f ∈ B.check θ ^ B.check α, ∃ β ∈ B.check θ, ∀ a ∈ B.check α, f ‘ a ∈ β := by
  let := hθ.1
  let := IsOrdinal.of_mem hα
  obtain ⟨i, hi, hαi⟩ := hcof α hα
  let := IsOrdinal.of_mem (hK i hi)
  let D := forcingDirectLimit θ P π E U
  let ρ := forcingThreadCoordinate D i
  have hπ : IsForcingSplitProjection (P ‘ i) (R ‘ i) B.P B.R ρ (forcingThreadSection θ P π E i) := by
    rw [hBP, hBR]
    exact forcingDirectLimit_splitProjection h hi hU hsplit
  let A : ForcingContext V := ⟨P ‘ i, R ‘ i, t ‘ i, forcingProjectionGeneric (P ‘ i) (R ‘ i) ρ B.G,
    hR i hi, ht i hi, hπ.projection.generic (hR i hi) B.generic⟩
  have hA : forcingProjectionGeneric A.P A.R ρ B.G = A.G := rfl
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  let cn : ForcingName A.P := ⟨checkName A.one (K ‘ i), checkName_isName A.top.1 _⟩
  have hd : ∀ β ∈ A.check (K ‘ i), InternalDependentChoiceAt β :=
    (Defined.eval_iff _).mp ((A.formula_truth dependentChoiceBelowFormula ![cn]).mpr
        ⟨p, hp, hDC i hi p (A.generic.1.1 p hp)⟩)
  have hclosed : IsForcingClosedBelow (A.projectionQuotient B.P ρ)
      (forcingSeparativeOrder (A.projectionQuotient B.P ρ) (A.projectionQuotientOrder B.P B.R ρ)) (A.check (K ‘ i)) := by
    have hh := A.directLimit_quotient_separative_closedBelow_of_small hθ (hsmall i hi) h hi rfl hU hsplit
      ((A.checkEmbedding.subset_iff _ _).mpr (IsOrdinal.toIsTransitive.transitive _ (hK i hi))) (fun j hj hij ↦
        A.projectionQuotient_closedBelow_of_forced (hsplit i hi j hj hij).projection (hR j hj) (hc i hi j hj hij))
    simpa only [hBP, hBR, ρ, D, ForcingContext.checkEmbedding] using hh
  have hαi' : A.check α ∈ A.check (K ‘ i) := (A.check_mem_iff _ _).mpr hαi
  have hthrough : IsForcingClosedThrough (A.projectionQuotient B.P ρ)
      (forcingSeparativeOrder (A.projectionQuotient B.P ρ) (A.projectionQuotientOrder B.P B.R ρ)) (A.check α) := by
    intro β hβ hβα
    let := hβ
    exact hclosed β (ordinal_mem_of_subset_mem hβα hαi')
  constructor
  · have hh := A.projectionInclusion_dependentChoiceAt_of_separative_closed B hπ hA (hd _ hαi') hthrough
    rwa [A.projectionInclusion_check B hπ hA] at hh
  · intro f hf
    have hf' : f ∈ A.projectionInclusion B hπ hA (A.check θ) ^ A.projectionInclusion B hπ hA (A.check α) := by
      simpa only [A.projectionInclusion_check B hπ hA] using hf
    have hh := A.projectionInclusion_function_values_bounded_of_separative_closed B hπ hA
      (A.check_regular_of_small hθ (hsmall i hi)) ((A.check_mem_iff α θ).mpr hα) (hd _ hαi') hthrough hf'
    simpa only [A.projectionInclusion_check B hπ hA] using hh

theorem directLimit_stage_cardinal (B : ForcingContext V)
    {θ P R π E U K t : V} (hθ : IsChoicelessInaccessible θ)
    (h : IsSplitForcingSystem θ P π E)
    (hR : ∀ i ∈ θ, IsForcingPreorder (P ‘ i) (R ‘ i))
    (ht : ∀ i ∈ θ, IsForcingTop (P ‘ i) (R ‘ i) (t ‘ i))
    (hsplit : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j →
      IsForcingSplitProjection (P ‘ i) (R ‘ i) (P ‘ j) (R ‘ j) (π ‘ ⟨i, j⟩ₖ) (E ‘ ⟨i, j⟩ₖ))
    (hU : ∀ i ∈ θ, P ‘ i ⊆ U) (hsmall : ∀ i ∈ θ, P ‘ i ∈ hierarchy θ)
    (hK : ∀ i ∈ θ, K ‘ i ∈ θ) (hcof : ∀ β ∈ θ, ∃ i ∈ θ, β ∈ K ‘ i)
    (hDC : ∀ i ∈ θ, ∀ p ∈ P ‘ i, p ∈ forcingFormula (P ‘ i) (R ‘ i) dependentChoiceBelowFormula
      (standardTuple ![checkName (t ‘ i) (K ‘ i)]))
    (hc : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j →
      ForcesProjectionQuotientClosedBelow (P ‘ i) (R ‘ i) (t ‘ i) (P ‘ j) (R ‘ j) (π ‘ ⟨i, j⟩ₖ) (K ‘ i))
    (hBP : B.P = forcingDirectLimit θ P π E U)
    (hBR : B.R = forcingThreadOrder θ R (forcingDirectLimit θ P π E U)) :
    IsRegularCardinal (B.check θ) ∧ ∀ α ∈ B.check θ, InternalDependentChoiceAt α := by
  let := hθ.1
  constructor
  · apply B.check_regular_of_short_functions_bounded hθ.regular.2.1
    intro α hα
    exact (B.directLimit_short_preservation hθ h hR ht hsplit hU hsmall hK hcof hDC hc hBP hBR hα).2
  · intro α hα
    obtain ⟨β, hβ, rfl⟩ := (B.mem_check_iff θ α).mp hα
    exact (B.directLimit_short_preservation hθ h hR ht hsplit hU hsmall hK hcof hDC hc hBP hBR hβ).1

end ForcingContext
end ZFVP
