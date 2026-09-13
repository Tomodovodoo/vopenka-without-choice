import ZFVP.ModelTheory.DirectLimitQuotientSupport
import ZFVP.ModelTheory.QuotientSplitProjection
import ZFVP.ModelTheory.LimitSplitProjection
import ZFVP.ModelTheory.SplitSeparativeOrder
import ZFVP.ModelTheory.ForcingSmallCardinals

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

/-- Closure of the stage quotients gives closure of the direct-limit quotient
for all intermediate sequences below the intermediate cofinality of the length. -/
theorem directLimit_quotient_separative_closedAt (A : ForcingContext V)
    {θ P R π E U i : V} [IsOrdinal θ] {α : A.Model}
    (h : IsSplitForcingSystem θ P π E) (hi : i ∈ θ) (hAP : A.P = P ‘ i)
    (hU : ∀ j ∈ θ, P ‘ j ⊆ U)
    (hsplit : ∀ j ∈ θ, ∀ k ∈ θ, j ⊆ k →
      IsForcingSplitProjection (P ‘ j) (R ‘ j) (P ‘ k) (R ‘ k)
        (π ‘ ⟨j, k⟩ₖ) (E ‘ ⟨j, k⟩ₖ))
    (hα : α ∈ internalCofinality (A.check θ))
    (hc : ∀ k ∈ θ, i ⊆ k →
      IsForcingClosedAt (A.projectionQuotient (P ‘ k) (π ‘ ⟨i, k⟩ₖ))
        (forcingSeparativeOrder (A.projectionQuotient (P ‘ k) (π ‘ ⟨i, k⟩ₖ))
          (A.projectionQuotientOrder (P ‘ k) (R ‘ k) (π ‘ ⟨i, k⟩ₖ))) α) :
    IsForcingClosedAt
      (A.projectionQuotient (forcingDirectLimit θ P π E U)
        (forcingThreadCoordinate (forcingDirectLimit θ P π E U) i))
      (forcingSeparativeOrder
        (A.projectionQuotient (forcingDirectLimit θ P π E U)
          (forcingThreadCoordinate (forcingDirectLimit θ P π E U) i))
        (A.projectionQuotientOrder (forcingDirectLimit θ P π E U)
          (forcingThreadOrder θ R (forcingDirectLimit θ P π E U))
          (forcingThreadCoordinate (forcingDirectLimit θ P π E U) i))) α := by
  intro f hf
  let D := forcingDirectLimit θ P π E U
  let ρ := forcingThreadCoordinate D i
  have hρ : ρ ∈ A.P ^ D := by
    rw [hAP]
    exact (forcingDirectLimit_splitProjection h hi hU hsplit).projection.maps
  obtain ⟨k, hk, hik, hs⟩ := A.check_directLimit_cofinal_common_support h hi hα
    (fun a ha ↦ (mem_sep_iff.mp (function_value_mem hf.1 ha)).1)
  have hkproj := forcingDirectLimit_splitProjection h hk hU hsplit
  have hτ : (π ‘ ⟨i, k⟩ₖ) ∈ A.P ^ (P ‘ k) := by
    rw [hAP]
    exact (hsplit i hi k hk hik).projection.maps
  have hcomm : ∀ q ∈ D,
      (π ‘ ⟨i, k⟩ₖ) ‘ ((forcingThreadCoordinate D k) ‘ q) = ρ ‘ q := by
    intro q hq
    rw [forcingThreadCoordinate_value hq, forcingThreadCoordinate_value hq]
    exact forcingInverseLimit_project_subset h
      (forcingDirectLimit_subset _ _ _ _ _ _ hq) hi hk hik
  have hqproj := A.projectionQuotient_splitProjection hρ hτ hkproj hcomm
  let := IsOrdinal.of_mem hα
  apply hqproj.separative_bound_of_range (hc k hk hik) hf
  intro a ha
  obtain ⟨q, hq, he, hsupport⟩ := hs a ha
  have hqa := function_value_mem hf.1 ha
  rw [he] at hqa
  have hqk := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp
    (forcingDirectLimit_subset _ _ _ _ _ _ hq)).2.1 k hk
  have hval : (A.projectionQuotientMap D ρ (forcingThreadCoordinate D k)) ‘ (A.check q) =
      A.check (q ‘ k) := by
    rw [A.projectionQuotientMap_value hkproj.projection.maps hq hqa,
      forcingThreadCoordinate_value hq]
  have hqkG := function_value_mem hqproj.projection.maps hqa
  rw [hval] at hqkG
  refine ⟨A.check (q ‘ k), hqkG, ?_⟩
  rw [A.projectionQuotientMap_value hkproj.maps hqk hqkG, he]
  congr 1
  rw [forcingThreadSection_value hqk]
  apply forcingThread_eq_of_support
    (forcingDirectLimit_subset _ _ _ _ _ _ (forcingSectionThread_mem h hk hqk hU))
    (forcingDirectLimit_subset _ _ _ _ _ _ hq)
    (forcingSectionThread_support h hk hqk) hsupport
  rw [forcingSectionThread_value hk, forcingSectionValue_self h hk hqk]

/-- Smallness of the initial forcing preserves the regularity needed at an
inaccessible direct limit. The closure cutoff may itself be intermediate. -/
theorem directLimit_quotient_separative_closedBelow_of_small (A : ForcingContext V)
    {θ P R π E U i : V} {κ : A.Model}
    (hθ : IsChoicelessInaccessible θ) (hsmall : A.P ∈ hierarchy θ)
    (h : IsSplitForcingSystem θ P π E) (hi : i ∈ θ) (hAP : A.P = P ‘ i)
    (hU : ∀ j ∈ θ, P ‘ j ⊆ U)
    (hsplit : ∀ j ∈ θ, ∀ k ∈ θ, j ⊆ k →
      IsForcingSplitProjection (P ‘ j) (R ‘ j) (P ‘ k) (R ‘ k)
        (π ‘ ⟨j, k⟩ₖ) (E ‘ ⟨j, k⟩ₖ))
    (hκ : κ ⊆ A.check θ)
    (hc : ∀ k ∈ θ, i ⊆ k →
      IsForcingClosedBelow (A.projectionQuotient (P ‘ k) (π ‘ ⟨i, k⟩ₖ))
        (forcingSeparativeOrder (A.projectionQuotient (P ‘ k) (π ‘ ⟨i, k⟩ₖ))
          (A.projectionQuotientOrder (P ‘ k) (R ‘ k) (π ‘ ⟨i, k⟩ₖ))) κ) :
    IsForcingClosedBelow
      (A.projectionQuotient (forcingDirectLimit θ P π E U)
        (forcingThreadCoordinate (forcingDirectLimit θ P π E U) i))
      (forcingSeparativeOrder
        (A.projectionQuotient (forcingDirectLimit θ P π E U)
          (forcingThreadCoordinate (forcingDirectLimit θ P π E U) i))
        (A.projectionQuotientOrder (forcingDirectLimit θ P π E U)
          (forcingThreadOrder θ R (forcingDirectLimit θ P π E U))
          (forcingThreadCoordinate (forcingDirectLimit θ P π E U) i))) κ := by
  let := hθ.1
  have hcf := (A.check_regular_of_small hθ hsmall).2.2
  intro α hα
  apply A.directLimit_quotient_separative_closedAt h hi hAP hU hsplit
  · rw [hcf]
    exact hκ α hα
  · intro k hk hik
    exact hc k hk hik α hα

end ForcingContext
end ZFVP
