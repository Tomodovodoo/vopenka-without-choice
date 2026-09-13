import ZFVP.ModelTheory.InverseLimitProjection
import ZFVP.ModelTheory.LimitSplitProjection
import ZFVP.ModelTheory.QuotientSplitProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Coherent lifts make inverse-limit coordinates split projections with the
same canonical sections as the direct limit. -/
theorem forcingInverseLimit_splitProjection {θ P R π E L U k : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hL : IsCoherentForcingLift θ P R π L)
    (hk : k ∈ θ) (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hsplit : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j →
      IsForcingSplitProjection (P ‘ i) (R ‘ i) (P ‘ j) (R ‘ j)
        (π ‘ ⟨i, j⟩ₖ) (E ‘ ⟨i, j⟩ₖ)) :
    IsForcingSplitProjection (P ‘ k) (R ‘ k) (forcingInverseLimit θ P π U)
      (forcingThreadOrder θ R (forcingInverseLimit θ P π U))
      (forcingThreadCoordinate (forcingInverseLimit θ P π U) k)
      (forcingThreadSection θ P π E k) := by
  have hsec : ∀ p ∈ P ‘ k, forcingSectionThread θ π E k p ∈ forcingInverseLimit θ P π U :=
    fun p hp ↦ forcingDirectLimit_subset θ P π E U _ (forcingSectionThread_mem h hk hp hU)
  have hm : forcingThreadSection θ P π E k ∈ (forcingInverseLimit θ P π U) ^ (P ‘ k) := by
    exact definableGraph_mem_function_of_mapsTo _ _ _ _ hsec
  refine ⟨forcingInverseLimit_coordinate_projection h hL hk hU ?_, hm, ?_, ?_⟩
  · intro j hj p hp q hq hpq
    have hjθ := (IsOrdinal.toIsTransitive (x := θ)).mem_trans hj hk
    let := IsOrdinal.of_mem hk
    exact (hsplit j hjθ k hk (IsOrdinal.toIsTransitive.transitive _ hj)).projection.monotone
      p hp q hq hpq
  · intro p hp
    rw [forcingThreadSection_value hp, forcingThreadCoordinate_value (hsec p hp),
      forcingSectionThread_value hk, forcingSectionValue_self h hk hp]
  · intro f hf p hp
    rw [forcingThreadCoordinate_value hf]
    exact forcingThread_below_section_of_subset h hk (fun _ hx ↦ hx) hsplit hf hp (hsec p hp)

namespace ForcingContext

theorem inverseLimit_quotient_splitProjection (A : ForcingContext V)
    {θ P R π E L U i k : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hL : IsCoherentForcingLift θ P R π L)
    (hi : i ∈ θ) (hk : k ∈ θ) (hik : i ⊆ k) (hAP : A.P = P ‘ i)
    (hU : ∀ j ∈ θ, P ‘ j ⊆ U)
    (hsplit : ∀ j ∈ θ, ∀ l ∈ θ, j ⊆ l →
      IsForcingSplitProjection (P ‘ j) (R ‘ j) (P ‘ l) (R ‘ l)
        (π ‘ ⟨j, l⟩ₖ) (E ‘ ⟨j, l⟩ₖ)) :
    let D := forcingInverseLimit θ P π U
    let ρ := forcingThreadCoordinate D i
    IsForcingSplitProjection
      (A.projectionQuotient (P ‘ k) (π ‘ ⟨i, k⟩ₖ))
      (A.projectionQuotientOrder (P ‘ k) (R ‘ k) (π ‘ ⟨i, k⟩ₖ))
      (A.projectionQuotient D ρ)
      (A.projectionQuotientOrder D (forcingThreadOrder θ R D) ρ)
      (A.projectionQuotientMap D ρ (forcingThreadCoordinate D k))
      (A.projectionQuotientMap (P ‘ k) (π ‘ ⟨i, k⟩ₖ) (forcingThreadSection θ P π E k)) := by
  dsimp only
  have hρ : forcingThreadCoordinate (forcingInverseLimit θ P π U) i ∈
      A.P ^ forcingInverseLimit θ P π U := by
    rw [hAP]
    exact forcingThreadCoordinate_maps hi
  have hτ : (π ‘ ⟨i, k⟩ₖ) ∈ A.P ^ (P ‘ k) := by
    rw [hAP]
    exact (hsplit i hi k hk hik).projection.maps
  apply A.projectionQuotient_splitProjection hρ hτ
    (forcingInverseLimit_splitProjection h hL hk hU hsplit)
  intro q hq
  rw [forcingThreadCoordinate_value hq, forcingThreadCoordinate_value hq]
  exact forcingInverseLimit_project_subset h hq hi hk hik

end ForcingContext
end ZFVP
