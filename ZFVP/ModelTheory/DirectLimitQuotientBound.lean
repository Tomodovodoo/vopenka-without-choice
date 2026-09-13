import ZFVP.ModelTheory.DirectLimitQuotientClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A target in the direct limit is a section of one coordinate. A separative
bound at that coordinate therefore suffices for a bound in the whole quotient. -/
theorem ForcingContext.directLimit_quotient_separative_of_coordinates (A : ForcingContext V)
    {θ P R π E U i q c : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hi : i ∈ θ) (hAP : A.P = P ‘ i)
    (hU : ∀ j ∈ θ, P ‘ j ⊆ U)
    (hsplit : ∀ j ∈ θ, ∀ k ∈ θ, j ⊆ k →
      IsForcingSplitProjection (P ‘ j) (R ‘ j) (P ‘ k) (R ‘ k)
        (π ‘ ⟨j, k⟩ₖ) (E ‘ ⟨j, k⟩ₖ))
    (hq : A.check q ∈ A.projectionQuotient (forcingDirectLimit θ P π E U)
      (forcingThreadCoordinate (forcingDirectLimit θ P π E U) i))
    (hc : A.check c ∈ A.projectionQuotient (forcingDirectLimit θ P π E U)
      (forcingThreadCoordinate (forcingDirectLimit θ P π E U) i))
    (hbound : ∀ k ∈ θ, i ⊆ k →
      ⟨A.check (q ‘ k), A.check (c ‘ k)⟩ₖ ∈
        forcingSeparativeOrder (A.projectionQuotient (P ‘ k) (π ‘ ⟨i, k⟩ₖ))
          (A.projectionQuotientOrder (P ‘ k) (R ‘ k) (π ‘ ⟨i, k⟩ₖ))) :
    ⟨A.check q, A.check c⟩ₖ ∈
      forcingSeparativeOrder
        (A.projectionQuotient (forcingDirectLimit θ P π E U)
          (forcingThreadCoordinate (forcingDirectLimit θ P π E U) i))
        (A.projectionQuotientOrder (forcingDirectLimit θ P π E U)
          (forcingThreadOrder θ R (forcingDirectLimit θ P π E U))
          (forcingThreadCoordinate (forcingDirectLimit θ P π E U) i)) := by
  let D := forcingDirectLimit θ P π E U
  let ρ := forcingThreadCoordinate D i
  have hρ : ρ ∈ A.P ^ D := by
    rw [hAP]
    exact (forcingDirectLimit_splitProjection h hi hU hsplit).projection.maps
  have hqD := ((A.check_mem_projectionQuotient_iff hρ).mp hq).1
  have hcD := ((A.check_mem_projectionQuotient_iff hρ).mp hc).1
  obtain ⟨hcI, b, hb⟩ := (mem_forcingDirectLimit_iff _ _ _ _ _ _).mp hcD
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hb.1
  obtain ⟨k, hk, hbk, hik⟩ : ∃ k ∈ θ, b ⊆ k ∧ i ⊆ k := by
    rcases IsOrdinal.mem_trichotomy i b with hib | rfl | hbi
    · exact ⟨b, hb.1, subset_refl _, IsOrdinal.toIsTransitive.transitive _ hib⟩
    · exact ⟨i, hi, subset_refl _, subset_refl _⟩
    · exact ⟨i, hi, IsOrdinal.toIsTransitive.transitive _ hbi, subset_refl _⟩
  have hcs := hb.raise ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hcI).2.1 hk hbk
    (fun l hl hkl x hx ↦ h.secComp b hb.1 k hk l hl hbk hkl x hx)
  have hkproj := forcingDirectLimit_splitProjection h hk hU hsplit
  have hτ : (π ‘ ⟨i, k⟩ₖ) ∈ A.P ^ (P ‘ k) := by
    rw [hAP]
    exact (hsplit i hi k hk hik).projection.maps
  have hcomm : ∀ d ∈ D, (π ‘ ⟨i, k⟩ₖ) ‘ ((forcingThreadCoordinate D k) ‘ d) = ρ ‘ d := by
    intro d hd
    rw [forcingThreadCoordinate_value hd, forcingThreadCoordinate_value hd]
    exact forcingInverseLimit_project_subset h (forcingDirectLimit_subset _ _ _ _ _ _ hd) hi hk hik
  have hproj := A.projectionQuotient_splitProjection hρ hτ hkproj hcomm
  have hcK := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hcI).2.1 k hk
  have hcv : (A.projectionQuotientMap D ρ (forcingThreadCoordinate D k)) ‘ (A.check c) = A.check (c ‘ k) := by
    rw [A.projectionQuotientMap_value hkproj.projection.maps hcD hc, forcingThreadCoordinate_value hcD]
  have hcKG := hcv ▸ function_value_mem hproj.projection.maps hc
  have hsection : (A.projectionQuotientMap (P ‘ k) (π ‘ ⟨i, k⟩ₖ)
      (forcingThreadSection θ P π E k)) ‘ (A.check (c ‘ k)) = A.check c := by
    rw [A.projectionQuotientMap_value hkproj.maps hcK hcKG, forcingThreadSection_value hcK]
    congr 1
    apply forcingThread_eq_of_support
      (forcingDirectLimit_subset _ _ _ _ _ _ (forcingSectionThread_mem h hk hcK hU)) hcI
      (forcingSectionThread_support h hk hcK) hcs
    rw [forcingSectionThread_value hk, forcingSectionValue_self h hk hcK]
  rw [← hsection]
  apply (hproj.separative_below hq hcKG).mpr
  rw [A.projectionQuotientMap_value hkproj.projection.maps hqD hq, forcingThreadCoordinate_value hqD]
  exact hbound k hk hik

end ZFVP
