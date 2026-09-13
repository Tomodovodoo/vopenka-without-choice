import ZFVP.ModelTheory.WoodinPrefixCoordinates
import ZFVP.ModelTheory.InverseSplitProjection
import ZFVP.ModelTheory.QuotientSequenceProjection
import ZFVP.ModelTheory.WoodinUniformTailSupport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {δ θ : V} [IsOrdinal θ]
  (hs : ∀ j ∈ θ, IsWoodinIteration δ (succ j) (kpair.π₁ (woodinIterationRec j))
    (kpair.π₂ (woodinIterationRec j)))
include hs

theorem woodinIterationPrefix_order_value {j k : V} (hj : j ∈ θ) (hk : k ∈ succ j) :
    (forcingCodeR (woodinIterationPrefix θ)) ‘ k =
      (forcingCodeR (kpair.π₁ (woodinIterationRec j))) ‘ k :=
  ((hs j hj).code.tableR.value_of_subset (woodinIterationPrefix_of_stages hs).code.tableR
    (woodinIterationRec_extends_to_prefix hj).subR hk).symm

theorem woodinIterationPrefix_top_value {j k : V} (hj : j ∈ θ) (hk : k ∈ succ j) :
    (forcingCodet (woodinIterationPrefix θ)) ‘ k =
      (forcingCodet (kpair.π₁ (woodinIterationRec j))) ‘ k :=
  ((hs j hj).code.tablet.value_of_subset (woodinIterationPrefix_of_stages hs).code.tablet
    (woodinIterationRec_extends_to_prefix hj).subt hk).symm

theorem woodinInverseCoordinate_split {i : V} (hi : i ∈ θ) :
    IsForcingSplitProjection ((forcingCodeP (woodinIterationPrefix θ)) ‘ i)
      ((forcingCodeR (woodinIterationPrefix θ)) ‘ i)
      (forcingInverseCodePoset θ (woodinIterationPrefix θ)) (forcingInverseCodeOrder θ (woodinIterationPrefix θ))
      (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i)
      (forcingThreadSection θ (forcingCodeP (woodinIterationPrefix θ))
        (forcingCodeπ (woodinIterationPrefix θ)) (forcingCodeE (woodinIterationPrefix θ)) i) := by
  have h := (woodinIterationPrefix_of_stages hs).code
  exact forcingInverseLimit_splitProjection h.system.split h.system.lifts hi h.subset_universe
    (fun a ha b hb hab ↦ h.system.splitProjection ha hb hab)

theorem woodinInverseThread_project {i j d : V} (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j)
    (hd : d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ)) :
    ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) ‘ (d ‘ j) = d ‘ i := by
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  have h := (mem_forcingInverseLimit_iff _ _ _ _ _).mp hd
  rcases IsOrdinal.subset_iff.mp hij with rfl | hij
  · exact (woodinIterationPrefix_of_stages hs).code.system.split.projId hi (h.2.1 i hi)
  · exact h.2.2 j hj i hij hi

theorem ForcingContext.woodinCoordinate_descending {i j α : V}
    (A : ForcingContext V) (hi : i ∈ θ) (hj : j ∈ θ) (hij : i ⊆ j)
    (hP : A.P = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (hR : A.R = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (ho : A.one = (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)
    [IsOrdinal α] (f : ForcingName A.P)
    (hf : IsForcingDescending
      (A.projectionQuotient (forcingInverseCodePoset θ (woodinIterationPrefix θ))
        (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i))
      (forcingSeparativeOrder
        (A.projectionQuotient (forcingInverseCodePoset θ (woodinIterationPrefix θ))
          (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i))
        (A.projectionQuotientOrder (forcingInverseCodePoset θ (woodinIterationPrefix θ))
          (forcingInverseCodeOrder θ (woodinIterationPrefix θ))
          (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i)))
      (A.check α) (A.ofName f)) :
    let μ : ForcingName A.P := ⟨woodinBoundCoordinateName θ i f.val j,
      by simpa only [← hP] using woodinBoundCoordinateName_isName θ i f.val j⟩
    IsForcingDescending
      (A.projectionQuotient ((forcingCodeP (woodinIterationPrefix θ)) ‘ j)
        ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ))
      (forcingSeparativeOrder
        (A.projectionQuotient ((forcingCodeP (woodinIterationPrefix θ)) ‘ j)
          ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ))
        (A.projectionQuotientOrder ((forcingCodeP (woodinIterationPrefix θ)) ‘ j)
          ((forcingCodeR (woodinIterationPrefix θ)) ‘ j)
          ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ))) (A.check α) (A.ofName μ) := by
  have hc := (woodinIterationPrefix_of_stages hs).code
  have hπ := (woodinInverseCoordinate_split hs hi).projection
  have hτ := hc.system.projection hi hj hij
  rw [woodinIterationPrefix_poset_value hs hi (mem_succ_self i),
    woodinIterationPrefix_order_value hs hi (mem_succ_self i), ← hP, ← hR] at hπ hτ
  have hρ := (woodinInverseCoordinate_split hs hj).projection
  have he : ∀ d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ),
      ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) ‘
        ((forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) j) ‘ d) =
          (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i) ‘ d := by
    intro d hd
    rw [forcingThreadCoordinate_value hd, forcingThreadCoordinate_value hd]
    exact woodinInverseThread_project hs hi hj hij hd
  have ht := A.projectionQuotient_name_descending hπ.maps hτ.maps hρ he f hf
  simpa only [woodinBoundCoordinateName, ← hP, ← hR, ← ho] using ht

theorem ForcingContext.woodinCoordinate_value {i j d : V}
    (A : ForcingContext V) (hj : j ∈ θ)
    (hP : A.P = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (hR : A.R = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (ho : A.one = (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName A.P) {α a : A.Model}
    (hf : A.ofName f ∈ A.check (forcingInverseCodePoset θ (woodinIterationPrefix θ)) ^ α)
    (ha : a ∈ α) (hd : d ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (had : (A.ofName f) ‘ a = A.check d) :
    let μ : ForcingName A.P := ⟨woodinBoundCoordinateName θ i f.val j,
      by simpa only [← hP] using woodinBoundCoordinateName_isName θ i f.val j⟩
    (A.ofName μ) ‘ a = A.check (d ‘ j) := by
  let D := forcingInverseCodePoset θ (woodinIterationPrefix θ)
  let ρ := forcingThreadCoordinate D j
  have hρ := (woodinInverseCoordinate_split hs hj).projection.maps
  let := IsFunction.of_mem hρ
  let μ : ForcingName A.P := ⟨woodinBoundCoordinateName θ i f.val j,
    by simpa only [← hP] using woodinBoundCoordinateName_isName θ i f.val j⟩
  have hv : A.ofName μ = compose (A.ofName f) (A.check ρ) := by
    have he := A.forcingCompositionName_value f ⟨checkName A.one ρ, checkName_isName A.top.1 _⟩
    change A.ofName ⟨forcingCompositionName A.P A.R f.val (checkName A.one ρ), _⟩ =
      compose (A.ofName f) (A.check ρ) at he
    simpa only [μ, woodinBoundCoordinateName, ← hP, ← hR, ← ho, ρ, D] using he
  dsimp only
  change (A.ofName μ) ‘ a = _
  rw [hv, value_compose_of_mem_function hf ((A.check_function_iff _ _ _).mpr hρ) ha, had,
    A.check_value ((domain_eq_of_mem_function hρ).symm ▸ hd), forcingThreadCoordinate_value hd]

end ZFVP
