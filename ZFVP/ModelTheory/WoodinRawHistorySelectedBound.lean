import ZFVP.ModelTheory.WoodinCommonLiftRawOrder
import ZFVP.ModelTheory.QuotientLiftCompatibility

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 600000 in
theorem ForcingContext.woodinRawHistory_le_selected [Countable V]
    {δ θ ξ i p c t : V} [IsOrdinal θ] [IsOrdinal ξ]
    (A : ForcingContext V)
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) (hξ : ξ ⊆ θ) (hi : i ∈ ξ)
    (hP : A.P = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (hR : A.R = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (ho : A.one = (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName A.P) (hpG : p ∈ A.G)
    (hc : c ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (hcG : c ‘ i ∈ A.G)
    {X a : A.Model}
    (hf : A.ofName f ∈ A.check (forcingInverseCodePoset θ (woodinIterationPrefix θ)) ^ X)
    (ha : a ∈ X) (hac : (A.ofName f) ‘ a = A.check c)
    (ht : t ∈ forcingInverseCodePoset ξ (woodinIterationPrefix ξ))
    (htc : ∀ k ∈ ξ, t ‘ k = c ‘ k)
    (hmem : ∀ k ∈ ξ, woodinQuotientBoundRec θ i p f.val k ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ k)
    (hnorm : ∀ k ∈ ξ, IsWoodinBoundNormalizationAt θ i p f.val k) :
    let D := forcingInverseCodePoset ξ (woodinIterationPrefix ξ)
    let S := forcingInverseCodeOrder ξ (woodinIterationPrefix ξ)
    let π := forcingThreadCoordinate D i
    ⟨A.check (woodinQuotientBoundHistory θ i p f.val ξ), A.check t⟩ₖ ∈
      forcingSeparativeOrder (A.projectionQuotient D π) (A.projectionQuotientOrder D S π) := by
  let hssub := fun k hk ↦ hs k (hξ k hk)
  have hlocal := (woodinIterationPrefix_of_stages hssub).code
  have hglobal := (woodinIterationPrefix_of_stages hs).code
  have hext := woodinIterationPrefix_extends hξ
  have hAP : A.P = (forcingCodeP (woodinIterationPrefix ξ)) ‘ i :=
    hP.trans (woodinIterationPrefix_poset_value hssub hi (mem_succ_self i)).symm
  have hAR : A.R = (forcingCodeR (woodinIterationPrefix ξ)) ‘ i :=
    hR.trans (woodinIterationPrefix_order_value hssub hi (mem_succ_self i)).symm
  have hAPg : A.P = (forcingCodeP (woodinIterationPrefix θ)) ‘ i :=
    hP.trans (woodinIterationPrefix_poset_value hs (hξ i hi) (mem_succ_self i)).symm
  have hARg : A.R = (forcingCodeR (woodinIterationPrefix θ)) ‘ i :=
    hR.trans (woodinIterationPrefix_order_value hs (hξ i hi) (mem_succ_self i)).symm
  let D := forcingInverseCodePoset ξ (woodinIterationPrefix ξ)
  let S := forcingInverseCodeOrder ξ (woodinIterationPrefix ξ)
  let π := forcingThreadCoordinate D i
  let L := forcingLimitLift D A.P ξ (forcingCodeπ (woodinIterationPrefix ξ))
    (forcingCodeL (woodinIterationPrefix ξ)) i
  have hπ := (woodinInverseCoordinate_split hssub hi).projection.maps
  rw [← hAP] at hπ
  have hmemlocal : ∀ k ∈ ξ, woodinQuotientBoundRec θ i p f.val k ∈
      (forcingCodeP (woodinIterationPrefix ξ)) ‘ k := by
    intro k hk
    rw [hlocal.tableP.value_of_subset hglobal.tableP hext.subP hk]
    exact hmem k hk
  have hq := woodinQuotientBoundHistory_inverse_condition (ξ := θ) hssub hi hmemlocal
  have hqG := (A.check_mem_projectionQuotient_iff hπ).mpr ⟨hq.1, hq.2.symm ▸ hpG⟩
  have htG : A.check t ∈ A.projectionQuotient D π := by
    apply (A.check_mem_projectionQuotient_iff hπ).mpr
    refine ⟨ht, ?_⟩
    rw [forcingThreadCoordinate_value ht, htc i hi]
    exact hcG
  obtain ⟨d, hdG, hdc, hselected⟩ := A.exists_woodinSelectedThreadDecision_below hP hR ho f hf ha hac hcG
  have hd : d ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i := hAPg ▸ A.generic.1.1 d hdG
  have hdc' := hARg ▸ hdc
  let f₀ : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i) := ⟨f.val, hP ▸ f.property⟩
  have hcommon := woodinCommonLiftBoundAt_below hs hξ hi f₀ hc hd hdc' hmem hnorm hselected
  have hL : ∀ r ∈ D, ∀ b ∈ A.P, ⟨b, π ‘ r⟩ₖ ∈ A.R →
      L ‘ ⟨r, b⟩ₖ ∈ D ∧ ⟨L ‘ ⟨r, b⟩ₖ, r⟩ₖ ∈ S ∧ π ‘ (L ‘ ⟨r, b⟩ₖ) = b := by
    intro r hr b hb hbr
    have hbr' : ⟨b, r ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix ξ)) ‘ i := by
      rwa [hAR, forcingThreadCoordinate_value hr] at hbr
    have hh := forcingLimitLift_inverse_lift hlocal.system.split hlocal.system.lifts hr hi
      (hAP ▸ hb) hbr' hlocal.subset_universe ?_
    · change L ‘ ⟨r, b⟩ₖ ∈ D ∧ _
      have he : L = forcingLimitLift D ((forcingCodeP (woodinIterationPrefix ξ)) ‘ i) ξ
          (forcingCodeπ (woodinIterationPrefix ξ)) (forcingCodeL (woodinIterationPrefix ξ)) i := by
        simp only [L, hAP]
      rw [he]
      refine ⟨hh.1, hh.2.1, ?_⟩
      exact (forcingThreadCoordinate_value (i := i) hh.1).trans hh.2.2
    · intro k hk x hx y hy hxy
      let := IsOrdinal.of_mem hi
      exact hlocal.system.order.projMono k (IsOrdinal.toIsTransitive.mem_trans hk hi) i hi
        (IsOrdinal.toIsTransitive.transitive _ hk) x hx y hy hxy
  apply A.projectionQuotient_separative_of_lift hπ hL hqG htG hdG
  intro r hr hrq b hb hbr hbd
  rw [forcingLimitLift_value hr hb]
  apply woodinCommonLift_raw_le hs hξ hi hc hd hdc' ht htc hcommon hr hrq (hAPg ▸ hb) ?_ (hARg ▸ hbd)
  rwa [forcingThreadCoordinate_value hr, hARg] at hbr

end ZFVP
