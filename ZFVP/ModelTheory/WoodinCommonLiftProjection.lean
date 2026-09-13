import ZFVP.ModelTheory.WoodinCommonLiftInvariant

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinCommonLift_project_le {δ θ i p f c d j r b k : V} [IsOrdinal θ]
    (hs : ∀ l ∈ θ, IsWoodinIteration δ (succ l) (kpair.π₁ (woodinIterationRec l))
      (kpair.π₂ (woodinIterationRec l))) (hj : j ∈ θ) (hi : i ∈ j) (hk : k ∈ j)
    (hc : c ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (hd : d ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i)
    (hdc : ⟨d, c ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i)
    (hq : woodinQuotientBoundRec θ i p f j ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j)
    (hproj : ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨k, j⟩ₖ) ‘
      (woodinQuotientBoundRec θ i p f j) = woodinQuotientBoundRec θ i p f k)
    (hprev : IsWoodinCommonLiftBoundAt θ i p f c d k)
    (hr : r ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j)
    (hrq : ⟨r, woodinQuotientBoundRec θ i p f j⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ j)
    (hb : b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i)
    (hbr : ⟨b, ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) ‘ r⟩ₖ ∈
      (forcingCodeR (woodinIterationPrefix θ)) ‘ i)
    (hbd : ⟨b, d⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i) :
    ⟨((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨k, j⟩ₖ) ‘
      (((forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) ‘ ⟨r, b⟩ₖ), c ‘ k⟩ₖ ∈
      (forcingCodeR (woodinIterationPrefix θ)) ‘ k := by
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hk
  have hiθ := IsOrdinal.toIsTransitive.mem_trans hi hj
  have hkθ := IsOrdinal.toIsTransitive.mem_trans hk hj
  have hij : i ⊆ j := IsOrdinal.toIsTransitive.transitive _ hi
  have hkj : k ⊆ j := IsOrdinal.toIsTransitive.transitive _ hk
  have h := (woodinIterationPrefix_of_stages hs).code.system
  by_cases hki : k ∈ i
  · have hki' : k ⊆ i := IsOrdinal.toIsTransitive.transitive _ hki
    have hl := h.lifts.lift i hiθ j hj hij r hr b hb hbr
    rw [← h.split.projComp k hkθ i hiθ j hj hki' hij _ hl.1, hl.2.2]
    have hci := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hc).2.1 i hiθ
    have hbc := (h.order.preorder i hiθ).2.2 b hb d hd _ hci hbd hdc
    have hbc' := h.order.projMono k hkθ i hiθ hki' b hb _ hci hbc
    rwa [woodinInverseThread_project hs hkθ hiθ hki' hc] at hbc'
  · have hik : i ⊆ k := by
      rcases IsOrdinal.mem_trichotomy k i with hki' | he | hik
      · exact (hki hki').elim
      · subst k; exact fun _ hx ↦ hx
      · exact IsOrdinal.toIsTransitive.transitive _ hik
    rw [h.lifts.commute i hiθ k hkθ j hj hik hkj r hr b hb hbr]
    apply hprev hik _ (h.split.projMaps k hkθ j hj hkj r hr) ?_ b hb ?_ hbd
    · have ht := h.order.projMono k hkθ j hj hkj r hr _ hq hrq
      rwa [hproj] at ht
    · rwa [h.split.projComp i hiθ k hkθ j hj hik hkj r hr]

end ZFVP
