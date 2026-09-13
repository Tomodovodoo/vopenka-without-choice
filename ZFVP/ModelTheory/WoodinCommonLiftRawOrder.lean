import ZFVP.ModelTheory.WoodinCommonLiftInduction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinCommonLift_raw_le {δ θ ξ i p f c d t r b : V} [IsOrdinal θ] [IsOrdinal ξ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) (hξ : ξ ⊆ θ) (hi : i ∈ ξ)
    (hc : c ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (hd : d ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i)
    (hdc : ⟨d, c ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i)
    (ht : t ∈ forcingInverseCodePoset ξ (woodinIterationPrefix ξ))
    (htc : ∀ k ∈ ξ, t ‘ k = c ‘ k)
    (hcommon : ∀ k ∈ ξ, IsWoodinCommonLiftBoundAt θ i p f c d k)
    (hr : r ∈ forcingInverseCodePoset ξ (woodinIterationPrefix ξ))
    (hrq : ⟨r, woodinQuotientBoundHistory θ i p f ξ⟩ₖ ∈ forcingInverseCodeOrder ξ (woodinIterationPrefix ξ))
    (hb : b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i)
    (hbr : ⟨b, r ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i)
    (hbd : ⟨b, d⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i) :
    ⟨forcingThreadSplice ξ (forcingCodeπ (woodinIterationPrefix ξ))
      (forcingCodeL (woodinIterationPrefix ξ)) r i b, t⟩ₖ ∈
        forcingInverseCodeOrder ξ (woodinIterationPrefix ξ) := by
  classical
  let := IsOrdinal.of_mem hi
  have hlocal := (woodinIterationPrefix_of_stages (fun k hk ↦ hs k (hξ k hk))).code
  have hglobal := (woodinIterationPrefix_of_stages hs).code
  have hext := woodinIterationPrefix_extends hξ
  have hPi := hlocal.tableP.value_of_subset hglobal.tableP hext.subP hi
  have hRi := hlocal.tableR.value_of_subset hglobal.tableR hext.subR hi
  have hb' := hPi.symm ▸ hb
  have hbr' := hRi.symm ▸ hbr
  have hr' := (mem_forcingInverseLimit_iff _ _ _ _ _).mp hr
  have hrq' := (mem_forcingThreadOrder_iff _ _ _ _ _).mp hrq
  apply (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
  refine ⟨forcingThreadSplice_mem hlocal.system.split hlocal.system.lifts hr hi hb' hbr'
    hlocal.subset_universe, ht, ?_⟩
  intro k hk
  let := IsOrdinal.of_mem hk
  rw [htc k hk]
  by_cases hki : k ∈ i
  · rw [forcingThreadSplice_value hk]
    simp only [forcingSpliceValue, ite_eq_left hki]
    have hki' : k ⊆ i := IsOrdinal.toIsTransitive.transitive _ hki
    have hci := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hc).2.1 i (hξ i hi)
    have hbc := (hglobal.system.order.preorder i (hξ i hi)).2.2 b hb d hd _ hci hbd hdc
    have hbc' := hglobal.system.order.projMono k (hξ k hk) i (hξ i hi) hki' b hb _ hci hbc
    rw [woodinInverseThread_project hs (hξ k hk) (hξ i hi) hki' hc] at hbc'
    rw [hlocal.tableπ.value_of_subset hglobal.tableπ hext.subπ
      (mem_prod_iff.mpr ⟨k, hk, i, hi, rfl⟩),
      hlocal.tableR.value_of_subset hglobal.tableR hext.subR hk]
    exact hbc'
  · have hik : i ⊆ k := by
      rcases IsOrdinal.mem_trichotomy k i with hki' | he | hik
      · exact (hki hki').elim
      · subst k; exact subset_refl _
      · exact IsOrdinal.toIsTransitive.transitive _ hik
    rw [forcingThreadSplice_coordinate hk hik,
      hlocal.tableL.value_of_subset hglobal.tableL hext.subL (mem_prod_iff.mpr ⟨i, hi, k, hk, rfl⟩),
      hlocal.tableR.value_of_subset hglobal.tableR hext.subR hk]
    have hrk : r ‘ k ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ k := by
      rw [← hlocal.tableP.value_of_subset hglobal.tableP hext.subP hk]
      exact hr'.2.1 k hk
    apply hcommon k hk hik _ hrk ?_ b hb ?_ hbd
    · have hh := hrq'.2.2 k hk
      rwa [woodinQuotientBoundHistory_value hk,
        hlocal.tableR.value_of_subset hglobal.tableR hext.subR hk] at hh
    · rw [← hlocal.tableπ.value_of_subset hglobal.tableπ hext.subπ
        (mem_prod_iff.mpr ⟨i, hi, k, hk, rfl⟩),
        forcingInverseLimit_project_subset hlocal.system.split hr hi hk hik]
      exact hbr

end ZFVP
