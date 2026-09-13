import ZFVP.ModelTheory.WoodinCommonLiftProjection
import ZFVP.ModelTheory.WoodinInverseFirstCoordinates

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinCommonLift_inverse_first_le {δ θ i p f c d j r b : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) (hj : j ∈ θ) (hi : i ∈ j)
    (hlim : j ≠ succ (⋃ˢ j))
    (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hc : c ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (hd : d ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i)
    (hdc : ⟨d, c ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i)
    (hq : woodinQuotientBoundRec θ i p f j ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j)
    (hprev : ∀ k ∈ j, IsWoodinCommonLiftBoundAt θ i p f c d k)
    (hr : r ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j)
    (hrq : ⟨r, woodinQuotientBoundRec θ i p f j⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ j)
    (hb : b ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i)
    (hbr : ⟨b, ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) ‘ r⟩ₖ ∈
      (forcingCodeR (woodinIterationPrefix θ)) ‘ i)
    (hbd : ⟨b, d⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i) :
    ⟨kpair.π₁ (((forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) ‘ ⟨r, b⟩ₖ),
      kpair.π₁ (c ‘ j)⟩ₖ ∈ forcingInverseCodeOrder j (woodinIterationPrefix j) := by
  let := IsOrdinal.of_mem hj
  have hiθ := IsOrdinal.toIsTransitive.mem_trans hi hj
  have hij : i ⊆ j := IsOrdinal.toIsTransitive.transitive _ hi
  have h0 : j ≠ ∅ := by rintro rfl; exact not_mem_empty hi
  have h := (woodinIterationPrefix_of_stages hs).code
  have hl := h.system.lifts.lift i hiθ j hj hij r hr b hb hbr
  have hcj := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hc).2.1 j hj
  apply (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
  refine ⟨woodinInverse_first_mem hs hj h0 hlim hinac hl.1,
    woodinInverse_first_mem hs hj h0 hlim hinac hcj, ?_⟩
  intro k hk
  have ht := woodinCommonLift_project_le hs hj hi hk hc hd hdc hq
    (woodinQuotientBoundRec_projects_inverse hs hj hi hk hlim hinac hq)
    (hprev k hk) hr hrq hb hbr hbd
  rw [woodinInverse_projection_value hs hj h0 hlim hinac hk hl.1,
    (woodinThread_inverse_coordinate hs hj h0 hlim hinac hc).2 k hk] at ht
  have hsub : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  have hlocal := (woodinIterationPrefix_of_stages (fun l hl ↦ hs l (hsub l hl))).code
  rw [hlocal.tableR.value_of_subset h.tableR (woodinIterationPrefix_extends hsub).subR hk]
  exact ht

end ZFVP
