import ZFVP.ModelTheory.WoodinCommonLiftProjection
import ZFVP.ModelTheory.WoodinDirectLiftCoordinates

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinCommonLiftBoundAt_direct {δ θ i p f c d j : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) (hj : j ∈ θ) (hi : i ∈ j)
    (hlim : j ≠ succ (⋃ˢ j))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hc : c ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (hd : d ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i)
    (hdc : ⟨d, c ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i)
    (hq : woodinQuotientBoundRec θ i p f j ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j)
    (hprev : ∀ k ∈ j, IsWoodinCommonLiftBoundAt θ i p f c d k) :
    IsWoodinCommonLiftBoundAt θ i p f c d j := by
  intro hij r hr hrq b hb hbr hbd
  let := IsOrdinal.of_mem hj
  have hiθ := IsOrdinal.toIsTransitive.mem_trans hi hj
  have h0 : j ≠ ∅ := by rintro rfl; exact not_mem_empty hi
  have h := (woodinIterationPrefix_of_stages hs).code
  have hl := h.system.lifts.lift i hiθ j hj hij r hr b hb hbr
  have hcj := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hc).2.1 j hj
  have hpoint : ∀ k ∈ j,
      ⟨((((forcingCodeL (woodinIterationPrefix θ)) ‘ ⟨i, j⟩ₖ) ‘ ⟨r, b⟩ₖ) ‘ k), (c ‘ j) ‘ k⟩ₖ ∈
        (forcingCodeR (woodinIterationPrefix θ)) ‘ k := by
    intro k hk
    have ht := woodinCommonLift_project_le hs hj hi hk hc hd hdc hq
      (woodinQuotientBoundRec_projects_direct hs hj hi hk hlim hinac hq)
      (hprev k hk) hr hrq hb hbr hbd
    rwa [woodinDirect_projection_value hs hj hk hlim hinac hl.1,
      (woodinThread_direct_coordinate hs hj h0 hlim hinac hc).2 k hk] at ht
  have hrec := woodinIterationRec_direct h0 hlim hinac
  have hP : (forcingCodeP (woodinIterationPrefix θ)) ‘ j =
      forcingDirectLimit j (forcingCodeP (woodinIterationPrefix j))
        (forcingCodeπ (woodinIterationPrefix j)) (forcingCodeE (woodinIterationPrefix j))
        (forcingCodeUniverse (woodinIterationPrefix j)) := by
    rw [woodinIterationPrefix_poset_value hs hj (mem_succ_self j), hrec, kpair.π₁_kpair]
    simp only [forcingDirectCode, forcingThreadCode_poset]
  rw [woodinIterationPrefix_order_value hs hj (mem_succ_self j), hrec, kpair.π₁_kpair]
  simp only [forcingDirectCode, forcingThreadCode_order]
  apply (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
  refine ⟨hP ▸ hl.1, hP ▸ hcj, ?_⟩
  intro k hk
  have hsub : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  have hlocal := (woodinIterationPrefix_of_stages (fun l hl ↦ hs l (hsub l hl))).code
  rw [hlocal.tableR.value_of_subset h.tableR (woodinIterationPrefix_extends hsub).subR hk]
  exact hpoint k hk

end ZFVP
