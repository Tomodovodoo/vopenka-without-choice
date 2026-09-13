import ZFVP.ModelTheory.WoodinCanonicalBoundInduction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

set_option maxHeartbeats 600000 in
theorem woodinRawHistory_bound [Countable V] {δ θ i p α : V} [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hc : ∀ k ∈ θ, HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hi : i ∈ θ) (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientSequence θ i p f.val α)
    (G : Set V) (hG : IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G) (hpG : p ∈ G) :
    let A : ForcingContext V := ⟨_, _, _, G,
      (hs i hi).code.system.order.preorder i (mem_succ_self i),
      (hs i hi).code.system.tops.top i (mem_succ_self i), hG⟩
    let D := forcingInverseCodePoset θ (woodinIterationPrefix θ)
    let U := forcingInverseCodeOrder θ (woodinIterationPrefix θ)
    let π := forcingThreadCoordinate D i
    A.check (woodinQuotientBoundHistory θ i p f.val θ) ∈ A.projectionQuotient D π ∧
      ∀ a ∈ A.check α,
        ⟨A.check (woodinQuotientBoundHistory θ i p f.val θ), (A.ofName f) ‘ a⟩ₖ ∈
          forcingSeparativeOrder (A.projectionQuotient D π) (A.projectionQuotientOrder D U π) := by
  let A : ForcingContext V := ⟨_, _, _, G,
    (hs i hi).code.system.order.preorder i (mem_succ_self i),
    (hs i hi).code.system.tops.top i (mem_succ_self i), hG⟩
  have hp := hG.1.1 p hpG
  have hn := woodinQuotientBound_all_stages hs hc hi hα hp f hf
  have hq := woodinQuotientBoundHistory_mem_and_projects hs hc hi hα hp f hf
  have hπ := (woodinInverseCoordinate_split hs hi).projection.maps
  rw [woodinIterationPrefix_poset_value hs hi (mem_succ_self i)] at hπ
  refine ⟨(A.check_mem_projectionQuotient_iff hπ).mpr ⟨hq.1, hq.2.symm ▸ hpG⟩, ?_⟩
  intro a ha
  have hd := woodinQuotientSequence_semantics hs hi f hf G hG hpG
  have hfun := mem_function_of_mem_function_of_subset hd.1 sep_subset
  have hva := function_value_mem hd.1 ha
  obtain ⟨c, hcD, hval⟩ := (A.mem_check_iff _ _).mp (sep_subset _ hva)
  have hcG := ((A.check_mem_projectionQuotient_iff hπ).mp (hval ▸ hva)).2
  rw [forcingThreadCoordinate_value hcD] at hcG
  rw [hval]
  exact A.woodinRawHistory_le_selected hs (fun _ hx ↦ hx) hi rfl rfl rfl f hpG hcD hcG hfun ha hval
    hcD (fun _ _ ↦ rfl) (fun k hk ↦ (hn k hk).1.1) (fun k hk ↦ (hn k hk).2)

end ZFVP
