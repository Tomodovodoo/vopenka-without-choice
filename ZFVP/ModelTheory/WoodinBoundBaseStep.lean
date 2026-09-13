import ZFVP.ModelTheory.WoodinBoundInvariantSemantics
import ZFVP.ModelTheory.WoodinBoundCoherence
import ZFVP.ModelTheory.IdentityQuotientClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {δ θ i p f α : V} [IsOrdinal θ]
  (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
    (kpair.π₂ (woodinIterationRec k))) (hi : i ∈ θ)
include hs hi

theorem woodinQuotientBoundAt_before_base {j : V} (hji : j ∈ i)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i) :
    IsWoodinQuotientBoundAt θ i p f α j := by
  let := IsOrdinal.of_mem hi
  have hj := IsOrdinal.toIsTransitive.mem_trans hji hi
  have hp' : p ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i := by
    rwa [woodinIterationPrefix_poset_value hs hi (mem_succ_self i)]
  refine ⟨?_, fun hij ↦ False.elim (mem_irrefl j (hij j hji))⟩
  rw [woodinQuotientBoundRec_before_base hs hi (mem_succ_iff.mpr (Or.inr hji)) hp']
  exact function_value_mem ((woodinIterationPrefix_of_stages hs).code.system.functions.projection
    j hj i hi (IsOrdinal.toIsTransitive.transitive _ hji)) hp'

theorem woodinQuotientBoundAt_base [Countable V] [IsOrdinal α]
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientSequence θ i p f.val α) :
    IsWoodinQuotientBoundAt θ i p f.val α i := by
  let := IsOrdinal.of_mem hi
  have hPi := woodinIterationPrefix_poset_value hs hi (mem_succ_self i)
  have hRi := woodinIterationPrefix_order_value hs hi (mem_succ_self i)
  have hc := (woodinIterationPrefix_of_stages hs).code
  have hm := hc.system.functions.projection i hi i hi (subset_refl i)
  have he : ∀ q ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i,
      ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, i⟩ₖ) ‘ q = q := by
    intro q hq
    exact hc.system.split.projId hi (hPi.symm ▸ hq)
  apply (woodinQuotientBoundAt_iff_generics hs hi hi (subset_refl _) hp f).mpr
  refine ⟨?_, ?_⟩
  · rw [woodinQuotientBoundRec_base, hPi]
    exact hp
  · intro G hG hpG
    let A : ForcingContext V := ⟨_, _, _, G,
      (hs i hi).code.system.order.preorder i (mem_succ_self i),
      (hs i hi).code.system.tops.top i (mem_succ_self i), hG⟩
    have hdesc := woodinQuotientSequence_semantics hs hi f hf G hG hpG
    have hd := A.woodinCoordinate_descending hs hi hi (subset_refl _) rfl rfl rfl f hdesc
    rw [hPi, hRi] at hd
    rw [hPi] at hm
    have hpQ : A.check p ∈ A.projectionQuotient A.P ((forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨i, i⟩ₖ) :=
      (A.check_mem_projectionQuotient_iff hm).mpr ⟨hp, (he p hp).symm ▸ hpG⟩
    dsimp only
    rw [woodinQuotientBoundRec_base, hPi, hRi]
    exact ⟨hpQ, fun a ha ↦ A.identityQuotient_separative hm he hpQ (function_value_mem hd.1 ha)⟩

end ZFVP
