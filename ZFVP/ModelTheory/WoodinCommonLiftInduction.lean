import ZFVP.ModelTheory.WoodinCommonLiftDirect
import ZFVP.ModelTheory.WoodinCommonLiftSuccessor
import ZFVP.ModelTheory.WoodinCommonLiftInverse

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinCommonLiftBoundAt_below [Countable V] {δ θ ξ i p c d : V} [IsOrdinal θ] [IsOrdinal ξ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) (hξ : ξ ⊆ θ) (hi : i ∈ ξ)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hc : c ∈ forcingInverseCodePoset θ (woodinIterationPrefix θ))
    (hd : d ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ i)
    (hdc : ⟨d, c ‘ i⟩ₖ ∈ (forcingCodeR (woodinIterationPrefix θ)) ‘ i)
    (hmem : ∀ k ∈ ξ, woodinQuotientBoundRec θ i p f.val k ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ k)
    (hnorm : ∀ k ∈ ξ, IsWoodinBoundNormalizationAt θ i p f.val k)
    (hselected : IsWoodinSelectedThreadDecision θ i f.val c d) :
    ∀ k ∈ ξ, IsWoodinCommonLiftBoundAt θ i p f.val c d k := by
  let := IsOrdinal.of_mem hi
  have hall := transfinite_induction
    (fun k : V ↦ k ∈ ξ → IsWoodinCommonLiftBoundAt θ i p f.val c d k) (by definability) ?_
  · intro k hk
    let := IsOrdinal.of_mem hk
    exact hall (IsOrdinal.toOrdinal k) hk
  intro k ih hk
  have hkθ := hξ k hk
  rcases IsOrdinal.mem_trichotomy (k : V) i with hki | he | hik
  · exact woodinCommonLiftBoundAt_before hki
  · subst i
    exact woodinCommonLiftBoundAt_base hs hkθ hc hd hdc
  have hprev : ∀ l ∈ (k : V), IsWoodinCommonLiftBoundAt θ i p f.val c d l := by
    intro l hl
    let := IsOrdinal.of_mem hl
    exact ih (IsOrdinal.toOrdinal l) hl (IsOrdinal.toIsTransitive.mem_trans hl hk)
  by_cases hsucc : (k : V) = succ (⋃ˢ (k : V))
  · have hkm : ⋃ˢ (k : V) ∈ (k : V) :=
      (congrArg (fun x : V ↦ (⋃ˢ (k : V)) ∈ x) hsucc).mpr (mem_succ_self _)
    have hh := woodinCommonLiftBoundAt_successor hs (hsucc ▸ hkθ) (hsucc ▸ hik) f hc hd hdc
      (hsucc ▸ hmem k hk) (hsucc ▸ hnorm k hk) hselected (hprev _ hkm)
    rwa [← hsucc] at hh
  · by_cases hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix (k : V)))
    · exact woodinCommonLiftBoundAt_direct hs hkθ hik hsucc hinac hc hd hdc (hmem k hk) hprev
    · exact woodinCommonLiftBoundAt_inverse hs hkθ hik hsucc hinac f hc hd hdc
        (hmem k hk) (hnorm k hk) hselected hprev

end ZFVP
