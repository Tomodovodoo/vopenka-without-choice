import ZFVP.ModelTheory.WoodinEventualEmptyTails
import ZFVP.ModelTheory.WoodinDirectBoundSmall
import ZFVP.ModelTheory.WoodinBoundSupport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinQuotientBound_direct_mem [Countable V] {δ θ i j p α : V}
    [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hj : j ∈ θ) (hi : i ∈ j) (hlim : j ≠ succ (⋃ˢ j))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ∀ (A : ForcingContext V),
      A.P = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i →
      A.R = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i →
      A.one = (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i → p ∈ A.G →
      ∀ g : ForcingName A.P, g.val = f.val →
        A.ofName g ∈ A.check (forcingInverseCodePoset θ (woodinIterationPrefix θ)) ^ A.check α)
    (hmem : ∀ k ∈ j, woodinQuotientBoundRec θ i p f.val k ∈
      (forcingCodeP (woodinIterationPrefix θ)) ‘ k) :
    woodinQuotientBoundRec θ i p f.val j ∈ (forcingCodeP (woodinIterationPrefix θ)) ‘ j := by
  let := IsOrdinal.of_mem hj
  have hsj := fun k hk ↦ hs k (IsOrdinal.toIsTransitive.mem_trans hk hj)
  have hcj := (woodinIterationPrefix_of_stages hsj).code
  have hcθ := (woodinIterationPrefix_of_stages hs).code
  have hsub : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  have hmemj : ∀ k ∈ j, woodinQuotientBoundRec θ i p f.val k ∈
      (forcingCodeP (woodinIterationPrefix j)) ‘ k := by
    intro k hk
    rw [hcj.tableP.value_of_subset hcθ.tableP (woodinIterationPrefix_extends hsub).subP hk]
    exact hmem k hk
  obtain ⟨hji, hB, hX⟩ := woodinBound_direct_small hs hj hi hlim hinac hα
  obtain ⟨b, hb, hib, hS, hI⟩ := woodinBound_eventual_empty_tails hs hj hi hlim hinac hji hB hX hp f hf
  have hhistory := woodinQuotientBoundHistory_mem_direct_of_empty_tails hsj hi hmemj hb hib hS hI
  have h0 : j ≠ ∅ := by rintro rfl; exact not_mem_empty hi
  rw [woodinQuotientBoundRec_direct hi hlim hinac,
    woodinIterationPrefix_poset_value hs hj (mem_succ_self j),
    woodinIterationRec_direct h0 hlim hinac, kpair.π₁_kpair]
  simpa only [forcingDirectCode, forcingThreadCode_poset] using hhistory

end ZFVP
