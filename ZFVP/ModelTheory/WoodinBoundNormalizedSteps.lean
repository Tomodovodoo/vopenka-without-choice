import ZFVP.ModelTheory.WoodinBoundNormalization
import ZFVP.ModelTheory.WoodinBoundBaseStep
import ZFVP.ModelTheory.WoodinBoundDirectStep

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinBoundNormalizationAt_before_base {θ i p f j : V} [IsOrdinal i]
    (hji : j ∈ i) : IsWoodinBoundNormalizationAt θ i p f j := by
  intro hij
  exact False.elim (mem_irrefl i (IsOrdinal.toIsTransitive.mem_trans hij hji))

theorem woodinBoundNormalizationAt_base (θ i p f : V) :
    IsWoodinBoundNormalizationAt θ i p f i := by
  intro h
  exact False.elim (mem_irrefl i h)

theorem woodinBoundNormalizationAt_direct {θ i p f j : V}
    (hlim : j ≠ succ (⋃ˢ j))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j))) :
    IsWoodinBoundNormalizationAt θ i p f j := by
  exact fun _ ↦ ⟨fun h ↦ (hlim h).elim, fun _ h ↦ (h hinac).elim⟩

theorem woodinQuotientBoundAt_before_base_normalized {δ θ i p f α j : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) (hi : i ∈ θ) (hji : j ∈ i)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i) :
    IsWoodinNormalizedQuotientBoundAt θ i p f α j := by
  let := IsOrdinal.of_mem hi
  exact ⟨woodinQuotientBoundAt_before_base hs hi hji hp,
    woodinBoundNormalizationAt_before_base hji⟩

theorem woodinQuotientBoundAt_base_normalized [Countable V] {δ θ i p α : V}
    [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k))) (hi : i ∈ θ)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientSequence θ i p f.val α) :
    IsWoodinNormalizedQuotientBoundAt θ i p f.val α i :=
  ⟨woodinQuotientBoundAt_base hs hi hp f hf, woodinBoundNormalizationAt_base θ i p f.val⟩

theorem woodinQuotientBoundAt_direct_normalized [Countable V] {δ θ i p α j : V}
    [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hj : j ∈ θ) (hi : i ∈ j) (hlim : j ≠ succ (⋃ˢ j))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientSequence θ i p f.val α)
    (hprev : ∀ k ∈ j, IsWoodinQuotientBoundAt θ i p f.val α k) :
    IsWoodinNormalizedQuotientBoundAt θ i p f.val α j :=
  ⟨woodinQuotientBoundAt_direct hs hj hi hlim hinac hα hp f hf hprev,
    woodinBoundNormalizationAt_direct hlim hinac⟩

end ZFVP
