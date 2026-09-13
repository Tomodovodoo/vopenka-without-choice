import ZFVP.ModelTheory.WoodinBoundNormalizedSteps
import ZFVP.ModelTheory.WoodinBoundSuccessorStep
import ZFVP.ModelTheory.WoodinBoundInverseStep
import ZFVP.ModelTheory.WoodinHistoryQuotientClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The successor step wants closure at the prefix of `succ k`, while the stage
hypotheses give it one stage at a time. This repackages the stage hypotheses. -/
theorem hasWoodinQuotientClosure_prefix_of_stages {δ θ k : V} [IsOrdinal θ] [IsOrdinal k]
    (hs : ∀ l ∈ θ, IsWoodinIteration δ (succ l) (kpair.π₁ (woodinIterationRec l))
      (kpair.π₂ (woodinIterationRec l)))
    (hc : ∀ l ∈ θ, HasWoodinQuotientClosure (succ l) (kpair.π₁ (woodinIterationRec l))
      (kpair.π₂ (woodinIterationRec l)))
    (hk : succ k ∈ θ) :
    HasWoodinQuotientClosure (succ k) (woodinIterationPrefix (succ k))
      (woodinIterationCardinalPrefix (succ k)) := by
  refine woodinIterationPrefix_quotient_closure (δ := δ) (fun l hl ↦ ?_) (fun l hl ↦ ?_)
  · exact hs l (IsOrdinal.toIsTransitive.mem_trans hl hk)
  · exact hc l (IsOrdinal.toIsTransitive.mem_trans hl hk)

/-- Transfinite induction over the stage index assembling the four proved steps of
the canonical quotient bound, using closure only at earlier completed stages. -/
theorem woodinQuotientBound_all_stages [Countable V] {δ θ i p α : V} [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hc : ∀ k ∈ θ, HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hi : i ∈ θ) (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientSequence θ i p f.val α) :
    ∀ j ∈ θ, IsWoodinNormalizedQuotientBoundAt θ i p f.val α j := by
  let := IsOrdinal.of_mem hi
  have hall := transfinite_induction
    (fun j : V ↦ j ∈ θ → IsWoodinNormalizedQuotientBoundAt θ i p f.val α j)
    (by definability) ?_
  · intro j hj
    let := IsOrdinal.of_mem hj
    exact hall (IsOrdinal.toOrdinal j) hj
  intro j ih hj
  have hprevn : ∀ l ∈ (j : V), IsWoodinNormalizedQuotientBoundAt θ i p f.val α l := by
    intro l hl
    let := IsOrdinal.of_mem hl
    exact ih (IsOrdinal.toOrdinal l) hl (IsOrdinal.toIsTransitive.mem_trans hl hj)
  have hprev : ∀ l ∈ (j : V), IsWoodinQuotientBoundAt θ i p f.val α l :=
    fun l hl ↦ (hprevn l hl).1
  by_cases hji : (j : V) ∈ succ i
  · rcases mem_succ_iff.mp hji with hje | hji'
    · subst hje
      exact woodinQuotientBoundAt_base_normalized hs hi hp f hf
    · exact woodinQuotientBoundAt_before_base_normalized hs hi hji' hp
  have hij : i ∈ (j : V) := by
    rcases IsOrdinal.mem_trichotomy i (j : V) with hij | he | hji'
    · exact hij
    · exact False.elim (hji (he ▸ mem_succ_self i))
    · exact False.elim (hji (mem_succ_iff.mpr (Or.inr hji')))
  by_cases hsucc : (j : V) = succ (⋃ˢ (j : V))
  · have hkprev : ⋃ˢ (j : V) ∈ (j : V) :=
      (congrArg (fun x : V ↦ (⋃ˢ (j : V)) ∈ x) hsucc).mpr (mem_succ_self (⋃ˢ (j : V)))
    let := IsOrdinal.of_mem hkprev
    have hkθ : succ (⋃ˢ (j : V)) ∈ θ := by rw [← hsucc]; exact hj
    have hik : i ∈ succ (⋃ˢ (j : V)) := by rw [← hsucc]; exact hij
    have hprev' : ∀ l ∈ succ (⋃ˢ (j : V)), IsWoodinQuotientBoundAt θ i p f.val α l := by
      rw [← hsucc]; exact hprev
    have hclosure := hasWoodinQuotientClosure_prefix_of_stages hs hc hkθ
    rw [hsucc]
    exact woodinQuotientBoundAt_successor_normalized hs hkθ hik hclosure hα hp f hf hprev'
  · by_cases hinac :
      IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix (j : V)))
    · exact woodinQuotientBoundAt_direct_normalized hs hj hij hsucc hinac hα hp f hf hprev
    · exact woodinQuotientBoundAt_inverse_normalized hs hj hij hsucc hinac (hc _ hj) hα hp f hf hprevn

theorem woodinQuotientBoundAt_all_stages [Countable V] {δ θ i p α : V} [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hc : ∀ k ∈ θ, HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hi : i ∈ θ) (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientSequence θ i p f.val α) :
    ∀ j ∈ θ, IsWoodinQuotientBoundAt θ i p f.val α j :=
  fun j hj ↦ (woodinQuotientBound_all_stages hs hc hi hα hp f hf j hj).1

/-- The whole bound history is a condition of the inverse limit poset at `θ` and it
restricts to `p` at coordinate `i`. -/
theorem woodinQuotientBoundHistory_mem_and_projects [Countable V] {δ θ i p α : V}
    [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hc : ∀ k ∈ θ, HasWoodinQuotientClosure (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hi : i ∈ θ) (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i)
    (hp : p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
    (f : ForcingName ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i))
    (hf : ForcesWoodinQuotientSequence θ i p f.val α) :
    woodinQuotientBoundHistory θ i p f.val θ ∈
        forcingInverseCodePoset θ (woodinIterationPrefix θ) ∧
      (forcingThreadCoordinate (forcingInverseCodePoset θ (woodinIterationPrefix θ)) i) ‘
        (woodinQuotientBoundHistory θ i p f.val θ) = p :=
  woodinQuotientBoundHistory_inverse_condition hs hi
    (fun j hj ↦ (woodinQuotientBoundAt_all_stages hs hc hi hα hp f hf j hj).1)

end ZFVP
