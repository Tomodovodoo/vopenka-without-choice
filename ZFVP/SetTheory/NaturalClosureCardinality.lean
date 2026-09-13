import ZFVP.SetTheory.NaturalIteration
import ZFVP.SetTheory.FiniteSequencesCardinality
import ZFVP.SetTheory.RegularUnions

/-! Cardinal bounds for finite sequences and countable definable closure. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem naturalIteration_union_cardLE (hAC : InternalChoice V) {lam A : V}
    (hlam : IsInitialOrdinal lam) (hω : (ω : V) ⊆ lam)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) (hA : A ≤# lam)
    (hstep : ∀ X, X ≤# lam → F X ≤# lam) :
    ⋃ˢ range (naturalIterationGraph F hF A) ≤# lam := by
  have hi := naturalIteration_invariant F hF A (fun X ↦ X ≤# lam) (by definability) hA hstep
  have hc : ∀ n ∈ (ω : V), (naturalIterationGraph F hF A) ‘ n ≤# lam := by
    intro n hn
    rw [naturalIterationGraph_value F hF A hn]
    exact hi n hn
  exact (sUnion_range_cardLE_prod hAC (domain_naturalIterationGraph F hF A) hc).trans
    (prod_cardLE_of_cardLE_initial hlam hω (cardLE_of_subset hω) (CardLE.refl lam))

theorem function_power_cardLE_of_cardLE_initial {lam A : V}
    (hlam : IsInitialOrdinal lam) (hω : (ω : V) ⊆ lam) (hA : A ≤# lam) :
    ∀ n ∈ (ω : V), A ^ n ≤# lam := by
  apply naturalNumber_induction (fun n ↦ A ^ n ≤# lam) (by definability)
  · exact function_power_zero_cardLE ⟨∅, hω ∅ empty_mem_ω⟩
  · intro n _ ih
    exact (function_power_succ_cardLE A n).trans
      (prod_cardLE_of_cardLE_initial hlam hω ih hA)

theorem finiteSequences_cardLE_of_cardLE_initial (hAC : InternalChoice V) {lam A : V}
    (hlam : IsInitialOrdinal lam) (hω : (ω : V) ⊆ lam) (hA : A ≤# lam) :
    finiteSequences A ≤# lam := by
  let C := definableGraph (ω : V) (fun n ↦ A ^ n) (by definability)
  let : IsFunction C := definableGraph_isFunction _ _ _
  have hd : domain C = (ω : V) := domain_definableGraph _ _ _
  have hv : ∀ n ∈ (ω : V), C ‘ n = A ^ n := fun n hn ↦ value_definableGraph _ _ _ hn
  have hc : ∀ n ∈ (ω : V), C ‘ n ≤# lam := by
    intro n hn
    rw [hv n hn]
    exact function_power_cardLE_of_cardLE_initial hlam hω hA n hn
  have hsub : finiteSequences A ⊆ ⋃ˢ range C := by
    intro s hs
    obtain ⟨n, hn, hsn⟩ := (mem_finiteSequences_iff A s).mp hs
    refine mem_sUnion_iff.mpr ⟨A ^ n, ?_, hsn⟩
    rw [← hv n hn]
    exact value_mem_range (IsFunction.mem_function C) (hd ▸ hn)
  exact ((cardLE_of_subset hsub).trans (sUnion_range_cardLE_prod hAC hd hc)).trans
    (prod_cardLE_of_cardLE_initial hlam hω (cardLE_of_subset hω) (CardLE.refl lam))

end ZFVP
