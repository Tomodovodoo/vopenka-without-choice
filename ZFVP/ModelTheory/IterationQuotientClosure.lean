import ZFVP.ModelTheory.SaturatedQuotientClosureTransfer
import ZFVP.ModelTheory.IdentityQuotientClosureForcing
import ZFVP.ModelTheory.IterationSystemProjection
import ZFVP.ModelTheory.ForcingSuccessorCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IterationQuotientClosedBelow (s i j η : V) : Prop :=
  ForcesProjectionQuotientClosedBelow ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
    ((forcingCodet s) ‘ i) ((forcingCodeP s) ‘ j) ((forcingCodeR s) ‘ j)
    ((forcingCodeπ s) ‘ ⟨i, j⟩ₖ) η

def HasWoodinQuotientClosure (θ s K : V) : Prop :=
  ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → IterationQuotientClosedBelow s i j (K ‘ i)

theorem IsForcingIterationCode.diagonal_quotient_closedBelow {θ s i : V}
    (h : IsForcingIterationCode θ s) (hi : i ∈ θ) (η : V) :
    IterationQuotientClosedBelow s i i η :=
  identityQuotient_closedBelow_forced (h.system.order.preorder i hi) (h.system.tops.top i hi)
    (h.system.functions.projection i hi i hi (subset_refl i))
    (fun _ hp ↦ h.system.split.projId hi hp)

theorem IsForcingIterationCode.initial_quotient_closure {s : V}
    (h : IsForcingIterationCode (succ ∅) s) (K : V) : HasWoodinQuotientClosure (succ ∅) s K := by
  intro i hi j hj _
  have hi0 : i = ∅ := by simpa only [mem_succ_iff, not_mem_empty, or_false] using hi
  have hj0 : j = ∅ := by simpa only [mem_succ_iff, not_mem_empty, or_false] using hj
  subst i j
  exact h.diagonal_quotient_closedBelow (mem_succ_self ∅) _

theorem forcingSuccessorCode_quotient_old {k s Q S t i j η : V}
    (hi : i ∈ succ k) (hj : j ∈ succ k) :
    IterationQuotientClosedBelow (forcingSuccessorCode k s Q S t) i j η ↔
      IterationQuotientClosedBelow s i j η := by
  simp only [IterationQuotientClosedBelow, forcingSuccessorCode, forcingIterationCodeNext,
    forcingCodeP_code, forcingCodeR_code, forcingCodet_code, forcingCodeπ_code,
    forcingFamilyNext_old hi, forcingFamilyNext_old hj,
    forcingMatrixNext_old (mem_succ_iff.mpr (Or.inr hi)) hj]

theorem saturatedSuccessorCode_quotient_closedBelow {k s κ δ η i : V} [IsOrdinal k] [IsOrdinal η]
    (hs : IsForcingIterationCode (succ k) s) (hi : i ∈ succ k)
    (hδ : IsChoicelessInaccessible δ) (hP : (forcingCodeP s) ‘ k ∈ hierarchy δ) (hκδ : κ ⊆ δ)
    (hκ : ∀ p ∈ (forcingCodeP s) ‘ k, p ∈ forcingFormula ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k)
      regularCardinalFormula (standardTuple ![checkName ((forcingCodet s) ‘ k) κ]))
    (hηκ : η ⊆ κ)
    (hDC : ∀ p ∈ (forcingCodeP s) ‘ i, p ∈ forcingFormula ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
      dependentChoiceBelowFormula (standardTuple ![checkName ((forcingCodet s) ‘ i) η]))
    (hbase : IterationQuotientClosedBelow s i k η) :
    IterationQuotientClosedBelow
      (forcingSuccessorCode k s
        (saturatedWoodinPrefixPosetName ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) ((forcingCodet s) ‘ k) κ δ)
        (saturatedWoodinPrefixOrderName ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) ((forcingCodet s) ‘ k) κ δ) ∅)
      i (succ k) η := by
  let Q := saturatedWoodinPrefixPosetName ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) ((forcingCodet s) ‘ k) κ δ
  let S := saturatedWoodinPrefixOrderName ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) ((forcingCodet s) ‘ k) κ δ
  let z := forcingSuccessorCode k s Q S ∅
  have hk : k ∈ succ k := mem_succ_self k
  have hi' : i ∈ succ (succ k) := mem_succ_iff.mpr (Or.inr hi)
  let := IsOrdinal.of_mem hi
  have hik : i ⊆ k := IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hi)
  have hiter := saturatedWoodinPrefix_iterand (hs.system.order.preorder k hk)
    (hs.system.tops.top k hk) hδ hP hκδ hκ
  have hz : IsForcingIterationCode (succ (succ k)) z := forcingSuccessorCode_valid hs hiter
  have hPi : (forcingCodeP z) ‘ i = (forcingCodeP s) ‘ i := by
    simp only [z, forcingSuccessorCode, forcingIterationCodeNext, forcingCodeP_code, forcingFamilyNext_old hi]
  have hRi : (forcingCodeR z) ‘ i = (forcingCodeR s) ‘ i := by
    simp only [z, forcingSuccessorCode, forcingIterationCodeNext, forcingCodeR_code, forcingFamilyNext_old hi]
  have hti : (forcingCodet z) ‘ i = (forcingCodet s) ‘ i := by
    simp only [z, forcingSuccessorCode, forcingIterationCodeNext, forcingCodet_code, forcingFamilyNext_old hi]
  change IterationQuotientClosedBelow z i (succ k) η
  unfold IterationQuotientClosedBelow
  rw [hPi, hRi, hti]
  have hproj := hz.system.projection hi' (mem_succ_self (succ k))
    (IsOrdinal.toIsTransitive.transitive _ hi)
  rw [hPi, hRi] at hproj
  apply saturatedWoodin_quotient_closure_forced (hs.system.order.preorder i hi) (hs.system.tops.top i hi)
    (hs.system.splitProjection hi hk hik) (hs.system.order.preorder k hk) (hs.system.tops.top k hk)
    hδ hP hκδ hκ (forcingSuccessorCode_poset k s Q S ∅) (forcingSuccessorCode_order k s Q S ∅)
    hproj ?_ hηκ hDC hbase
  intro q hq
  have hq' : q ∈ twoStepConditions ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) Q ∅ := by
    simpa only [z, forcingSuccessorCode_poset] using hq
  simp only [z, forcingSuccessorCode, forcingIterationCodeNext, forcingCodeπ_code,
    forcingMatrixNext_column hi, successorProjectionColumn_value hi hq']

end ZFVP
