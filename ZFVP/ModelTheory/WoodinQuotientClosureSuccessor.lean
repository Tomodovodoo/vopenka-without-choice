import ZFVP.ModelTheory.IterationQuotientClosure
import ZFVP.ModelTheory.WoodinIterationInvariant

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem HasWoodinQuotientClosure.successor {δ k s K : V} [IsOrdinal k]
    (hδ : IsWoodinSupercompact δ) (h : IsWoodinIteration δ (succ k) s K)
    (hc : HasWoodinQuotientClosure (succ k) s K) :
    HasWoodinQuotientClosure (succ (succ k)) (woodinIterationSuccessor k s K)
      (woodinIterationCardinalNext k s K) := by
  let z := woodinIterationSuccessor k s K
  let L := woodinIterationCardinalNext k s K
  let c := woodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) ((forcingCodet s) ‘ k) (K ‘ k)
  have hn : IsWoodinIteration δ (succ (succ k)) z L := h.successor hδ
  have hk : k ∈ succ k := mem_succ_self k
  have hk' : k ∈ succ (succ k) := mem_succ_iff.mpr (Or.inr hk)
  have hnew : L ‘ (succ k) = c := by
    simp only [L, c, woodinIterationCardinalNext, forcingFamilyNext_new,
      woodinSuccessorStep, woodinSuccessorAt, woodinIterationStage, woodinStagePoset_code,
      woodinStageOrder_code, woodinStageTop_code, woodinStageCardinal_code]
  have hold (i : V) (hi : i ∈ succ k) : L ‘ i = K ‘ i := forcingFamilyNext_old hi
  have hci : IsChoicelessInaccessible c := hnew ▸ hn.inaccessible (succ k) (mem_succ_self (succ k))
  let := hci.1
  have hκc : K ‘ k ∈ c := by
    simpa only [hold k hk, hnew] using hn.increasing k hk' (succ k) (mem_succ_self (succ k)) hk
  have hP : (forcingCodeP s) ‘ k ∈ hierarchy c := by
    have hs := h.small k hk c hci
    simp only [woodinIterationStage, woodinStageCardinal_code, woodinStagePoset_code] at hs
    exact hs hκc
  have hκ : ∀ p ∈ (forcingCodeP s) ‘ k, p ∈ forcingFormula ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k)
      regularCardinalFormula (standardTuple ![checkName ((forcingCodet s) ‘ k) (K ‘ k)]) := by
    simpa only [woodinIterationStage, woodinStageCardinal_code, woodinStagePoset_code,
      woodinStageOrder_code, woodinStageTop_code] using (h.stage k hk).2.2.2.1
  intro i hi j hj hij
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  rcases mem_succ_iff.mp hj with rfl | hj
  · rcases mem_succ_iff.mp hi with rfl | hi
    · exact hn.code.diagonal_quotient_closedBelow (mem_succ_self (succ k)) _
    · change IterationQuotientClosedBelow z i (succ k) (L ‘ i)
      rw [hold i hi]
      let := (h.inaccessible i hi).1
      let := (h.inaccessible k hk).1
      have hik : i ⊆ k := IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hi)
      have hKi : K ‘ i ⊆ K ‘ k := by
        rcases mem_succ_iff.mp hi with rfl | hik'
        · exact subset_refl _
        · exact IsOrdinal.toIsTransitive.transitive _ (h.increasing i hi k hk hik')
      apply saturatedSuccessorCode_quotient_closedBelow h.code hi hci hP
        (IsOrdinal.toIsTransitive.transitive _ hκc) hκ hKi ?_ (hc i hi k hk hik)
      simpa only [woodinIterationStage, woodinStageCardinal_code, woodinStagePoset_code,
        woodinStageOrder_code, woodinStageTop_code] using (h.stage i hi).2.2.2.2
  · have hiold : i ∈ succ k := ordinal_mem_of_subset_mem hij hj
    change IterationQuotientClosedBelow z i j (L ‘ i)
    rw [hold i hiold]
    exact (forcingSuccessorCode_quotient_old hiold hj).mpr (hc i hiold j hj hij)

end ZFVP
