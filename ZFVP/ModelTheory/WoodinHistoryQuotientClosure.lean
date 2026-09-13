import ZFVP.ModelTheory.WoodinRecursionHistoryInduction
import ZFVP.ModelTheory.IterationQuotientClosure
import ZFVP.ModelTheory.WoodinIterationContract

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IterationQuotientClosedBelow.of_code_extension {θ η s z i j κ : V}
    (hs : IsForcingIterationCode θ s) (hz : IsForcingIterationCode η z)
    (he : ForcingCodeExtends s z) (hi : i ∈ θ) (hj : j ∈ θ)
    (hc : IterationQuotientClosedBelow s i j κ) :
    IterationQuotientClosedBelow z i j κ := by
  unfold IterationQuotientClosedBelow at hc ⊢
  rw [← hs.tableP.value_of_subset hz.tableP he.subP hi,
    ← hs.tableR.value_of_subset hz.tableR he.subR hi,
    ← hs.tablet.value_of_subset hz.tablet he.subt hi,
    ← hs.tableP.value_of_subset hz.tableP he.subP hj,
    ← hs.tableR.value_of_subset hz.tableR he.subR hj,
    ← hs.tableπ.value_of_subset hz.tableπ he.subπ (mem_prod_iff.mpr ⟨i, hi, j, hj, rfl⟩)]
  exact hc

theorem IsWoodinIterationHistory.union_quotient_closure {δ θ H J : V} [IsOrdinal θ]
    (h : IsWoodinIterationHistory δ θ H J)
    (hc : ∀ j ∈ θ, HasWoodinQuotientClosure (succ j) (H ‘ j) (J ‘ j)) :
    HasWoodinQuotientClosure θ (forcingIterationCodeUnion θ H) (woodinHistoryCardinalUnion θ J) := by
  intro i hi j hj hij
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hi
  have hij' : i ∈ succ j := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hij)
  rw [h.cardinal_union_value hj hij']
  exact (hc j hj i hij' j (mem_succ_self j) hij).of_code_extension
    (h.stage j hj).code h.codes.union_code (forcingIterationCodeUnion_extends hj) hij' (mem_succ_self j)

theorem woodinIterationPrefix_quotient_closure {δ θ : V} [IsOrdinal θ]
    (hs : ∀ i ∈ θ, IsWoodinIteration δ (succ i) (kpair.π₁ (woodinIterationRec i))
      (kpair.π₂ (woodinIterationRec i)))
    (hc : ∀ i ∈ θ, HasWoodinQuotientClosure (succ i) (kpair.π₁ (woodinIterationRec i))
      (kpair.π₂ (woodinIterationRec i))) :
    HasWoodinQuotientClosure θ (woodinIterationPrefix θ) (woodinIterationCardinalPrefix θ) := by
  apply (woodinIterationHistory_of_stages hs).union_quotient_closure
  intro j hj
  simpa only [woodinIterationHistory_code_value hj, woodinIterationHistory_cardinal_value hj] using hc j hj

/-- The endpoint clauses of the frozen contract follow from the stage induction. -/
theorem woodinIterationExit_of_stages {δ : V} [IsOrdinal δ] (hAC : ¬InternalChoice V)
    (hs : ∀ θ ∈ δ, IsWoodinIteration δ (succ θ) (kpair.π₁ (woodinIterationRec θ))
      (kpair.π₂ (woodinIterationRec θ)))
    (hc : ∀ θ ∈ δ, HasWoodinQuotientClosure (succ θ) (kpair.π₁ (woodinIterationRec θ))
      (kpair.π₂ (woodinIterationRec θ))) : WoodinIterationExit δ :=
  ⟨woodinSeedCardinal_spec hAC, fun θ hθ ↦ ⟨hs θ hθ, hc θ hθ⟩,
    woodinIterationPrefix_of_stages hs, woodinIterationPrefix_quotient_closure hs hc⟩

end ZFVP
