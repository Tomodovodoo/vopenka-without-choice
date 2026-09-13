import ZFVP.ModelTheory.WoodinRecursionHistoryInduction
import ZFVP.ModelTheory.WoodinRecursionSuccessor

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinIterationRec_extends_to_prefix {θ j : V} (hj : j ∈ θ) :
    ForcingCodeExtends (kpair.π₁ (woodinIterationRec j)) (woodinIterationPrefix θ) := by
  have he := forcingIterationCodeUnion_extends (H := woodinHistoryCodes (woodinIterationHistory θ)) hj
  rw [woodinIterationHistory_code_value hj] at he
  exact he


theorem woodinIterationPrefix_extends {η θ : V} (hηθ : η ⊆ θ) :
    ForcingCodeExtends (woodinIterationPrefix η) (woodinIterationPrefix θ) := by
  have ht (c : V → V) (hc : ℒₛₑₜ-function₁ c) :
      forcingHistoryTable η (woodinHistoryCodes (woodinIterationHistory η)) c hc ⊆
        forcingHistoryTable θ (woodinHistoryCodes (woodinIterationHistory θ)) c hc := by
    let := hc
    unfold forcingHistoryTable iterationTableUnion
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
    obtain ⟨j, hj, rfl⟩ := (repl_spec (by definability)).mp hy
    refine mem_sUnion_iff.mpr
      ⟨c ((woodinHistoryCodes (woodinIterationHistory θ)) ‘ j),
        (repl_spec (by definability)).mpr ⟨j, hηθ j hj, rfl⟩, ?_⟩
    simpa only [woodinIterationHistory_code_value hj, woodinIterationHistory_code_value (hηθ j hj)] using hxy
  unfold woodinIterationPrefix forcingIterationCodeUnion
  constructor <;> simp only [forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code,
    forcingCodeE_code, forcingCodeL_code, forcingCodet_code] <;> apply ht

variable {δ θ : V} [IsOrdinal θ]
  (hs : ∀ j ∈ θ, IsWoodinIteration δ (succ j) (kpair.π₁ (woodinIterationRec j))
    (kpair.π₂ (woodinIterationRec j)))

include hs

theorem woodinIterationPrefix_poset_value {j k : V} (hj : j ∈ θ) (hk : k ∈ succ j) :
    (forcingCodeP (woodinIterationPrefix θ)) ‘ k =
      (forcingCodeP (kpair.π₁ (woodinIterationRec j))) ‘ k :=
  ((hs j hj).code.tableP.value_of_subset (woodinIterationPrefix_of_stages hs).code.tableP
    (woodinIterationRec_extends_to_prefix hj).subP hk).symm

theorem woodinIterationPrefix_projection_value {j k l : V}
    (hj : j ∈ θ) (hk : k ∈ succ j) (hl : l ∈ succ j) :
    (forcingCodeπ (woodinIterationPrefix θ)) ‘ ⟨k, l⟩ₖ =
      (forcingCodeπ (kpair.π₁ (woodinIterationRec j))) ‘ ⟨k, l⟩ₖ :=
  ((hs j hj).code.tableπ.value_of_subset (woodinIterationPrefix_of_stages hs).code.tableπ
    (woodinIterationRec_extends_to_prefix hj).subπ (mem_prod_iff.mpr ⟨k, hk, l, hl, rfl⟩)).symm

theorem woodinIterationPrefix_section_value {j k l : V}
    (hj : j ∈ θ) (hk : k ∈ succ j) (hl : l ∈ succ j) :
    (forcingCodeE (woodinIterationPrefix θ)) ‘ ⟨k, l⟩ₖ =
      (forcingCodeE (kpair.π₁ (woodinIterationRec j))) ‘ ⟨k, l⟩ₖ :=
  ((hs j hj).code.tableE.value_of_subset (woodinIterationPrefix_of_stages hs).code.tableE
    (woodinIterationRec_extends_to_prefix hj).subE (mem_prod_iff.mpr ⟨k, hk, l, hl, rfl⟩)).symm

end ZFVP
