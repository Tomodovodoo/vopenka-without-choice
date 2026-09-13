import ZFVP.ModelTheory.WoodinUniformTailSupport
import ZFVP.ModelTheory.WoodinDirectIndex

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinBound_direct_small {δ θ i j α : V} [IsOrdinal θ] [IsOrdinal α]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hj : j ∈ θ) (hi : i ∈ j) (hlim : j ≠ succ (⋃ˢ j))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
    (hα : α ∈ (kpair.π₂ (woodinIterationRec i)) ‘ i) :
    IsChoicelessInaccessible j ∧
      (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i ∈ hierarchy j ∧ α ∈ hierarchy j := by
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hi
  have hh := woodinIterationHistory_of_stages
    (fun k hk ↦ hs k (IsOrdinal.toIsTransitive.mem_trans hk hj))
  have h := woodinIterationPrefix_of_stages
    (fun k hk ↦ hs k (IsOrdinal.toIsTransitive.mem_trans hk hj))
  have he := h.index_eq_regular_limit (ordinal_limit_of_not_successor hlim) hinac.regular
  have hji : IsChoicelessInaccessible j := he.symm ▸ hinac
  have hKi : (woodinIterationCardinalPrefix j) ‘ i = (kpair.π₂ (woodinIterationRec i)) ‘ i := by
    simpa only [woodinIterationCardinalPrefix, woodinIterationHistory_cardinal_value hi] using hh.cardinal_union_value hi (mem_succ_self i)
  have hKj : (woodinIterationCardinalPrefix j) ‘ i ∈ j := by
    exact (congrArg (fun z ↦ (woodinIterationCardinalPrefix j) ‘ i ∈ z) he).mpr
      (h.cardinal_mem_limit (ordinal_limit_of_not_successor hlim) hi)
  have hP := h.small i hi j hji
  simp only [woodinIterationStage, woodinStageCardinal_code, woodinStagePoset_code] at hP
  have hPi := woodinIterationPrefix_poset_value
    (fun k hk ↦ hs k (IsOrdinal.toIsTransitive.mem_trans hk hj)) hi (mem_succ_self i)
  refine ⟨hji, hPi ▸ hP hKj, ordinal_mem_hierarchy_iff.mpr ?_⟩
  exact IsOrdinal.toIsTransitive.mem_trans (hKi.symm ▸ hα) hKj

end ZFVP
