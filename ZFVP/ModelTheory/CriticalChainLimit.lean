import ZFVP.ModelTheory.DirectedElementaryUnion

/-! The internal critical rank chain is elementary in its union, which models ZF. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem naturalElementaryChain_monotone (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (hstep : ∀ n ∈ (ω : V), IsElementaryInclusion (F n) (F (succ n)))
    {i j : V} (hi : i ∈ (ω : V)) (hj : j ∈ (ω : V)) (hij : i ⊆ j) :
    IsElementaryInclusion (F i) (F j) := by
  have hall : ∀ j ∈ (ω : V), ∀ i ∈ (ω : V), i ⊆ j → IsElementaryInclusion (F i) (F j) := by
    apply naturalNumber_induction
      (fun j ↦ ∀ i ∈ (ω : V), i ⊆ j → IsElementaryInclusion (F i) (F j)) (by definability)
    · intro i hi his
      have he : i = (0 : V) := subset_empty_iff_eq_empty.mp his
      rw [he]
      exact IsElementaryInclusion.refl (hstep 0 (by simp)).source_nonempty
    · intro j hj ih i hi his
      let := IsOrdinal.of_mem hj
      let := IsOrdinal.of_mem hi
      rcases IsOrdinal.subset_iff.mp his with he | hl
      · rw [he]
        exact IsElementaryInclusion.refl (hstep _ (ω_succ_closed hj)).source_nonempty
      · have hij' : i ⊆ j := by
          rcases mem_succ_iff.mp hl with he | hlt
          · exact SetTheory.subset_of_eq he
          · exact IsOrdinal.toIsTransitive.transitive i hlt
        exact (ih i hi hij').trans (hstep j hj)
  exact hall j hj i hi hij

theorem naturalElementaryChain_directed (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (hstep : ∀ n ∈ (ω : V), IsElementaryInclusion (F n) (F (succ n))) :
    ∀ i ∈ (ω : V), ∀ j ∈ (ω : V), ∃ k ∈ (ω : V),
      IsElementaryInclusion (F i) (F k) ∧ IsElementaryInclusion (F j) (F k) := by
  intro i hi j hj
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  rcases IsOrdinal.subset_or_supset i j with hij | hji
  · exact ⟨j, hj, naturalElementaryChain_monotone F hF hstep hi hj hij,
      IsElementaryInclusion.refl (hstep j hj).source_nonempty⟩
  · exact ⟨i, hi, IsElementaryInclusion.refl (hstep i hi).source_nonempty,
      naturalElementaryChain_monotone F hF hstep hj hi hji⟩

theorem IsElementaryInclusion.models_iff {A B : V} [Nonempty (SetDomain A)] [Nonempty (SetDomain B)]
    (h : IsElementaryInclusion A B) (T : SetTheory) :
    (SetDomain A)↓[ℒₛₑₜ] ⊧* T ↔ (SetDomain B)↓[ℒₛₑₜ] ⊧* T := by
  simp only [models_theory_iff]
  apply forall_congr'
  intro φ
  apply forall_congr'
  intro _
  have he := h.eval_semisentence φ ![]
  have hb : h.toFunction ∘ ![] = ![] := by funext i; exact Fin.elim0 i
  rw [hb] at he
  exact he

namespace CriticalSequence

variable {k : ℕ} {δ f κ : V} (hδ : Cn (k + 1) δ)
  (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
  (hκ : IsCriticalPoint (hierarchy δ) f κ)

include hδ h hκ

theorem rank_union_iff (x : V) : x ∈ hierarchy (criticalLimit f κ) ↔
    ∃ n ∈ (ω : V), x ∈ hierarchy (criticalIterate f κ n) := by
  let := limit_ordinal hδ h hκ
  rw [mem_hierarchy_iff_rank_mem, mem_criticalLimit_iff]
  apply exists_congr
  intro n
  apply and_congr_right
  intro hn
  let := (iterate_spec hδ h hκ hn).1
  exact (mem_hierarchy_iff_rank_mem x (criticalIterate f κ n)).symm

theorem limit_elementaryInclusion {n : V} (hn : n ∈ (ω : V)) :
    IsElementaryInclusion (hierarchy (criticalIterate f κ n)) (hierarchy (criticalLimit f κ)) := by
  apply directedUnion_elementary (fun i ↦ hierarchy (criticalIterate f κ i)) (by definability)
    (show IsNonempty (ω : V) from ⟨0, by simp⟩)
    (fun i hi ↦ (successive_elementaryInclusion hδ h hκ hi).source_nonempty)
    (naturalElementaryChain_directed _ (by definability) (fun i hi ↦ successive_elementaryInclusion hδ h hκ hi))
    (rank_union_iff hδ h hκ) n hn

theorem limit_models_zf [Nonempty (SetDomain (hierarchy (criticalLimit f κ)))] :
    (SetDomain (hierarchy (criticalLimit f κ)))↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  let hcrit := rankEmbedding_criticalPoint_rankCriterion hδ hδ h hκ
  let := hcrit.1
  let := rankDomain_nonempty hcrit.2.1
  have hinc : IsElementaryInclusion (hierarchy κ) (hierarchy (criticalLimit f κ)) := by
    simpa using limit_elementaryInclusion hδ h hκ (by simp : (0 : V) ∈ ω)
  exact (hinc.models_iff 𝗭𝗙).mp hcrit.models_zf

end CriticalSequence

end ZFVP
