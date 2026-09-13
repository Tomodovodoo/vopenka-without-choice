import ZFVP.ModelTheory.CriticalSequence
import ZFVP.ModelTheory.RankEmbeddingDictionary
import ZFVP.SetTheory.PiOneInitialOrdinal

/-! Critical-sequence stages and their supremum are initial ordinals. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankEmbedding_initial_iff {k l : ℕ} {θ η f α : V}
    (hθ : Cn (k + 1) θ) (hη : Cn (l + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f)
    (hα : α ∈ hierarchy θ) : IsInitialOrdinal α ↔ IsInitialOrdinal (f ‘ α) := by
  exact rankEmbedding_defined_iff (hθ.of_le (by omega : 1 ≤ k + 1))
    (hη.of_le (by omega : 1 ≤ l + 1)) hf piOneInitialOrdinalFormula_piOne
    (fun v ↦ IsInitialOrdinal (v 0)) ![α] (by simpa using hα)

namespace CriticalSequence

variable {k : ℕ} {δ f κ : V} (hδ : Cn (k + 1) δ)
  (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
  (hκ : IsCriticalPoint (hierarchy δ) f κ)

include hδ h hκ

theorem iterate_initial {n : V} (hn : n ∈ (ω : V)) : IsInitialOrdinal (criticalIterate f κ n) := by
  have hi : ∀ n ∈ (ω : V), IsInitialOrdinal (criticalIterate f κ n) := by
    apply naturalNumber_induction (fun n ↦ IsInitialOrdinal (criticalIterate f κ n)) (by definability)
    · simpa using rankEmbedding_criticalPoint_initial hδ hδ h hκ
    · intro n hn ih
      rw [criticalIterate_succ f κ hn]
      exact (rankEmbedding_initial_iff hδ hδ h (iterate_spec hδ h hκ hn).2.1).mp ih
  exact hi n hn

theorem limit_initial : IsInitialOrdinal (criticalLimit f κ) := by
  let := limit_ordinal hδ h hκ
  refine ⟨inferInstance, ?_⟩
  intro α hα hinj
  obtain ⟨n, hn, hαn⟩ := (mem_criticalLimit_iff f κ α).mp hα
  have hCn := iterate_initial hδ h hκ hn
  have hsub : criticalIterate f κ n ⊆ criticalLimit f κ :=
    IsOrdinal.toIsTransitive.transitive _ (iterate_mem_limit hδ h hκ hn)
  exact hCn.2 α hαn ((cardLE_of_subset hsub).trans hinj)

end CriticalSequence

end ZFVP
