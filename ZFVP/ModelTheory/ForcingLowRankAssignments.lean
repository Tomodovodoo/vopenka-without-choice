import ZFVP.ModelTheory.ForcingFiniteAssignments
import ZFVP.ModelTheory.ForcingLowRankNames
import ZFVP.ModelTheory.SuccessorRankNameDomain

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem mem_range_evaluationGraph_iff (S : ForcingContext V) (C : V)
    (hC : ∀ σ ∈ C, IsForcingName S.P σ) (y : S.Model) :
    y ∈ range (S.evaluationGraph C hC) ↔ ∃ σ, ∃ hσ : σ ∈ C, y = S.ofName ⟨σ, hC σ hσ⟩ := by
  rw [mem_range_iff]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨σ, hσ, _, hy⟩ := (S.pair_mem_evaluationGraph_iff C hC x y).mp hx
    exact ⟨σ, hσ, hy⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨S.check σ, (S.pair_mem_evaluationGraph_iff C hC _ _).mpr ⟨σ, hσ, rfl, rfl⟩⟩

theorem lowRankNameSet_names (S : ForcingContext V) (δ : V) :
    ∀ σ ∈ lowRankNameSet S.P δ, IsForcingName S.P σ := fun σ hσ ↦ (mem_lowRankNameSet S.P δ σ).mp hσ |>.2

theorem lowRankEvaluation_range (S : ForcingContext V) {δ : V}
    (hδ : Cn 1 δ) (hP : S.P ∈ hierarchy δ) :
    range (S.evaluationGraph (lowRankNameSet S.P δ) (S.lowRankNameSet_names δ)) = hierarchy (S.check δ) := by
  apply mem_ext
  intro y
  rw [S.mem_range_evaluationGraph_iff, S.mem_checked_hierarchy_iff_low_name hδ hP]
  constructor
  · rintro ⟨σ, hσ, hy⟩
    exact ⟨⟨σ, S.lowRankNameSet_names δ σ hσ⟩, (mem_lowRankNameSet S.P δ σ).mp hσ |>.1, hy⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ.val, (mem_lowRankNameSet S.P δ σ.val).mpr ⟨hσ, σ.property⟩, rfl⟩

theorem lowRankFiniteAssignment_representative (S : ForcingContext V) {δ n : V}
    (hδ : Cn 1 δ) (hP : S.P ∈ hierarchy δ) (hn : n ∈ (ω : V))
    {b : S.Model} (hb : b ∈ hierarchy (S.check δ) ^ S.check n) :
    ∃ s : V, ∃ hsN : IsNameSequence S.P s,
      s ∈ lowRankNameSet S.P δ ^ n ∧ S.sequenceValue s hsN = b := by
  rw [← S.lowRankEvaluation_range hδ hP] at hb
  exact S.finite_sequenceValue_surjective _ (S.lowRankNameSet_names δ) hn hb

end ForcingContext
end ZFVP
