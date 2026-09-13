import ZFVP.ModelTheory.WoodinCollapseLift
import ZFVP.SetTheory.WoodinClosedFiniteModels

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem HighCriticalWoodinWitness.inaccessible_cutoff {δ γ a η : V}
    [IsOrdinal δ] (hδγ : δ ∈ γ) (hγ : Cn 1 γ)
    (hw : HighCriticalWoodinWitness δ γ a η) :
    ∃ ρ, ρ ∈ δ ∧ IsSigmaOneStarCorrect ρ ∧ ∃ x ∈ hierarchy ρ, ∃ e,
      IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e ∧
      ∃ c, IsCriticalPoint (hierarchy (succ ρ)) e c ∧ c ∈ ρ ∧ IsChoicelessInaccessible c ∧
        η ∈ c ∧ c ∈ δ ∧ e ‘ c = δ ∧ e ‘ x = a := by
  obtain ⟨_, ρ, hρδ, hρ, x, hx, e, he, c, hc, hec, hxa, hηc⟩ := hw
  let := hρ.1.ordinal
  let := hγ.ordinal
  let := hc.ordinal
  let := hierarchy_transitive (succ ρ)
  let := hierarchy_transitive (succ γ)
  have hcρ := successorRankEmbedding_criticalPoint_lt_height he hc (hec.symm ▸ hδγ)
  have hωρ : (ω : V) ∈ hierarchy (succ ρ) := hierarchy_mono
    (by intro z hz; exact mem_succ_iff.mpr (Or.inr hz)) _
      (ordinal_mem_hierarchy_iff.mpr hρ.1.omega_lt)
  have hci : IsChoicelessInaccessible c := by
    refine ⟨hc.ordinal, hc.omega_lt_of_omega_mem he hωρ, ?_⟩
    intro α hα g
    exact successorRankEmbedding_criticalPoint_no_rank_cofinalMap hρ.1 hγ he hc hcρ (hierarchy_mem hα)
  exact ⟨ρ, hρδ, hρ, x, hx, e, he, c, hc, hcρ, hci, hηc, hec ▸ hc.lt_value he, hec, hxa⟩

end ZFVP
