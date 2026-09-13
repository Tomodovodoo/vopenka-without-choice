import ZFVP.SetTheory.HighCriticalWoodinWitness
import ZFVP.ModelTheory.RankEmbeddingDictionary
import ZFVP.ModelTheory.CriticalPointRestriction
import ZFVP.SetTheory.CnCofinalUnbounded
import ZFVP.SetTheory.ChoicelessCorrectness

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

private theorem positiveSyntacticComplexity {m : ℕ} (φ : SetTheorySemisentence m) :
    IsLevyFormula .sigma (levySyntacticBound φ + 1) φ :=
  (isLevyFormula_syntacticBound φ .sigma).raise

opaque highCriticalWoodinComplexity :
    {n : ℕ // IsLevyFormula .sigma (n + 1) highCriticalWoodinWitnessFormula} :=
  ⟨levySyntacticBound highCriticalWoodinWitnessFormula,
    positiveSyntacticComplexity highCriticalWoodinWitnessFormula⟩

def highCriticalWoodinBound : ℕ := highCriticalWoodinComplexity.val + 1

theorem highCriticalWoodinWitness_complexity :
    IsLevyFormula .sigma highCriticalWoodinBound highCriticalWoodinWitnessFormula :=
  highCriticalWoodinComplexity.property

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCnExtendible.highCriticalWoodin_of_complexity {n : ℕ} {κ : V}
    (hφ : IsLevyFormula .sigma (n + 1) highCriticalWoodinWitnessFormula)
    (hκ : IsCnExtendible (n + 1) κ) : HasHighCriticalWoodinWitnesses κ := by
  let := hκ.1.1
  refine ⟨hκ.1, hκ.cn.omega_lt, ?_⟩
  intro γ hκγ hγ a ha η hη
  let := hγ.1.ordinal
  obtain ⟨μ, hγμ, hμ⟩ := cn_unbounded (n + 1) γ
  let := hμ.ordinal
  have hκμ := IsOrdinal.toIsTransitive.mem_trans hκγ hγμ
  obtain ⟨ν, f, _, hν, hf, hc, hmove⟩ := hκ.2 μ hμ hκμ
  let := hν.ordinal
  let := hierarchy_transitive μ
  let := hierarchy_transitive ν
  let := hierarchy_transitive (succ γ)
  let := IsFunction.of_mem hf.function
  have hγV := ordinal_subset_hierarchy μ γ hγμ
  have hκV := hc.mem_domain
  have hηV : η ∈ hierarchy μ := (hierarchy_transitive μ).mem_trans hη hκV
  have haV : a ∈ hierarchy μ := (hierarchy_transitive μ).mem_trans ha (hierarchy_mem hγμ)
  have hsγμ : succ γ ∈ μ := hμ.successor_closed γ hγμ
  have hsγV := ordinal_subset_hierarchy μ (succ γ) hsγμ
  have hAV := hierarchy_mem hsγμ
  have hκA : κ ∈ hierarchy (succ γ) := ordinal_subset_hierarchy (succ γ) κ
    (mem_succ_iff.mpr (Or.inr hκγ))
  have haA : a ∈ hierarchy (succ γ) := hierarchy_mono
    (by intro z hz; exact mem_succ_iff.mpr (Or.inr hz)) _ ha
  have hr := rankEmbedding_restrict hμ hν hf hAV ⟨κ, hκA⟩
  rw [(rankEmbedding_value_hierarchy hμ hν hf (inferInstance : IsOrdinal (succ γ)) hsγV).2,
    hf.value_succ hγV hsγV] at hr
  have hcr := hc.restrict hf.function ((hierarchy_transitive μ).transitive _ hAV) hκA
  have hw : HighCriticalWoodinWitness (f ‘ κ) (f ‘ γ) (f ‘ a) (f ‘ η) := by
    refine ⟨hf.value_ordinal hγ.1.ordinal hγV, γ, ?_, hγ, a, ha,
      f ↾ (hierarchy (succ γ)), hr, κ, hcr, ?_, ?_, ?_⟩
    · let := hf.value_ordinal hκ.1.1 hκV
      exact IsOrdinal.toIsTransitive.mem_trans hγμ hmove
    · exact value_restrict (by rw [domain_eq_of_mem_function hf.function]; exact hκV) hκA
    · exact value_restrict (by rw [domain_eq_of_mem_function hf.function]; exact haV) haA
    · rwa [hc.fixed_below hη]
  exact (rankEmbedding_defined_iff hμ hν hf hφ
    (fun v ↦ HighCriticalWoodinWitness (v 0) (v 1) (v 2) (v 3)) ![κ, γ, a, η]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hκV, hγV, haV, hηV])).mpr hw

theorem IsCnExtendible.highCriticalWoodin {κ : V}
    (hκ : IsCnExtendible highCriticalWoodinBound κ) : HasHighCriticalWoodinWitnesses κ :=
  IsCnExtendible.highCriticalWoodin_of_complexity
    (n := highCriticalWoodinComplexity.val) highCriticalWoodinWitness_complexity hκ

end ZFVP
