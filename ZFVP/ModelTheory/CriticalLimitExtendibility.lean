import ZFVP.ModelTheory.CriticalExtendibilityWitness
import ZFVP.SetTheory.CnExtendible

/-! The critical limit satisfies every positive standard instance of unbounded extendibility. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CriticalSequence

variable {k : ℕ} {δ f κ : V} (hδ : Cn (k + 1) δ)
  (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
  (hκ : IsCriticalPoint (hierarchy δ) f κ)

include hδ h hκ

theorem limit_iterate_extendible (hlim : criticalLimit f κ ∈ hierarchy δ)
    {i : V} (hi : i ∈ (ω : V)) (m : ℕ)
    (a : SetDomain (hierarchy (criticalLimit f κ))) (ha : a.val = criticalIterate f κ i) :
    (cnExtendibleFormula (m + 1)).Evalb ![a] := by
  let := limit_ordinal hδ h hκ
  let := hierarchy_transitive (criticalLimit f κ)
  let := rankDomain_nonempty (omega_mem_limit hδ h hκ)
  let := limit_models_zf hδ h hκ
  apply (eval_cnExtendibleFormula (m + 1) a).mpr
  have hcard : IsInitialOrdinal a := TransitiveZF.initial_of_noLowRankCofinalMaps _ a
    (ha ▸ (iterate_spec hδ h hκ hi).1) (ha ▸ (iterate_rankCriterion hδ h hκ hi).2.2.2)
  refine ⟨hcard, ?_⟩
  intro μ hμc haμ
  have hμord := (TransitiveZF.ordinal_iff (hierarchy (criticalLimit f κ)) μ).mp hμc.ordinal
  have hiμ : criticalIterate f κ i ∈ μ.val := ha ▸ haμ
  obtain ⟨ν, e, hνord, hμν, hνc, helim, he, heκ, hmove⟩ :=
    extendibility_witness hδ h hκ hlim hi m μ hμord hiμ ((eval_cnFormula _ μ).mpr hμc)
  let e' : SetDomain (hierarchy (criticalLimit f κ)) := ⟨e, helim⟩
  have hνc' := (eval_cnFormula (m + 1) ν).mp hνc
  let := hμc.ordinal
  let := hνc'.ordinal
  let := hierarchy_transitive μ
  have hA := TransitiveZF.rankHierarchy_val (criticalLimit f κ) μ hμc.ordinal
  have hB := TransitiveZF.rankHierarchy_val (criticalLimit f κ) ν hνc'.ordinal
  have he' : IsCodedMembershipEmbedding (hierarchy μ) (hierarchy ν) e' := by
    apply TransitiveZF.embedding_of_embedding (hierarchy (criticalLimit f κ))
    simpa only [hA, hB] using he
  have hAtrans : IsTransitive (hierarchy μ).val := by
    rw [hA]
    let := hμord
    exact hierarchy_transitive _
  let := hAtrans
  have heκ' : IsCriticalPoint (hierarchy μ) e' a := by
    apply (TransitiveZF.criticalPoint_iff (hierarchy (criticalLimit f κ))
      (hierarchy μ) (hierarchy ν) e' a he'.function).mpr
    simpa only [hA, ha] using heκ
  refine ⟨ν, e', hμν, hνc', he', heκ', ?_⟩
  let := IsFunction.of_mem he'.function
  change μ.val ∈ (e' ‘ a).val
  rw [TransitiveZF.value_val (hierarchy (criticalLimit f κ)) e' a
    (by rw [domain_eq_of_mem_function he'.function]; exact heκ'.mem_domain)]
  simpa only [ha] using hmove

theorem limit_unbounded_extendibility (hlim : criticalLimit f κ ∈ hierarchy δ) (m : ℕ) :
    SetSentenceTrue (unboundedExtendibilitySentence (m + 1)) (hierarchy (criticalLimit f κ)) := by
  let := limit_ordinal hδ h hκ
  let := hierarchy_transitive (criticalLimit f κ)
  let := rankDomain_nonempty (omega_mem_limit hδ h hκ)
  let := limit_models_zf hδ h hκ
  apply (setSentenceTrue_iff_models _ _).mpr
  apply (eval_unboundedExtendibilitySentence (m + 1)).mpr
  intro α hα
  have hαV := (TransitiveZF.ordinal_iff (hierarchy (criticalLimit f κ)) α).mp hα
  obtain ⟨i, hi, hαi⟩ := (mem_criticalLimit_iff f κ α.val).mp (ordinal_mem_limit hδ h hκ α hαV)
  let a : SetDomain (hierarchy (criticalLimit f κ)) :=
    ⟨criticalIterate f κ i, ordinal_subset_hierarchy _ _ (iterate_mem_limit hδ h hκ hi)⟩
  exact ⟨a, hαi, (eval_cnExtendibleFormula (m + 1) a).mp
    (limit_iterate_extendible hδ h hκ hlim hi m a rfl)⟩

end CriticalSequence

end ZFVP
