import ZFVP.SetTheory.ChoicelessSupercompact
import ZFVP.SetTheory.ChoicelessExtendibleWitness
import ZFVP.ModelTheory.RankEmbeddingPairPreimages
import ZFVP.ModelTheory.EmbeddingCnTransfer
import ZFVP.ModelTheory.CriticalPointRestriction

/-! Mohammd Lemma 2.7: positive-level choiceless supercompactness
gives choiceless extendibility one level lower. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsAlphaChoicelessSupercompact.extendible {k : ℕ} {α γ : V}
    (hs : IsAlphaChoicelessSupercompact (k + 2) α γ) : IsAlphaChoicelessExtendible (k + 1) α γ := by
  let := hs.1
  refine ⟨hs.1, hs.2.1, ?_⟩
  intro μ hμ hγμ
  let := hμ.ordinal
  obtain ⟨θ, hμθ, hθ⟩ := cn_unbounded (k + 2) μ
  let := hθ.ordinal
  let := hierarchy_transitive θ
  have hγθ : γ ∈ θ := IsOrdinal.toIsTransitive.mem_trans hγμ hμθ
  have hq : ⟨γ, μ⟩ₖ ∈ hierarchy θ := kpair_mem_hierarchy_limit hθ.successor_closed
    (ordinal_subset_hierarchy θ γ hγθ) (ordinal_subset_hierarchy θ μ hμθ)
  obtain ⟨_, ν, a, e, κ, hνγ, hν, ha, he, hc, hακ, hpair⟩ := hs.2.2 θ hθ hγθ _ hq
  let := hν.ordinal
  let := hierarchy_transitive ν
  let := hc.ordinal
  let := IsFunction.of_mem he.function
  obtain ⟨u, v, hu, hv, _, heu, hev⟩ := rankEmbedding_pair_preimages hν hθ he ha hpair
  have hCv : Cn (k + 1) v := by
    have hiff := rankEmbedding_cn_iff hν hθ he hv
    rw [hev] at hiff
    exact hiff.mpr hμ
  let := hCv.ordinal
  let := hierarchy_transitive v
  have huv : u ∈ v := (he.value_mem_iff hu hv).mp (by rwa [heu, hev])
  let : IsOrdinal u := IsOrdinal.of_mem huv
  have hvν : v ∈ ν := ordinal_mem_hierarchy_iff.mp hv
  have huν : u ∈ ν := ordinal_mem_hierarchy_iff.mp hu
  have humove : e ‘ u ≠ u := by
    rw [heu]
    intro hh
    have hug : u ∈ γ := IsOrdinal.toIsTransitive.mem_trans huν hνγ
    rw [hh] at hug
    exact mem_irrefl u hug
  have hκu : κ ⊆ u := hc.2.2 u inferInstance ⟨hu, humove⟩
  have hκv : κ ∈ v := ordinal_mem_of_subset_mem hκu huv
  have hr := rankEmbedding_restrict hν hθ he (hierarchy_mem hvν)
    ⟨ω, ordinal_subset_hierarchy v _ hCv.omega_lt⟩
  rw [(rankEmbedding_value_hierarchy hν hθ he hCv.ordinal hv).2, hev] at hr
  have hcr := hc.restrict he.function
    ((hierarchy_transitive ν).transitive _ (hierarchy_mem hvν)) (ordinal_subset_hierarchy v κ hκv)
  have hlocal : ChoicelessExtendibleWitness (k + 1) α u v := by
    refine ⟨hCv.ordinal, ordinal_subset_hierarchy v u huv,
      μ, e ↾ (hierarchy v), κ, hμ, hr, hcr, hακ, ?_⟩
    rw [value_restrict (by rw [domain_eq_of_mem_function he.function]; exact hu)
      (ordinal_subset_hierarchy v u huv), heu]
    exact IsOrdinal.toIsTransitive.mem_trans hvν hνγ
  have hαV : α ∈ hierarchy ν := (hierarchy_transitive ν).mem_trans hακ hc.mem_domain
  have hfix : e ‘ α = α := hc.fixed_below hακ
  have htransfer := rankEmbedding_defined_iff hν hθ he
    (positiveChoicelessExtendibleWitnessFormula_sigma k)
    (fun v ↦ ChoicelessExtendibleWitness (k + 1) (v 0) (v 1) (v 2)) ![α, u, v]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hαV, hu, hv])
  have htarget : ChoicelessExtendibleWitness (k + 1) α γ μ := by
    have ht : ChoicelessExtendibleWitness (k + 1) (e ‘ α) (e ‘ u) (e ‘ v) := htransfer.mp hlocal
    rwa [hfix, heu, hev] at ht
  exact htarget.2.2

end ZFVP
