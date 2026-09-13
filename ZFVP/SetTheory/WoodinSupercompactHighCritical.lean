import ZFVP.SetTheory.HighCriticalWoodinWitness
import ZFVP.SetTheory.SigmaOneStarUnbounded
import ZFVP.ModelTheory.SuccessorRankPairPreimages
import ZFVP.ModelTheory.EmbeddingOmegaFixation

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.omega_lt {δ : V} (hδ : IsWoodinSupercompact δ) : (ω : V) ∈ δ := by
  let := hδ.1.1
  obtain ⟨γ, hδγ, hγ⟩ := sigmaOneStarCorrect_unbounded δ
  let := hγ.1.ordinal
  have hzγ : (∅ : V) ∈ hierarchy γ := ordinal_mem_hierarchy_iff.mpr
    (IsOrdinal.toIsTransitive.mem_trans (show (∅ : V) ∈ (ω : V) by simp) hγ.1.omega_lt)
  obtain ⟨_, ρ, _, hρ, _, _, e, he, c, hc, hec, _⟩ := hδ.2 γ hδγ hγ ∅ hzγ
  let := hρ.1.ordinal
  let := hc.ordinal
  let := hierarchy_transitive (succ ρ)
  let := hierarchy_transitive (succ γ)
  have hωρ : (ω : V) ∈ hierarchy (succ ρ) :=
    hierarchy_mono (by intro z hz; exact mem_succ_iff.mpr (Or.inr hz)) _
      (ordinal_mem_hierarchy_iff.mpr hρ.1.omega_lt)
  have hcδ : c ∈ δ := hec ▸ hc.lt_value he
  exact IsOrdinal.toIsTransitive.mem_trans (hc.omega_lt_of_omega_mem he hωρ) hcδ

theorem IsWoodinSupercompact.highCritical {δ : V} (hδ : IsWoodinSupercompact δ) :
    HasHighCriticalWoodinWitnesses δ := by
  let := hδ.1.1
  refine ⟨hδ.1, hδ.omega_lt, ?_⟩
  intro γ hδγ hγ a ha η hη
  let := hγ.1.ordinal
  let := IsOrdinal.of_mem hη
  have hηγ : η ∈ γ := IsOrdinal.toIsTransitive.mem_trans hη hδγ
  have hηV : η ∈ hierarchy γ := ordinal_mem_hierarchy_iff.mpr hηγ
  have hpair := kpair_mem_hierarchy_limit hγ.1.successor_closed ha hηV
  obtain ⟨_, ρ, hρδ, hρ, x, hx, e, he, c, hc, hec, hxe⟩ := hδ.2 γ hδγ hγ ⟨a, η⟩ₖ hpair
  let := hρ.1.ordinal
  let := hc.ordinal
  let := hierarchy_transitive (succ ρ)
  let := hierarchy_transitive (succ γ)
  obtain ⟨u, v, hu, hv, _, hue, hve⟩ := successorRankEmbedding_pair_preimages hρ.1 hγ.1 he hx hxe
  have hvD : v ∈ hierarchy (succ ρ) :=
    hierarchy_mono (by intro z hz; exact mem_succ_iff.mpr (Or.inr hz)) _ hv
  have hvc : v ∈ c := (he.value_mem_iff hvD hc.mem_domain).mp (by rw [hve, hec]; exact hη)
  have hηc : η ∈ c := (hve.symm.trans (hc.fixed_below hvc)).symm ▸ hvc
  exact ⟨hγ.1.ordinal, ρ, hρδ, hρ, u, hu, e, he, c, hc, hec, hue, hηc⟩

theorem woodinSupercompact_iff_highCritical (δ : V) :
    IsWoodinSupercompact δ ↔ HasHighCriticalWoodinWitnesses δ :=
  ⟨IsWoodinSupercompact.highCritical, HasHighCriticalWoodinWitnesses.woodinSupercompact⟩

end ZFVP
