import ZFVP.ModelTheory.CriticalLimitCardinal
import ZFVP.ModelTheory.ShiftedFixedRankEmbedding
import ZFVP.ModelTheory.RankBerkeleyLeastFailure

/-! A critical limit below a C(2) self-embedding rank is nonzero rank-Berkeley. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem CriticalSequence.limit_nonzeroRankBerkeley {n : ℕ} {θ f κ : V}
    (hθ : Cn (n + 2) θ) (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy θ) f)
    (hc : IsCriticalPoint (hierarchy θ) f κ) (hlim : criticalLimit f κ ∈ hierarchy θ) :
    IsNonzeroRankBerkeley (criticalLimit f κ) := by
  let := hθ.ordinal
  let := hc.ordinal
  let := CriticalSequence.limit_ordinal hθ hf hc
  have hκlim : κ ∈ criticalLimit f κ := by
    simpa using CriticalSequence.iterate_mem_limit hθ hf hc (by simp : (0 : V) ∈ ω)
  have hfix := CriticalSequence.limit_fixed hθ hf hc hlim
  refine ⟨⟨κ, hκlim⟩, (rankBerkeleyClause_iff_no_failure _).mpr
    ⟨CriticalSequence.limit_initial hθ hf hc, ?_⟩⟩
  intro σ hbad
  obtain ⟨τ, hτθ, hmin⟩ := hθ.leastRankBerkeleyFailure_exists hlim ⟨σ, hbad⟩
  let := hmin.1
  have hlimτ := hmin.2.1.2.1
  have hfixτ := rankEmbedding_leastRankBerkeleyFailure_fixed hθ hf hmin hτθ hfix
  apply hmin.2.1.2.2
  intro ζ hζ
  obtain ⟨i, hi, hζi⟩ := (mem_criticalLimit_iff f κ ζ).mp hζ
  obtain ⟨g, hg, hcg, hglim⟩ := rankEmbedding_shifted_fixed_rank hθ hf hc hτθ
    (IsOrdinal.toIsTransitive.mem_trans hκlim hlimτ) hlimτ hfixτ hfix hi
  exact ⟨g, criticalIterate f κ i, hg, hcg, hζi,
    CriticalSequence.iterate_mem_limit hθ hf hc hi, hglim⟩

end ZFVP
