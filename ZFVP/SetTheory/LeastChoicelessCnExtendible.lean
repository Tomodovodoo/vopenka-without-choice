import ZFVP.ModelTheory.LastPointRankBerkeley
import ZFVP.SetTheory.CnExtendibleDownward

/-! Without higher rank-Berkeley cardinals, the least relative extendible
ordinal has itself as critical point and is C(n)-extendible. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem leastChoiceless_critical_eq_of_no_rankBerkeley {n : ℕ} {α γ θ η f κ : V}
    (hγ : IsLeastOrdinal (IsAlphaChoicelessExtendible (n + 1) α) γ) (hωα : (ω : V) ⊆ α)
    (hno : ∀ μ : V, α ∈ μ → ¬IsNonzeroRankBerkeley μ)
    (hθ : Cn (n + 2) θ) (hη : Cn (n + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f)
    (hc : IsCriticalPoint (hierarchy θ) f κ) (hακ : α ∈ κ)
    (hγθ : γ ∈ θ) (heq : lastPoint θ f = γ) : κ = γ := by
  let := hγ.1
  let := hc.ordinal
  have hle := hc.subset_lastPoint hθ hη hf
  rw [heq] at hle
  rcases IsOrdinal.subset_iff.mp hle with he | hl
  · exact he
  · obtain ⟨μ, hαμ, hμ⟩ := leastChoiceless_rankBerkeley_of_critical_below
      hγ hωα hθ hη hf hc hακ hl hγθ heq
    exact False.elim (hno μ hαμ hμ)

theorem leastChoiceless_cnExtendible_of_no_rankBerkeley {n : ℕ} {α γ : V}
    (hγ : IsLeastOrdinal (IsAlphaChoicelessExtendible (n + 2) α) γ) (hωα : (ω : V) ⊆ α)
    (hno : ∀ μ : V, α ∈ μ → ¬IsNonzeroRankBerkeley μ) : IsCnExtendible (n + 2) γ := by
  let := hγ.1
  have hinit : IsInitialOrdinal γ := by
    obtain ⟨θ, η, f, κ, _, hγθ, hθ, _, hη, hf, hc, hακ, _, heq⟩ :=
      leastChoiceless_high_lastPoint_embeddings hγ γ
    have hκeq := leastChoiceless_critical_eq_of_no_rankBerkeley hγ hωα hno hθ hη hf hc hακ hγθ heq
    exact hκeq ▸ rankEmbedding_criticalPoint_initial hθ hη hf hc
  refine ⟨hinit, ?_⟩
  intro μ hμ hγμ
  let := hμ.ordinal
  let := hierarchy_transitive μ
  obtain ⟨θ, η, f, κ, hμθ, hγθ, hθ, _, hη, hf, hc, hακ, hmove, heq⟩ :=
    leastChoiceless_high_lastPoint_embeddings hγ μ
  let := hθ.ordinal
  let := hη.ordinal
  let := hierarchy_transitive θ
  let := hierarchy_transitive η
  have hκeq := leastChoiceless_critical_eq_of_no_rankBerkeley hγ hωα hno hθ hη hf hc hακ hγθ heq
  subst κ
  have hμV := ordinal_subset_hierarchy θ μ hμθ
  have hγV := hc.mem_domain
  have hγA := ordinal_subset_hierarchy μ γ hγμ
  have himageCn := (rankEmbedding_cn_same_iff
    (hθ.of_le (by omega : n + 2 ≤ n + 3)) hη hf hμV).mp hμ
  let := himageCn.ordinal
  let := hf.value_ordinal hγ.1 hγV
  have hμfγ := IsOrdinal.toIsTransitive.mem_trans hμθ hmove
  have hfγfμ := (hf.value_mem_iff hγV hμV).mpr hγμ
  have hμfμ := IsOrdinal.toIsTransitive.mem_trans hμfγ hfγfμ
  have hr := rankEmbedding_restrict hθ hη hf (hierarchy_mem hμθ)
    ⟨γ, hγA⟩
  rw [(rankEmbedding_value_hierarchy hθ hη hf hμ.ordinal hμV).2] at hr
  have hcr := hc.restrict hf.function ((hierarchy_transitive θ).transitive _ (hierarchy_mem hμθ)) hγA
  refine ⟨f ‘ μ, f ↾ (hierarchy μ), hμfμ, himageCn, hr, hcr, ?_⟩
  let := IsFunction.of_mem hf.function
  rw [value_restrict (by rw [domain_eq_of_mem_function hf.function]; exact hγV) hγA]
  exact hμfγ

end ZFVP
