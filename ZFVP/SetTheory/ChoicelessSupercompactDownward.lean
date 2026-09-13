import ZFVP.SetTheory.ChoicelessSupercompactInterpolation

/-! Restricting supercompactness witnesses to lower correct target ranks.
Including the cutoff ordinal among the parameters preserves nontriviality. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem choicelessSupercompactWitness_downward {n : ℕ} {α γ μ η a : V}
    (hμ : Cn (n + 2) μ) (hη : Cn (n + 2) η) (hγμ : γ ∈ μ)
    (h : ChoicelessSupercompactWitness (n + 2) α γ η ⟨a, ⟨μ, γ⟩ₖ⟩ₖ)
    (ha : a ∈ hierarchy μ) : ChoicelessSupercompactWitness (n + 2) α γ μ a := by
  let := hμ.ordinal
  let := hη.ordinal
  let : IsOrdinal γ := IsOrdinal.of_mem hγμ
  let := hierarchy_transitive μ
  let := hierarchy_transitive η
  obtain ⟨_, ρ, p, f, κ, hργ, hρ, hp, hf, hc, hακ, hfp⟩ := h
  let := hρ.ordinal
  let := hc.ordinal
  let : IsOrdinal α := IsOrdinal.of_mem hακ
  let := hierarchy_transitive ρ
  let := IsFunction.of_mem hf.function
  obtain ⟨x, q, hx, hq, _, hfx, hfq⟩ := rankEmbedding_pair_preimages hρ hη hf hp hfp
  obtain ⟨τ, ζ, hτ, hζ, _, hfτ, hfζ⟩ := rankEmbedding_pair_preimages hρ hη hf hq hfq
  have hCτ : Cn (n + 2) τ := by
    have ht := rankEmbedding_cn_same_iff hρ hη hf hτ
    rw [hfτ] at ht
    exact ht.mpr hμ
  let := hCτ.ordinal
  let := hierarchy_transitive τ
  have hζo : IsOrdinal ζ := by
    apply (hf.bounded_defined_iff isOrdinalFormula_bounded (fun v ↦ IsOrdinal (v 0))
      ![ζ] (by simpa using hζ)).mpr
    change IsOrdinal (f ‘ ζ)
    rw [hfζ]
    infer_instance
  let := hζo
  have hVτ := hρ.hierarchy_closed hCτ.ordinal hτ
  have hfVτ : f ‘ (hierarchy τ) = hierarchy μ := by
    rw [(rankEmbedding_value_hierarchy hρ hη hf hCτ.ordinal hτ).2, hfτ]
  have hxτ : x ∈ hierarchy τ := (hf.value_mem_iff hx hVτ).mp (by rwa [hfx, hfVτ])
  have hζτ : ζ ∈ hierarchy τ := (hf.value_mem_iff hζ hVτ).mp (by
    rw [hfζ, hfVτ]
    exact ordinal_subset_hierarchy μ γ hγμ)
  have hr := rankEmbedding_restrict hρ hη hf hVτ
    ⟨ω, ordinal_subset_hierarchy τ _ hCτ.omega_lt⟩
  rw [hfVτ] at hr
  have hv : ∀ z ∈ hierarchy τ, (f ↾ (hierarchy τ)) ‘ z = f ‘ z := by
    intro z hz
    exact value_restrict (by
      rw [domain_eq_of_mem_function hf.function]
      exact (hierarchy_transitive ρ).mem_trans hz hVτ) hz
  have hmove : (f ↾ (hierarchy τ)) ‘ ζ ≠ ζ := by
    rw [hv ζ hζτ, hfζ]
    have hζγ := IsOrdinal.toIsTransitive.mem_trans (ordinal_mem_hierarchy_iff.mp hζ) hργ
    intro he
    rw [he] at hζγ
    exact mem_irrefl ζ hζγ
  obtain ⟨ξ, hξ, hαξ⟩ := criticalPoint_exists_above (α := α)
    ⟨ζ, hζo, hζτ, hmove⟩ (by
      intro z _ hz hle
      rw [hv z hz]
      exact hc.fixed_below (ordinal_mem_of_subset_mem hle hακ))
  refine ⟨hμ.ordinal, τ, x, f ↾ (hierarchy τ), ξ,
    IsOrdinal.toIsTransitive.mem_trans (ordinal_mem_hierarchy_iff.mp hτ) hργ,
    hCτ, hxτ, hr, hξ, hαξ, ?_⟩
  rw [hv x hxτ, hfx]

theorem choicelessSupercompactAt_downward {n : ℕ} {α γ μ η : V}
    (hμ : Cn (n + 2) μ) (hη : Cn (n + 2) η) (hγμ : γ ∈ μ) (hμη : μ ∈ η)
    (h : ∀ a ∈ hierarchy η, ChoicelessSupercompactWitness (n + 2) α γ η a) :
    ∀ a ∈ hierarchy μ, ChoicelessSupercompactWitness (n + 2) α γ μ a := by
  let := hμ.ordinal
  let := hη.ordinal
  let := hierarchy_transitive η
  intro a ha
  have haη := (hierarchy_transitive η).mem_trans ha (hierarchy_mem hμη)
  have hμV := ordinal_subset_hierarchy η μ hμη
  have hγV := (hierarchy_transitive η).mem_trans hγμ hμV
  have hp := kpair_mem_hierarchy_limit hη.successor_closed haη
    (kpair_mem_hierarchy_limit hη.successor_closed hμV hγV)
  exact choicelessSupercompactWitness_downward hμ hη hγμ (h _ hp) ha

end ZFVP
