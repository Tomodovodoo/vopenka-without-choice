import ZFVP.SetTheory.ChoicelessSupercompact
import ZFVP.ModelTheory.RankEmbeddingPairPreimages
import ZFVP.ModelTheory.EmbeddingCnTransfer
import ZFVP.ModelTheory.CriticalComposition

/-! Positive-level interpolation of choiceless supercompactness witnesses.
In the restriction case we also pull back the outer critical point, so the
composite is proved nontrivial even if the restriction fixes every ordinal. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def ChoicelessSupercompactBelow (n : ℕ) (α κ δ : V) : Prop :=
  ∀ μ, Cn n μ → κ ∈ μ → μ ∈ δ → ∀ a ∈ hierarchy μ,
    ChoicelessSupercompactWitness n α κ μ a

theorem choicelessSupercompactWitness_interpolate {n : ℕ} {α κ δ μ a : V}
    [IsOrdinal κ] [IsOrdinal δ]
    (hsmall : ChoicelessSupercompactBelow (n + 2) α κ δ)
    (hgap : ∃ η, κ ∈ η ∧ η ∈ δ ∧ Cn (n + 2) η)
    (hbig : ChoicelessSupercompactWitness (n + 2) α δ μ a) :
    ChoicelessSupercompactWitness (n + 2) α κ μ a := by
  obtain ⟨hμ, ν, x, j, χ, hνδ, hν, hx, hj, hχ, hαχ, hjx⟩ := hbig
  let := hμ
  let := hν.ordinal
  let := hχ.ordinal
  let : IsOrdinal α := IsOrdinal.of_mem hαχ
  let := hierarchy_transitive ν
  let := hierarchy_transitive μ
  rcases IsOrdinal.mem_trichotomy ν κ with hνκ | heq | hκν
  · exact ⟨hμ, ν, x, j, χ, hνκ, hν, hx, hj, hχ, hαχ, hjx⟩
  · subst ν
    obtain ⟨η, hκη, hηδ, hη⟩ := hgap
    let := hη.ordinal
    let := hierarchy_transitive η
    have hχη : χ ∈ hierarchy η :=
      hierarchy_mono (IsOrdinal.toIsTransitive.transitive κ hκη) _ hχ.mem_domain
    have hxη : x ∈ hierarchy η :=
      hierarchy_mono (IsOrdinal.toIsTransitive.transitive κ hκη) _ hx
    have hκη' : κ ∈ hierarchy η := ordinal_subset_hierarchy η κ hκη
    have hq : ⟨x, ⟨κ, χ⟩ₖ⟩ₖ ∈ hierarchy η :=
      kpair_mem_hierarchy_limit hη.successor_closed hxη
        (kpair_mem_hierarchy_limit hη.successor_closed hκη' hχη)
    obtain ⟨_, ρ, p, k, ξ, hρκ, hρ, hp, hk, hξ, hαξ, hkp⟩ :=
      hsmall η hη hκη hηδ _ hq
    let := hρ.ordinal
    let := hξ.ordinal
    let := hierarchy_transitive ρ
    obtain ⟨y, q, hy, hqρ, _, hky, hkq⟩ := rankEmbedding_pair_preimages hρ hη hk hp hkp
    obtain ⟨τ, ζ, hτ, hζ, _, hkτ, hkζ⟩ := rankEmbedding_pair_preimages hρ hη hk hqρ hkq
    have hCτ : Cn (n + 2) τ := by
      have ht := rankEmbedding_cn_same_iff hρ hη hk hτ
      rw [hkτ] at ht
      exact ht.mpr hν
    let := hCτ.ordinal
    let := hierarchy_transitive τ
    have hζo : IsOrdinal ζ := by
      have ht := hk.bounded_defined_iff isOrdinalFormula_bounded (fun v ↦ IsOrdinal (v 0))
        ![ζ] (by simpa using hζ)
      apply ht.mpr
      change IsOrdinal (k ‘ ζ)
      rw [hkζ]
      exact hχ.ordinal
    let := hζo
    have hVτ := hρ.hierarchy_closed hCτ.ordinal hτ
    have hkVτ : k ‘ (hierarchy τ) = hierarchy κ := by
      rw [(rankEmbedding_value_hierarchy hρ hη hk hCτ.ordinal hτ).2, hkτ]
    have hyτ : y ∈ hierarchy τ := (hk.value_mem_iff hy hVτ).mp (by rwa [hky, hkVτ])
    have hζτ : ζ ∈ hierarchy τ := (hk.value_mem_iff hζ hVτ).mp (by
      rw [hkζ, hkVτ]
      exact hχ.mem_domain)
    have hr := rankEmbedding_restrict hρ hη hk hVτ
      ⟨ω, ordinal_subset_hierarchy τ _ hCτ.omega_lt⟩
    rw [hkVτ] at hr
    let := IsFunction.of_mem hk.function
    have hv : ∀ z ∈ hierarchy τ, (k ↾ (hierarchy τ)) ‘ z = k ‘ z := by
      intro z hz
      exact value_restrict (by
        rw [domain_eq_of_mem_function hk.function]
        exact (hierarchy_transitive ρ).mem_trans hz hVτ) hz
    have hmoved : (compose (k ↾ (hierarchy τ)) j) ‘ ζ ≠ ζ := by
      let := hj.value_ordinal hχ.ordinal hχ.mem_domain
      rw [value_compose_of_mem_function hr.function hj.function hζτ, hv ζ hζτ, hkζ]
      have hle : ζ ⊆ χ := hkζ ▸ hk.ordinal_subset_value hζo hζ
      have hlt : ζ ∈ j ‘ χ := ordinal_mem_of_subset_mem hle (hχ.lt_value hj)
      intro he
      rw [he] at hlt
      exact mem_irrefl ζ hlt
    obtain ⟨θ, hθ, hαθ⟩ := criticalPoint_exists_above
      (A := hierarchy τ) (f := compose (k ↾ (hierarchy τ)) j) (α := α)
      ⟨ζ, hζo, hζτ, hmoved⟩ (by
        intro z _ hz hle
        rw [value_compose_of_mem_function hr.function hj.function hz, hv z hz,
          hξ.fixed_below (ordinal_mem_of_subset_mem hle hαξ),
          hχ.fixed_below (ordinal_mem_of_subset_mem hle hαχ)])
    refine ⟨hμ, τ, y, compose (k ↾ (hierarchy τ)) j, θ,
      IsOrdinal.toIsTransitive.mem_trans (ordinal_mem_hierarchy_iff.mp hτ) hρκ,
      hCτ, hyτ, hr.comp hj, hθ, hαθ, ?_⟩
    rw [value_compose_of_mem_function hr.function hj.function hyτ, hv y hyτ, hky, hjx]
  · obtain ⟨_, ρ, y, k, ξ, hρκ, hρ, hy, hk, hξ, hαξ, hky⟩ :=
      hsmall ν hν hκν hνδ x hx
    let := hρ.ordinal
    let := hξ.ordinal
    let := hierarchy_transitive ρ
    obtain ⟨θ, hθ, hαθ⟩ := hk.comp_criticalPoint_above hj (α := α)
      ⟨ξ, hξ.ordinal, hξ.mem_domain, hξ.moved⟩
      (fun z _ _ hle ↦ hξ.fixed_below (ordinal_mem_of_subset_mem hle hαξ))
      (fun z _ _ hle ↦ hχ.fixed_below (ordinal_mem_of_subset_mem hle hαχ))
    refine ⟨hμ, ρ, y, compose k j, θ, hρκ, hρ, hy, hk.comp hj, hθ, hαθ, ?_⟩
    rw [value_compose_of_mem_function hk.function hj.function hy, hky, hjx]

end ZFVP
