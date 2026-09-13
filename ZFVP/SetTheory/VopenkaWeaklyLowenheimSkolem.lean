import ZFVP.SetTheory.VopenkaFullChoiceless
import ZFVP.ModelTheory.RankEmbeddingRangeClosure

/-! Small rank embeddings give weak LS witnesses in the requested rank itself.
This supplies the weak-LS hypothesis in Usuba's collapse theorem directly from VP. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsChoicelessSupercompact.weaklyLSCardinal {κ : V}
    (hκ : IsChoicelessSupercompact 2 κ) : IsWeaklyLSCardinal κ := by
  let := hκ.1
  refine ⟨hκ.initial, hκ.omega_lt, ?_⟩
  intro δ hδκ α hα hκα x hx
  let := hα
  let := IsOrdinal.of_mem hδκ
  obtain ⟨η, hαη, hη⟩ := cn_unbounded 2 α
  let := hη.ordinal
  let := hierarchy_transitive η
  have hκη := ordinal_mem_of_subset_mem hκα hαη
  have hαV := ordinal_subset_hierarchy η α hαη
  have hxV := (hierarchy_transitive η).mem_trans hx (hierarchy_mem hαη)
  have hp := kpair_mem_hierarchy_limit hη.successor_closed hαV hxV
  obtain ⟨_, ν, a, f, c, hνκ, hν, ha, hj, hc, hδc, hpair⟩ :=
    (hκ.2.2 δ hδκ).2.2 η hη hκη _ hp
  let := hν.ordinal
  let := hierarchy_transitive ν
  let := hc.ordinal
  let := hierarchy_transitive c
  let := IsFunction.of_mem hj.function
  obtain ⟨β, y, hβV, hyV, _, hβimage, hyimage⟩ :=
    rankEmbedding_pair_preimages hν hη hj ha hpair
  have hβ : IsOrdinal β := by
    apply (hj.bounded_defined_iff isOrdinalFormula_bounded (fun v ↦ IsOrdinal (v 0))
      ![β] (by simpa using hβV)).mpr
    change IsOrdinal (f ‘ β)
    rwa [hβimage]
  let := hβ
  let := hierarchy_transitive β
  have hβν : β ∈ ν := ordinal_mem_hierarchy_iff.mp hβV
  have hVβ := hierarchy_mem hβν
  have hmap : f ‘ (hierarchy β) = hierarchy α := by
    rw [(rankEmbedding_value_hierarchy hν hη hj hβ hβV).2, hβimage]
  have hyβ : y ∈ hierarchy β := by
    apply (hj.value_mem_iff hyV hVβ).mp
    rwa [hmap, hyimage]
  have hr := rankEmbedding_restrict hν hη hj hVβ (show IsNonempty (hierarchy β) from ⟨y, hyβ⟩)
  rw [hmap] at hr
  have hδrange : hierarchy δ ⊆ range (f ↾ (hierarchy β)) := by
    intro u hu
    have huC := (hierarchy_transitive c).mem_trans hu (hierarchy_mem hδc)
    have huV := (hierarchy_transitive ν).mem_trans huC
      (hν.hierarchy_closed hc.ordinal hc.mem_domain)
    have hfix := rankEmbedding_fixed_below_criticalPoint hν hη hj hc u huC
    have huα : u ∈ hierarchy α :=
      hierarchy_mono (subset_trans (IsOrdinal.toIsTransitive.transitive _ hδκ) hκα) u hu
    have huβ : u ∈ hierarchy β := by
      apply (hj.value_mem_iff huV hVβ).mp
      rwa [hfix, hmap]
    have hv : (f ↾ (hierarchy β)) ‘ u = u := by
      rw [value_restrict (domain_eq_of_mem_function hj.function |>.symm ▸ huV) huβ, hfix]
    exact hv ▸ value_mem_range hr.function huβ
  refine ⟨range (f ↾ (hierarchy β)), hr.range_elementary, hδrange, ?_,
    hr.range_smallCollapse (hierarchy_mem (IsOrdinal.toIsTransitive.mem_trans hβν hνκ))⟩
  have hv : (f ↾ (hierarchy β)) ‘ y = x := by
    rw [value_restrict (domain_eq_of_mem_function hj.function |>.symm ▸ hyV) hyβ, hyimage]
  exact hv ▸ value_mem_range hr.function hyβ

theorem vopenka_singular_weaklyLSCardinal
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (ξ : V) [IsOrdinal ξ] :
    ∃ κ : V, ξ ∈ κ ∧ IsWeaklyLSCardinal κ ∧ internalCofinality κ = ω ∧
      internalCofinality κ ∈ κ := by
  obtain ⟨κ, hξκ, hκ, _, hωκ, hcf⟩ :=
    vopenka_choicelessSupercompact_cofinality_omega hVP 0 ξ
  exact ⟨κ, hξκ, hκ.weaklyLSCardinal, hcf, hcf.symm ▸ hωκ⟩

end ZFVP



