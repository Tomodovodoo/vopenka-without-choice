import ZFVP.SetTheory.FullChoicelessCardinals
import ZFVP.ModelTheory.RankEmbeddingRangeClosure

/-! Every 2-choiceless supercompact cardinal is LS. The source correct
rank is closed under function sets, supplying the finite rank padding
used explicitly in the paper's small-embedding argument. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsChoicelessSupercompact.lsCardinal {κ : V}
    (hκ : IsChoicelessSupercompact 2 κ) : IsLSCardinal κ := by
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
  obtain ⟨β, y, hβV, hyV, _, hβimage, hyimage⟩ :=
    rankEmbedding_pair_preimages hν hη hj ha hpair
  have hβ : IsOrdinal β := by
    apply (hj.bounded_defined_iff isOrdinalFormula_bounded (fun v ↦ IsOrdinal (v 0))
      ![β] (by simpa using hβV)).mpr
    change IsOrdinal (f ‘ β)
    rwa [hβimage]
  let := hβ
  have hβν : β ∈ ν := ordinal_mem_hierarchy_iff.mp hβV
  have hVδc : hierarchy δ ∈ hierarchy c := hierarchy_mem hδc
  have hVcV := hν.hierarchy_closed hc.ordinal hc.mem_domain
  have hδrange : hierarchy δ ⊆ range f := by
    intro u hu
    have huC := (hierarchy_transitive c).mem_trans hu hVδc
    have huV := (hierarchy_transitive ν).mem_trans huC hVcV
    have hfix := rankEmbedding_fixed_below_criticalPoint hν hη hj hc u huC
    exact hfix ▸ value_mem_range hj.function huV
  refine ⟨η, range f, hη.ordinal, IsOrdinal.toIsTransitive.transitive _ hαη,
    hj.range_elementary, hδrange, ?_, hj.range_smallCollapse (hierarchy_mem hνκ), ?_⟩
  · exact hyimage ▸ value_mem_range hj.function hyV
  · have hh := rankEmbedding_range_function_closed hν hη hj hc hδc hβ hβν
    rwa [hβimage] at hh

end ZFVP
