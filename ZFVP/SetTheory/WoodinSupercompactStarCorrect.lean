import ZFVP.SetTheory.WoodinSupercompactInaccessible

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.starCorrect_cofinal {δ : V} (hδ : IsWoodinSupercompact δ)
    {η : V} (hη : η ∈ δ) :
    ∃ ρ ∈ δ, η ∈ ρ ∧ IsSigmaOneStarCorrect ρ := by
  let := hδ.1.1
  obtain ⟨θ, hδθ, hθ⟩ := sigmaOneStarCorrect_unbounded δ
  let := hθ.1.ordinal
  have h0θ : (∅ : V) ∈ hierarchy θ := (hierarchy_transitive θ).mem_trans
    (show (∅ : V) ∈ ω by simp) (ordinal_mem_hierarchy_iff.mpr hθ.1.omega_lt)
  obtain ⟨_, ρ, hρδ, hρ, _, _, e, he, c, hc, hec, _, hηc⟩ :=
    hδ.highCritical.2.2 θ hδθ hθ ∅ h0θ η hη
  let := hρ.1.ordinal
  let := hc.ordinal
  let := hierarchy_transitive (succ ρ)
  let := hierarchy_transitive (succ θ)
  have hcρ := successorRankEmbedding_criticalPoint_lt_height he hc (hec.symm ▸ hδθ)
  exact ⟨ρ, hρδ, IsOrdinal.toIsTransitive.mem_trans hηc hcρ, hρ⟩

theorem IsWoodinSupercompact.cn_one {δ : V} (hδ : IsWoodinSupercompact δ) : Cn 1 δ := by
  let := hδ.1.1
  apply cn_closed 1 ⟨ω, hδ.omega_lt⟩
  intro η hη
  obtain ⟨ρ, hρδ, hηρ, hρ⟩ := hδ.starCorrect_cofinal hη
  exact ⟨ρ, hρδ, hηρ, hρ.1⟩

theorem IsWoodinSupercompact.sigmaOneStarCorrect {δ : V} (hδ : IsWoodinSupercompact δ) :
    IsSigmaOneStarCorrect δ := by
  let := hδ.1.1
  refine ⟨hδ.cn_one, ?_⟩
  intro α hα a ha φ hφ hex
  let := IsOrdinal.of_mem hα
  let := ordinal_union_ordinal α (rank a)
  have hr := (mem_hierarchy_iff_rank_mem _ _).mp ha
  obtain ⟨ρ, hρδ, hbound, hρ⟩ := hδ.starCorrect_cofinal (ordinal_union_mem hα hr)
  let := hρ.1.ordinal
  have hαρ : α ∈ ρ := ordinal_mem_of_subset_mem (subset_union_left α (rank a)) hbound
  have haρ : a ∈ hierarchy ρ := (mem_hierarchy_iff_rank_mem _ _).mpr
    (ordinal_mem_of_subset_mem (subset_union_right α (rank a)) hbound)
  obtain ⟨b, hb, hw⟩ := hρ.2 α hαρ a haρ φ hφ hex
  exact ⟨b, hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hρδ) _ hb, hw⟩

end ZFVP
