import ZFVP.ModelTheory.LocalRestorationRankThreshold

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.bounded_localRestorationRankThreshold {δ κ θ : V}
    (hδ : IsWoodinSupercompact δ) (hκ : IsRegularCardinal κ) (hκδ : κ ∈ δ) (hθδ : θ ∈ δ) :
    ∃ η ∈ δ, ∀ γ ∈ θ, IsLocalRestorationRankThreshold κ γ η := by
  let := hδ.1.1
  let := IsOrdinal.of_mem hθδ
  let R : V → V → Prop := fun γ η ↦ IsOrdinal η ∧ IsLocalRestorationRankThreshold κ γ η
  have hR : ℒₛₑₜ-relation R := by unfold R; definability
  have hex : ∀ γ ∈ θ, ∃ η ∈ hierarchy δ, R γ η := by
    intro γ hγ
    obtain ⟨η, hη, ht⟩ := hδ.localRestorationRankThreshold_exists hκ hκδ
      (IsOrdinal.toIsTransitive.mem_trans hγ hθδ)
    let := IsOrdinal.of_mem hη
    exact ⟨η, ordinal_mem_hierarchy_iff.mpr hη, inferInstance, ht⟩
  obtain ⟨b, hb, hall⟩ := hδ.inaccessible.rankCriterion.2.2.2.collection
    (fun _ hx ↦ regularCardinal_succ_closed hδ.inaccessible.regular hx)
    (ordinal_mem_hierarchy_iff.mpr hθδ) R hR hex
  refine ⟨rank b, (mem_hierarchy_iff_rank_mem _ _).mp hb, ?_⟩
  intro γ hγ
  obtain ⟨η, hηb, hηord, ht⟩ := hall γ hγ
  let := hηord
  have hη : η ∈ rank b := ordinal_mem_hierarchy_iff.mp
    ((mem_hierarchy_iff_rank_mem _ _).mpr (rank_mem hηb))
  exact ht.mono hη

end ZFVP
