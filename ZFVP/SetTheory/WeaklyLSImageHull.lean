import ZFVP.SetTheory.StrongLSWeakLS

/-! Weak LS hulls can contain two images of lower rank sets. This supplies
directedness for the small-hull family in Usuba's singular-cardinal argument. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ordinal_common_upper_bound {κ δ ε : V} [IsOrdinal κ]
    (hδ : δ ∈ κ) (hε : ε ∈ κ) : ∃ γ ∈ κ, δ ⊆ γ ∧ ε ⊆ γ := by
  let := IsOrdinal.of_mem hδ
  let := IsOrdinal.of_mem hε
  rcases IsOrdinal.subset_or_supset (α := δ) (β := ε) with h | h
  · exact ⟨ε, hε, h, subset_refl _⟩
  · exact ⟨δ, hδ, subset_refl _, h⟩

theorem IsWeaklyLSCardinal.hull_for_two_images {κ γ α x e₀ e₁ : V}
    (hκ : IsWeaklyLSCardinal κ) (hγκ : γ ∈ κ) [IsOrdinal α]
    (hκα : κ ⊆ α) (hx : x ∈ hierarchy α) [IsFunction e₀] [IsFunction e₁]
    (hd₀ : domain e₀ ⊆ hierarchy γ) (hd₁ : domain e₁ ⊆ hierarchy γ)
    (hr₀ : range e₀ ⊆ hierarchy α) (hr₁ : range e₁ ⊆ hierarchy α) :
    ∃ Z, IsElementaryInclusion Z (hierarchy α) ∧ x ∈ Z ∧
      HasSmallTransitiveCollapse κ Z ∧ range e₀ ⊆ Z ∧ range e₁ ⊆ Z := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hγκ
  have hωκ : (ω : V) ⊆ κ := IsOrdinal.toIsTransitive.transitive _ hκ.2.1
  have hsω : succ (ω : V) ∈ κ := initial_succ_mem hκ.1 hωκ hκ.2.1
  obtain ⟨δ, hδκ, hγδ, hlowδ⟩ := ordinal_common_upper_bound hγκ hsω
  let := IsOrdinal.of_mem hδκ
  let a := hierarchy α
  let U := codingUniverse a
  let T := membershipModelTruthTable a
  let p := ⟨⟨⟨U, T⟩ₖ, ⟨a, x⟩ₖ⟩ₖ, ⟨e₀, e₁⟩ₖ⟩ₖ
  let η := rank ({p, κ} : V)
  have hpη : p ∈ hierarchy η := (mem_hierarchy_iff_rank_mem _ _).mpr
    (rank_mem (show p ∈ ({p, κ} : V) by simp))
  have hκη : κ ∈ η := by
    simpa only [rank_of_ordinal] using rank_mem (show κ ∈ ({p, κ} : V) by simp)
  let := hierarchy_transitive η
  obtain ⟨Y, hY, hδY, hpY, hsmall⟩ :=
    hκ.2.2 δ hδκ η inferInstance (IsOrdinal.toIsTransitive.transitive _ hκη) p hpη
  have hp := hY.kpair_components_mem hpY
  have hp' := hY.kpair_components_mem hp.1
  have hUT := hY.kpair_components_mem hp'.1
  have hax := hY.kpair_components_mem hp'.2
  have heY := hY.kpair_components_mem hp.2
  have hlow : hierarchy (succ (ω : V)) ⊆ Y := subset_trans (hierarchy_mono hlowδ) hδY
  obtain ⟨C, hC, f, hf⟩ := hsmall
  let : IsTransitive a := hierarchy_transitive α
  let : IsSequenceSupport U := codingUniverse_isSequenceSupport a
  have haU : a ⊆ U := (codingUniverse_transitive a).transitive a (self_mem_codingUniverse a)
  have he : IsElementaryInclusion (Y ∩ a) a :=
    elementaryIntersection_of_truthTable hY hf hlow hax.1 ⟨x, hx⟩ hUT.1 haU hUT.2
      (membershipModelTruthTable_correct a)
  have hγY : hierarchy γ ⊆ Y := subset_trans (hierarchy_mono hγδ) hδY
  have himage (e : V) [IsFunction e] (heY : e ∈ Y) (hd : domain e ⊆ hierarchy γ)
      (hr : range e ⊆ a) : range e ⊆ Y ∩ a := by
    intro z hz
    obtain ⟨u, huz⟩ := mem_range_iff.mp hz
    have hu := mem_domain_of_kpair_mem huz
    have hv := hY.function_value_mem heY (hγY u (hd u hu)) hu
    exact mem_inter_iff.mpr ⟨value_eq_of_kpair_mem huz ▸ hv, hr z hz⟩
  exact ⟨Y ∩ a, he, mem_inter_iff.mpr ⟨hax.2, hx⟩,
    ⟨f ‘ a, (hierarchy_transitive κ).mem_trans (function_value_mem hf.2.1 hax.1) hC,
      f ↾ (Y ∩ a), transitiveCollapse_restrict_member hf hax.1⟩,
    himage e₀ heY.1 hd₀ hr₀, himage e₁ heY.2 hd₁ hr₁⟩

end ZFVP
