import ZFVP.ModelTheory.MarkerMembership
import ZFVP.ModelTheory.LimitCriticalPoint
import ZFVP.SetTheory.VopenkaDefinableClasses
import ZFVP.SetTheory.NaturalAddition
import ZFVP.SetTheory.WitnessClosure

/-! The one-marker rank structures in the direct proof of the ZF-rank lemma. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def rankMarkerStructure (ρ δ : V) : V :=
  markerStructure (hierarchy ρ) (hierarchy (ordinalAdd δ ω)) δ

instance rankMarkerStructure_definable : ℒₛₑₜ-function₂[V] rankMarkerStructure := by
  unfold rankMarkerStructure
  definability

def IsRankMarkerStructure (ρ M : V) : Prop :=
  ∃ δ, IsOrdinal δ ∧ ρ ⊆ δ ∧ M = rankMarkerStructure ρ δ

instance isRankMarkerStructure_definable : ℒₛₑₜ-relation[V] IsRankMarkerStructure := by
  unfold IsRankMarkerStructure
  definability

theorem rankMarkerStructure_base_subset {ρ δ : V} [IsOrdinal ρ] [IsOrdinal δ]
    (hρ : ρ ⊆ δ) : hierarchy ρ ⊆ hierarchy (ordinalAdd δ ω) :=
  hierarchy_mono (subset_trans hρ (subset_ordinalAdd δ ω))

theorem rankMarkerStructure_marker_mem (δ : V) [IsOrdinal δ] :
    δ ∈ hierarchy (ordinalAdd δ ω) :=
  ordinal_subset_hierarchy _ _ (ordinalAdd_omega_gt δ)

theorem rankMarkerStructure_expansion {ρ δ : V} [IsOrdinal ρ] [IsOrdinal δ]
    (hρ : ρ ⊆ δ) :
    IsMembershipExpansion (namedMembershipLanguageCode (succ (hierarchy ρ)))
      (rankMarkerStructure ρ δ) :=
  markerStructure_expansion ⟨δ, rankMarkerStructure_marker_mem δ⟩
    (rankMarkerStructure_base_subset hρ) (rankMarkerStructure_marker_mem δ)

theorem rankMarkerStructure_proper (ρ : V) [IsOrdinal ρ] :
    IsProperClass (IsRankMarkerStructure ρ) := by
  intro C
  let σ := ρ ∪ rank C
  let : IsOrdinal σ := ordinal_union_ordinal _ _
  let δ := succ σ
  have hρ : ρ ⊆ δ := by
    intro x hx
    exact mem_succ_iff.mpr (Or.inr (mem_union_iff.mpr (Or.inl hx)))
  have hCδ : rank C ∈ δ := by
    have hs : rank C ⊆ σ := fun x hx ↦ mem_union_iff.mpr (Or.inr hx)
    exact mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hs)
  refine ⟨rankMarkerStructure ρ δ, ⟨δ, inferInstance, hρ, rfl⟩, ?_⟩
  intro hm
  have hM := subset_hierarchy_rank C _ hm
  let := hierarchy_transitive (rank C)
  have hA : hierarchy (ordinalAdd δ ω) ∈ hierarchy (rank C) :=
    (kpair_components_mem_transitive hM).1
  have hδC : ordinalAdd δ ω ∈ rank C := by
    simpa only [rank_hierarchy] using (mem_hierarchy_iff_rank_mem _ _).mp hA
  have hCδ := IsOrdinal.toIsTransitive.mem_trans hCδ (ordinalAdd_omega_gt δ)
  exact mem_asymm hδC hCδ

theorem vopenka_rankMarker_embedding
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (ρ : V) [IsOrdinal ρ] :
    ∃ δ μ f : V, IsOrdinal δ ∧ IsOrdinal μ ∧ ρ ⊆ δ ∧ ρ ⊆ μ ∧ δ ≠ μ ∧
      IsCodedMembershipEmbedding (hierarchy (ordinalAdd δ ω)) (hierarchy (ordinalAdd μ ω)) f ∧
      f ‘ δ = μ ∧ ∀ x ∈ hierarchy ρ, f ‘ x = x := by
  obtain ⟨M, N, f, hne, hM, hN, hf⟩ := vopenka_definable_class hVP
    (namedMembershipLanguageCode (succ (hierarchy ρ))) (IsRankMarkerStructure ρ)
    (by definability) (rankMarkerStructure_proper ρ) (by
      rintro M ⟨δ, hδ, hρ, rfl⟩
      let := hδ
      exact (rankMarkerStructure_expansion hρ).2.1)
  obtain ⟨δ, hδ, hρδ, rfl⟩ := hM
  obtain ⟨μ, hμ, hρμ, rfl⟩ := hN
  let := hδ
  let := hμ
  have hv := hf.marker_values (rankMarkerStructure_base_subset hρδ)
    (rankMarkerStructure_marker_mem δ)
  refine ⟨δ, μ, f, hδ, hμ, hρδ, hρμ, ?_, ?_, hv⟩
  · intro he
    subst μ
    exact hne rfl
  · simpa only [rankMarkerStructure, markerStructure_domain] using
      hf.membership_reduct (rankMarkerStructure_expansion hρδ) (rankMarkerStructure_expansion hρμ)

theorem IsCriticalPoint.fixed_rank_bound {A f κ ρ : V} [IsOrdinal ρ]
    (hκ : IsCriticalPoint A f κ) (hfix : ∀ x ∈ hierarchy ρ, f ‘ x = x) : ρ ⊆ κ := by
  let := hκ.ordinal
  rcases IsOrdinal.mem_trichotomy ρ κ with hlt | he | hgt
  · exact IsOrdinal.toIsTransitive.transitive _ hlt
  · exact he ▸ subset_refl ρ
  · exact False.elim (hκ.moved (hfix κ (ordinal_subset_hierarchy ρ κ hgt)))

theorem vopenka_rankMarker_criticalPoint_above
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (γ : V) [IsOrdinal γ] :
    ∃ δ μ f κ : V, IsOrdinal δ ∧ IsOrdinal μ ∧
      IsCodedMembershipEmbedding (hierarchy (ordinalAdd δ ω)) (hierarchy (ordinalAdd μ ω)) f ∧
      IsCriticalPoint (hierarchy (ordinalAdd δ ω)) f κ ∧ γ ∈ κ ∧ (ω : V) ∈ κ := by
  let b := γ ∪ (ω : V)
  let : IsOrdinal b := ordinal_union_ordinal _ _
  let ρ := succ b
  obtain ⟨δ, μ, f, hδ, hμ, _, _, hne, hf, hval, hfix⟩ := vopenka_rankMarker_embedding hVP ρ
  let := hδ
  let := hμ
  let := hierarchy_transitive (ordinalAdd δ ω)
  let := hierarchy_transitive (ordinalAdd μ ω)
  have hmove : f ‘ δ ≠ δ := fun he ↦ hne (he.symm.trans hval)
  obtain ⟨κ, hκ, _⟩ := criticalPoint_exists_of_moved_ordinal hδ
    (rankMarkerStructure_marker_mem δ) hmove
  have hρκ := hκ.fixed_rank_bound hfix
  have hγρ : γ ∈ ρ := by
    exact mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (show γ ⊆ b from
      fun x hx ↦ mem_union_iff.mpr (Or.inl hx)))
  have hωρ : (ω : V) ∈ ρ := by
    exact mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (show (ω : V) ⊆ b from
      fun x hx ↦ mem_union_iff.mpr (Or.inr hx)))
  exact ⟨δ, μ, f, κ, hδ, hμ, hf, hκ, hρκ _ hγρ, hρκ _ hωρ⟩

theorem vopenka_direct_rankCriterion_unbounded
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (γ : V) [IsOrdinal γ] : ∃ κ : V, γ ∈ κ ∧ IsRankCriterionHeight κ := by
  obtain ⟨δ, μ, f, κ, hδ, hμ, hf, hκ, hγκ, hωκ⟩ := vopenka_rankMarker_criticalPoint_above hVP γ
  let := hδ
  let := hμ
  let := hierarchy_transitive (ordinalAdd μ ω)
  exact ⟨κ, hγκ, limitRankEmbedding_criticalPoint_rankCriterion
    (fun _ ↦ ordinalAdd_omega_succ_closed δ) hf hκ hωκ⟩

end ZFVP
