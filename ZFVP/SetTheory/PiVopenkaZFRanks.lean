import ZFVP.SetTheory.PiOneRankMarkerClass
import ZFVP.SetTheory.VopenkaLevyClasses
import ZFVP.SetTheory.VopenkaZFRanks
import ZFVP.SetTheory.LeastRankCriterionCode

/-! Every positive Pi fragment of arbitrary-language VP supplies unbounded internal ZF ranks. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem pi_vopenka_rankMarker_embedding {k : ℕ} (hk : 0 < k)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula k φ → VopenkaInstance (V := V) φ)
    (ρ : V) [IsOrdinal ρ] :
    ∃ δ μ f : V, IsOrdinal δ ∧ IsOrdinal μ ∧ ρ ⊆ δ ∧ ρ ⊆ μ ∧ δ ≠ μ ∧
      IsCodedMembershipEmbedding (hierarchy (ordinalAdd δ ω)) (hierarchy (ordinalAdd μ ω)) f ∧
      f ‘ δ = μ ∧ ∀ x ∈ hierarchy ρ, f ‘ x = x := by
  obtain ⟨M, N, f, hne, hM, hN, hf⟩ := vopenka_levy_definable_class hk hVP
    (namedMembershipLanguageCode (succ (hierarchy ρ))) (IsRankMarkerStructure ρ)
    piOneRankMarkerClassFormula (piOneRankMarkerClassFormula_piOne.mono hk) ![ρ, hierarchy ρ]
    (fun M ↦ eval_piOneRankMarkerClassFormula_hierarchy M ρ)
    (rankMarkerStructure_proper ρ) (by
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

theorem pi_vopenka_rankMarker_criticalPoint_above {k : ℕ} (hk : 0 < k)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula k φ → VopenkaInstance (V := V) φ)
    (γ : V) [IsOrdinal γ] :
    ∃ δ μ f κ : V, IsOrdinal δ ∧ IsOrdinal μ ∧
      IsCodedMembershipEmbedding (hierarchy (ordinalAdd δ ω)) (hierarchy (ordinalAdd μ ω)) f ∧
      IsCriticalPoint (hierarchy (ordinalAdd δ ω)) f κ ∧ γ ∈ κ ∧ (ω : V) ∈ κ := by
  let b := γ ∪ (ω : V)
  let : IsOrdinal b := ordinal_union_ordinal _ _
  let ρ := succ b
  obtain ⟨δ, μ, f, hδ, hμ, _, _, hne, hf, hval, hfix⟩ := pi_vopenka_rankMarker_embedding hk hVP ρ
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

theorem pi_vopenka_rankCriterion_unbounded {k : ℕ} (hk : 0 < k)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula k φ → VopenkaInstance (V := V) φ)
    (γ : V) [IsOrdinal γ] : ∃ κ : V, γ ∈ κ ∧ IsRankCriterionHeight κ := by
  obtain ⟨δ, μ, f, κ, hδ, hμ, hf, hκ, hγκ, hωκ⟩ := pi_vopenka_rankMarker_criticalPoint_above hk hVP γ
  let := hδ
  let := hμ
  let := hierarchy_transitive (ordinalAdd μ ω)
  exact ⟨κ, hγκ, limitRankEmbedding_criticalPoint_rankCriterion
    (fun _ ↦ ordinalAdd_omega_succ_closed δ) hf hκ hωκ⟩

theorem pi_vopenka_internalZFRanks_unbounded {k : ℕ} (hk : 0 < k)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula k φ → VopenkaInstance (V := V) φ)
    (α : V) [IsOrdinal α] : ∃ θ : V, IsOrdinal θ ∧ α ∈ θ ∧ IsInternalZFModel (hierarchy θ) := by
  obtain ⟨θ, hαθ, hθ⟩ := pi_vopenka_rankCriterion_unbounded hk hVP α
  exact ⟨θ, hθ.1, hαθ, hθ.internalZFModel⟩

theorem pi_vopenka_leastZFRankAbove_existsUnique {k : ℕ} (hk : 0 < k)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula k φ → VopenkaInstance (V := V) φ)
    (α : V) [IsOrdinal α] : ∃! θ : V, IsLeastZFRankAbove α θ :=
  leastOrdinal_existsUnique _ (by definability) (pi_vopenka_internalZFRanks_unbounded hk hVP α)

theorem pi_vopenka_leastRankCriterionAbove_existsUnique {k : ℕ} (hk : 0 < k)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula k φ → VopenkaInstance (V := V) φ)
    (b : V) [IsOrdinal b] : ∃! θ : V, IsLeastRankCriterionAbove b θ := by
  apply leastOrdinal_existsUnique _ (by definability)
  obtain ⟨θ, hb, hθ⟩ := pi_vopenka_rankCriterion_unbounded hk hVP b
  exact ⟨θ, hθ.1, hb, hθ⟩

theorem pi_vopenka_leastRankCriterionCode_existsUnique {k : ℕ} (hk : 0 < k)
    (hVP : ∀ φ : SetTheorySemisentence 2, IsPiFormula k φ → VopenkaInstance (V := V) φ)
    (b : V) [IsOrdinal b] : ∃! c : V, leastRankCriterionCodeFormula.Evalb ![c, b] := by
  obtain ⟨θ, hθ, _⟩ := pi_vopenka_leastRankCriterionAbove_existsUnique hk hVP b
  obtain ⟨d, hd, _⟩ := leastRankCriterionCertificate_exists hθ
  have hc := (eval_leastRankCriterionCodeFormula ⟨θ, d⟩ₖ b).mpr ⟨θ, d, rfl, hd⟩
  exact ⟨⟨θ, d⟩ₖ, hc, fun c hc' ↦ leastRankCriterionCode_unique hc' hc⟩

end ZFVP
