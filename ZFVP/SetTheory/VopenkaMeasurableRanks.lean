import ZFVP.SetTheory.RankMarkerStructures
import ZFVP.ModelTheory.DerivedUltrafilterComplete

/-! The direct VP rank argument supplies a measurable ordinal satisfying the ZF rank criterion. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem vopenka_measurable_rankCriterion_unbounded
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (γ : V) [IsOrdinal γ] :
    ∃ κ : V, γ ∈ κ ∧ IsRankCriterionHeight κ ∧ IsMeasurableOrdinal κ := by
  obtain ⟨δ, μ, f, κ, hδ, hμ, hf, hκ, hγκ, hωκ⟩ := vopenka_rankMarker_criticalPoint_above hVP γ
  let := hδ
  let := hμ
  let := hierarchy_transitive (ordinalAdd μ ω)
  have hc : ∀ β ∈ ordinalAdd δ ω, succ β ∈ ordinalAdd δ ω :=
    fun _ ↦ ordinalAdd_omega_succ_closed δ
  exact ⟨κ, hγκ, limitRankEmbedding_criticalPoint_rankCriterion hc hf hκ hωκ,
    limitRankEmbedding_criticalPoint_measurable hc hf hκ hωκ⟩

theorem vopenka_measurable_internalZFRanks_unbounded
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (γ : V) [IsOrdinal γ] :
    ∃ κ : V, γ ∈ κ ∧ IsInternalZFModel (hierarchy κ) ∧ IsMeasurableOrdinal κ := by
  obtain ⟨κ, hγκ, hκ, hm⟩ := vopenka_measurable_rankCriterion_unbounded hVP γ
  exact ⟨κ, hγκ, hκ.internalZFModel, hm⟩

end ZFVP
