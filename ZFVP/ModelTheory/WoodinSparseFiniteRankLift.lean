import ZFVP.ModelTheory.FiniteRankLiftExtension
import ZFVP.ModelTheory.FiniteRankLiftChecks
import ZFVP.ModelTheory.WoodinSparseMarkedNameCoverage

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω γ δ e : V} [IsOrdinal Ω] [IsOrdinal γ] [IsOrdinal δ]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G)
  (hγ : γ ∈ Ω) (hδ : δ ∈ Ω)
local notation "A" => woodinSparseFixedPointContext hΩ hAC hG hγ
local notation "B" => woodinSparseFixedPointContext hΩ hAC hG hδ

theorem woodinSparseFixedPointContext_finiteRankLiftData
    (hfixγ : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ)
    (hfixδ : (kpair.π₂ (woodinIterationRec Ω)) ‘ δ = δ)
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd γ (ω : V)))
      (hierarchy (ordinalAdd δ (ω : V))) e)
    (hP : e ‘ (A).P = (B).P) (hg : ∀ p ∈ (A).G, e ‘ p ∈ (B).G) :
    FiniteRankLiftData (A) (B) γ δ e := by
  have hrA := woodinSparseFixedPointContext_rank hΩ hAC hG hγ hfixγ
  have hrB := woodinSparseFixedPointContext_rank hΩ hAC hG hδ hfixδ
  have hγΩ : γ ⊆ Ω := IsOrdinal.toIsTransitive.transitive _ hγ
  have hδΩ : δ ⊆ Ω := IsOrdinal.toIsTransitive.transitive _ hδ
  have he' : IsCodedMembershipEmbedding (hierarchy (ordinalAdd (rank (A).P) (ω : V)))
      (hierarchy (ordinalAdd (rank (B).P) (ω : V))) e := by rwa [hrA, hrB]
  have hinA : IsChoicelessInaccessible γ := by
    rw [← hrA]
    exact woodinSparseStageCode_rank_inaccessible hΩ hAC hγΩ
  have hinB : IsChoicelessInaccessible δ := by
    rw [← hrB]
    exact woodinSparseStageCode_rank_inaccessible hΩ hAC hδΩ
  have hpA : (A).P ∈ hierarchy (ordinalAdd γ (ω : V)) := by
    apply (mem_hierarchy_iff_rank_mem _ _).mpr
    rw [hrA]
    exact ordinalAdd_omega_gt γ
  have hfγ : e ‘ γ = δ := by
    let := hierarchy_transitive (ordinalAdd δ (ω : V))
    rw [← hrA, limitRankEmbedding_value_rank (fun _ ↦ ordinalAdd_omega_succ_closed γ) he hpA,
      hP, hrB]
  refine ⟨hinA, hinB, he, ?_, ?_, hP, ?_, hfγ, hg,
    woodinSparseFixedPointContext_low_name_coverage hΩ hAC hG hγ hfixγ,
    woodinSparseFixedPointContext_low_name_coverage hΩ hAC hG hδ hfixδ⟩
  · simpa only [hrA] using subset_hierarchy_rank (A).P
  · simpa only [hrB] using subset_hierarchy_rank (B).P
  · exact woodinSparseStageCode_order_covariance hΩ hΩ hAC hγΩ hδΩ he' hP

end ZFVP

