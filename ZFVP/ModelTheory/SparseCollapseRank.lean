import ZFVP.ModelTheory.NormalizedPoolRank
import ZFVP.ModelTheory.SaturatedCollapseRankWitness

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem normalizedPrefixPool_rank_cofinal {P R one κ δ : V} [IsOrdinal κ]
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (h1 : (1 : V) ∈ κ) (hκ : κ ⊆ δ) :
    ∀ β ∈ δ, ∃ τ ∈ normalizedNamePool P R one δ (saturatedWoodinPrefixPosetName P R one κ δ),
      β ∈ rank τ := by
  apply normalizedNamePool_rank_cofinal hR ht hδ hP
  intro β hβ
  let := hδ.1
  let := IsOrdinal.of_mem hβ
  exact ⟨woodinCollapseRankWitness β, woodinCollapseRankWitness_mem_hierarchy hδ.rankCriterion.2.2.1 hβ,
    woodinCollapseRankWitness_rank β, saturatedWoodinPrefixPosetName_rankWitness hR ht hδ hP h1 hκ hβ⟩

theorem normalizedHartogsPool_rank_cofinal {P R one γ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (hγ : γ ∈ δ) (h1 : (1 : V) ⊆ γ) :
    ∀ β ∈ δ, ∃ τ ∈ normalizedNamePool P R one δ (saturatedHartogsPosetName P R one γ δ),
      β ∈ rank τ := by
  apply normalizedNamePool_rank_cofinal hR ht hδ hP
  intro β hβ
  let := hδ.1
  let := IsOrdinal.of_mem hβ
  exact ⟨woodinCollapseRankWitness β, woodinCollapseRankWitness_mem_hierarchy hδ.rankCriterion.2.2.1 hβ,
    woodinCollapseRankWitness_rank β, saturatedHartogsPosetName_rankWitness hR ht hδ hP hγ h1 hβ⟩

theorem sparseNormalizedPrefix_rank_lower {a P R κ δ : V} [IsOrdinal κ]
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R ∅)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (hsp : ∀ p ∈ P, IsSparseFunctionOn a p) (h1 : (1 : V) ∈ κ) (hκ : κ ⊆ δ) :
    δ ⊆ rank (sparseNormalizedTwoStep a P R ∅ δ (saturatedWoodinPrefixPosetName P R ∅ κ δ)) :=
  sparsePairCarrier_rank_lower hsp ht.1 (normalizedPrefixPool_rank_cofinal hR ht hδ hP h1 hκ)

theorem sparseNormalizedHartogs_rank_lower {a P R γ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R ∅)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (hsp : ∀ p ∈ P, IsSparseFunctionOn a p) (hγ : γ ∈ δ) (h1 : (1 : V) ⊆ γ) :
    δ ⊆ rank (sparseNormalizedTwoStep a P R ∅ δ (saturatedHartogsPosetName P R ∅ γ δ)) :=
  sparsePairCarrier_rank_lower hsp ht.1 (normalizedHartogsPool_rank_cofinal hR ht hδ hP hγ h1)

end ZFVP
