import ZFVP.ModelTheory.ForcingNameRankLower
import ZFVP.ModelTheory.SparseNormalizedTwoStep
import ZFVP.ModelTheory.TransitiveZFNames
import ZFVP.SetTheory.ChoicelessInaccessibleRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsChoicelessInaccessible.checkName_mem_hierarchy {δ one x : V}
    (hδ : IsChoicelessInaccessible δ) (ho : one ∈ hierarchy δ) (hx : x ∈ hierarchy δ) :
    checkName one x ∈ hierarchy δ := by
  let := hδ.1
  let := hierarchy_transitive δ
  let := rankDomain_nonempty hδ.2.1
  let := hδ.rankCriterion.models_zf
  let o : SetDomain (hierarchy δ) := ⟨one, ho⟩
  let y : SetDomain (hierarchy δ) := ⟨x, hx⟩
  exact (TransitiveZF.checkName_val (hierarchy δ) o y) ▸ (checkName o y).property

theorem normalizedNamePool_check_representative {P R one δ U x : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hx : x ∈ hierarchy δ)
    (hm : one ∈ atomicMembership P R (checkName one x) U) :
    ∃ τ ∈ normalizedNamePool P R one δ U,
      one ∈ atomicEquality P R τ (checkName one x) ∧ rank x ⊆ rank τ := by
  let := hδ.1
  let ν := checkName one x
  let τ := forcingLeastRankName P R one ν
  have hn : IsForcingName P ν := checkName_isName ht.1 x
  have hτN : IsForcingName P τ := forcingLeastRankName_isName hR ht.1 hn
  have he : one ∈ atomicEquality P R ν τ := forcingLeastRankName_forced_equal hR ht.1 hn
  have he' : one ∈ atomicEquality P R τ ν := (atomicEquality_symm P R ν τ) ▸ he
  have hν : ν ∈ hierarchy δ := hδ.checkName_mem_hierarchy ((hierarchy_transitive δ).mem_trans ht.1 hP) hx
  have hτ : τ ∈ hierarchy δ := by
    apply forcingLeastRankName_mem_hierarchy_of_equiv hR ht.1 hn hn ?_ hν
    rw [atomicEquality_refl hR]
    exact ht.1
  refine ⟨τ, mem_sep_iff.mpr ⟨hτ, hτN, forcingLeastRankName_idempotent hR ht.1 hn, ?_⟩,
    he', forcingName_rank_lower_of_check hR ht ht.1 hτN he'⟩
  exact atomicMembership_subst_left hR he hm

theorem normalizedNamePool_rank_cofinal {P R one δ U : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (hw : ∀ β ∈ δ, ∃ x ∈ hierarchy δ, β ∈ rank x ∧
      one ∈ atomicMembership P R (checkName one x) U) :
    ∀ β ∈ δ, ∃ τ ∈ normalizedNamePool P R one δ U, β ∈ rank τ := by
  intro β hβ
  obtain ⟨x, hx, hβx, hm⟩ := hw β hβ
  obtain ⟨τ, hτ, _, hb⟩ := normalizedNamePool_check_representative hR ht hδ hP hx hm
  exact ⟨τ, hτ, hb β hβx⟩

theorem sparsePairCarrier_rank_lower {a P W δ : V}
    (hP : ∀ p ∈ P, IsSparseFunctionOn a p) (h0 : (∅ : V) ∈ P)
    (hW : ∀ β ∈ δ, ∃ τ ∈ W, β ∈ rank τ) :
    δ ⊆ rank (sparsePairCarrier a P W) := by
  intro β hβ
  obtain ⟨τ, hτ, hβτ⟩ := hW β hβ
  have hn : τ ≠ ∅ := by
    intro he
    rw [he, rank_empty] at hβτ
    exact not_mem_empty hβτ
  have hq := sparseAppend_mem_pairCarrier hP h0 hτ
  have hv := subset_hierarchy_rank (sparsePairCarrier a P W) _ hq
  have hh : ⟨a, τ⟩ₖ ∈ sparseAppend a ∅ τ := by rw [sparseAppend_nonempty hn]; simp
  let := hierarchy_transitive (rank (sparsePairCarrier a P W))
  have hτv := (kpair_components_mem_transitive ((hierarchy_transitive (rank (sparsePairCarrier a P W))).mem_trans hh hv)).2
  exact IsOrdinal.toIsTransitive.mem_trans hβτ ((mem_hierarchy_iff_rank_mem _ _).mp hτv)

theorem sparseNormalizedTwoStep_rank_lower {a P R δ U : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R ∅)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (hsp : ∀ p ∈ P, IsSparseFunctionOn a p)
    (hw : ∀ β ∈ δ, ∃ x ∈ hierarchy δ, β ∈ rank x ∧
      (∅ : V) ∈ atomicMembership P R (checkName ∅ x) U) :
    δ ⊆ rank (sparseNormalizedTwoStep a P R ∅ δ U) :=
  sparsePairCarrier_rank_lower hsp ht.1 (normalizedNamePool_rank_cofinal hR ht hδ hP hw)

end ZFVP


