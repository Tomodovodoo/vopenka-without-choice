import ZFVP.ModelTheory.ForcingLSHullClosure
import ZFVP.ModelTheory.ForcingHullSmallCollapse

/-! Set forcing preserves an unbounded class of LS cardinals. Correct
limits of ground LS cardinals provide the name bounds for the two-hull
argument, and such limits are unbounded under the original hypothesis. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem ls_hull_of_correct_limit (A : ForcingContext V) {κ α γ : V}
    (hκ : IsLSCardinal κ) (hcorrect : Cn 1 κ)
    (hcof : ∀ ξ ∈ κ, ∃ μ ∈ κ, ξ ∈ μ ∧ IsLSCardinal μ)
    (hP : A.P ∈ hierarchy κ) [IsOrdinal α] (hκα : κ ⊆ α)
    (hγ : γ ∈ κ) (x : A.Model) :
    ∃ β : V, ∃ X : A.Model, IsOrdinal β ∧ α ⊆ β ∧
      IsElementaryInclusion X (hierarchy (A.check β)) ∧
      hierarchy (A.check γ) ⊆ X ∧ x ∈ X ∧ HasSmallTransitiveCollapse (A.check κ) X ∧
      (X ∩ hierarchy (A.check α)) ^ hierarchy (A.check γ) ⊆ X := by
  let := hκ.1.1
  let := IsOrdinal.of_mem hγ
  obtain ⟨δ, ν, hδκ, hδ, hνδ, hγν, hων, hPν, hBν⟩ :=
    A.ls_small_input_bounds hκ hcorrect hcof hP hγ
  let := hδ.1.1
  let := IsOrdinal.of_mem hνδ
  obtain ⟨τ, rfl⟩ := A.ofName_surjective x
  obtain ⟨η, hαη, hη⟩ := cn_unbounded 1 α
  let := hη.ordinal
  let := ordinal_union_ordinal η (rank τ.val)
  obtain ⟨β, hbβ, hβ⟩ := cn_unbounded 1 (η ∪ rank τ.val)
  let := hβ.ordinal
  have hηβ : η ∈ β := ordinal_mem_of_subset_mem (subset_union_left _ _) hbβ
  have hrτβ : rank τ.val ∈ β := ordinal_mem_of_subset_mem (subset_union_right _ _) hbβ
  have hαη' : α ⊆ η := IsOrdinal.toIsTransitive.transitive _ hαη
  have hκη : κ ⊆ η := subset_trans hκα hαη'
  have hηβ' : η ⊆ β := IsOrdinal.toIsTransitive.transitive _ hηβ
  have hκβ : κ ⊆ β := subset_trans hκη hηβ'
  have hνδ' : ν ⊆ δ := IsOrdinal.toIsTransitive.transitive _ hνδ
  have hδκ' : δ ⊆ κ := IsOrdinal.toIsTransitive.transitive _ hδκ
  have hνη : ν ⊆ η := subset_trans hνδ' (subset_trans hδκ' hκη)
  let D := lowRankNameSet A.P β
  let T := internalForcingTruthTable A.P A.R D
  let E := forcingNameEqualityTable A.P A.R D (lowRankNameSet A.P η)
  let q := ⟨⟨hierarchy β, D⟩ₖ, ⟨⟨T, E⟩ₖ, τ.val⟩ₖ⟩ₖ
  let χ := succ (κ ∪ (η ∪ rank q))
  let := ordinal_union_ordinal η (rank q)
  let := ordinal_union_ordinal κ (η ∪ rank q)
  have hκχ : κ ⊆ χ := subset_trans (subset_union_left _ _)
    (IsOrdinal.toIsTransitive.transitive _ (mem_succ_self (κ ∪ (η ∪ rank q))))
  have hηχ : η ∈ χ := ordinal_mem_of_subset_mem
    (subset_trans (subset_union_left η (rank q)) (subset_union_right κ (η ∪ rank q)))
    (mem_succ_self (κ ∪ (η ∪ rank q)))
  have hqχ : q ∈ hierarchy χ := (mem_hierarchy_iff_rank_mem _ _).mpr
    (ordinal_mem_of_subset_mem
      (subset_trans (subset_union_right η (rank q)) (subset_union_right κ (η ∪ rank q)))
      (mem_succ_self (κ ∪ (η ∪ rank q))))
  obtain ⟨ζ, Y, hζ, hχζ, hY, hδY, hqY, hsmall, hclosed⟩ :=
    hκ.2.2 δ hδκ χ inferInstance hκχ q hqχ
  let := hζ
  let := hierarchy_transitive ζ
  have hνY : hierarchy ν ⊆ Y := subset_trans (hierarchy_mono hνδ') hδY
  have hlow : hierarchy (succ (ω : V)) ⊆ Y := subset_trans (hierarchy_mono hων) hνY
  have hzero : (∅ : V) ∈ Y := hlow ∅ (by simp [hierarchy_succ])
  have hqparts := hY.kpair_components_mem hqY
  have hVD := hY.kpair_components_mem hqparts.1
  have hTEτ := hY.kpair_components_mem hqparts.2
  have hTE := hY.kpair_components_mem hTEτ.1
  have hPY : A.P ⊆ Y := subset_trans hPν hνY
  have hPβ : A.P ∈ hierarchy β := hierarchy_mono hκβ _ hP
  have hPη : A.P ∈ hierarchy η := hierarchy_mono hκη _ hP
  obtain ⟨he, hsmall'⟩ := A.lowRank_hullImage_elementary_small hκ.weaklyLSCardinal hP
    hβ hY hlow hVD.1 hVD.2 hPβ hPY hTE.1 hsmall
  have hBD : forcingNameHierarchy A.P γ ⊆ D := by
    intro σ hσ
    exact (mem_lowRankNameSet A.P β σ).mpr
      ⟨hierarchy_mono (subset_trans hνη hηβ') σ (hBν σ hσ),
        forcingNameHierarchy_names A.P γ σ hσ⟩
  have hinput := A.hullImage_contains_evaluation (forcingNameHierarchy_names A.P γ)
    (A.lowRankNameSet_names β) (subset_trans hBν hνY) hBD
  rw [A.lsInputNameEvaluation_range γ] at hinput
  have hx : A.ofName τ ∈ A.hullImage D (A.lowRankNameSet_names β) Y :=
    (A.mem_hullImage_iff D (A.lowRankNameSet_names β) Y _).mpr
      ⟨τ.val, mem_inter_iff.mpr ⟨hTEτ.2,
        (mem_lowRankNameSet A.P β τ.val).mpr
          ⟨(mem_hierarchy_iff_rank_mem _ _).mpr hrτβ, τ.property⟩⟩, rfl⟩
  have hηχ' : η ⊆ χ := IsOrdinal.toIsTransitive.transitive _ hηχ
  have hηζ : succ η ⊆ ζ := subset_trans (by
    intro z hz
    rcases mem_succ_iff.mp hz with rfl | hz
    · exact hηχ
    · exact IsOrdinal.toIsTransitive.mem_trans hz hηχ) hχζ
  have hclosedη : (Y ∩ hierarchy η) ^ hierarchy δ ⊆ Y := by
    intro f hf
    apply hclosed
    apply mem_function_of_mem_function_of_subset hf
    intro y hy
    exact mem_inter_iff.mpr ⟨(mem_inter_iff.mp hy).1,
      hierarchy_mono hηχ' y (mem_inter_iff.mp hy).2⟩
  exact ⟨β, A.hullImage D (A.lowRankNameSet_names β) Y, hβ.ordinal,
    subset_trans hαη' hηβ', he, hinput, hx, hsmall',
    A.lowRank_hullImage_closed hY hβ hη hηβ hηζ hαη' hδ.weaklyLSCardinal
      hclosedη hzero hνδ hνη hνY hBν hPν hPη hTE.2⟩

theorem check_ls_of_correct_limit (A : ForcingContext V) {κ : V}
    (hκ : IsLSCardinal κ) (hcorrect : Cn 1 κ)
    (hcof : ∀ ξ ∈ κ, ∃ μ ∈ κ, ξ ∈ μ ∧ IsLSCardinal μ)
    (hP : A.P ∈ hierarchy κ) : IsLSCardinal (A.check κ) := by
  let := hκ.1.1
  refine ⟨A.check_initial_of_weaklyLS hκ.weaklyLSCardinal hP, ?_, ?_⟩
  · have hh := (A.check_mem_iff (ω : V) κ).mpr hκ.2.1
    change A.checkEmbedding (ω : V) ∈ A.check κ at hh
    rwa [A.checkEmbedding.map_omega] at hh
  intro γ hγ α hα hκα x _hx
  let := hα
  obtain ⟨g, hg, rfl⟩ := (A.mem_check_iff κ γ).mp hγ
  obtain ⟨a, ha, rfl⟩ := A.ordinal_eq_check α
  let := ha
  obtain ⟨b, X, hb, hab, he, hgX, hxX, hsmall, hclosed⟩ :=
    A.ls_hull_of_correct_limit hκ hcorrect hcof hP
      ((A.checkEmbedding.subset_iff κ a).mp hκα) hg x
  let := hb
  exact ⟨A.check b, X, inferInstance, (A.checkEmbedding.subset_iff a b).mpr hab,
    he, hgX, hxX, hsmall, hclosed⟩

theorem unbounded_ls_preserved (A : ForcingContext V)
    (hLS : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ) :
    ∀ α : A.Model, IsOrdinal α → ∃ κ : A.Model, α ∈ κ ∧ IsLSCardinal κ := by
  intro α hα
  let := hα
  obtain ⟨a, ha, rfl⟩ := A.ordinal_eq_check α
  let := ha
  obtain ⟨κ, haκ, hκ, hc, hP, hcof⟩ := A.exists_rank_small_correct_ls_limit hLS a
  exact ⟨A.check κ, (A.check_mem_iff a κ).mpr haκ,
    A.check_ls_of_correct_limit hκ hc hcof hP⟩

end ForcingContext
end ZFVP
