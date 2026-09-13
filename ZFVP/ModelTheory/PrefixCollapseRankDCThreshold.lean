import ZFVP.ModelTheory.BoundedPrefixCollapseName
import ZFVP.ModelTheory.TwoStepRankDCThreshold
import ZFVP.SetTheory.WoodinSupercompactStarCorrect

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.prefixCollapse_name_height {δ P κ γ : V}
    (hδ : IsWoodinSupercompact δ) (hP : P ∈ hierarchy δ) (hκ : κ ∈ δ) (hγ : γ ∈ δ) :
    ∃ θ ∈ δ, Cn 1 θ ∧ P ∈ hierarchy θ ∧ κ ∈ θ ∧ γ ∈ θ := by
  let := hδ.1.1
  let := IsOrdinal.of_mem hκ
  let := IsOrdinal.of_mem hγ
  let := ordinal_union_ordinal κ γ
  let := ordinal_union_ordinal (rank P) (κ ∪ γ)
  obtain ⟨θ, hθ, hh, hc⟩ := hδ.starCorrect_cofinal
    (ordinal_union_mem ((mem_hierarchy_iff_rank_mem _ _).mp hP) (ordinal_union_mem hκ hγ))
  let := hc.1.ordinal
  have hrθ : rank P ∈ θ := ordinal_mem_of_subset_mem (subset_union_left _ _) hh
  have hkγ : κ ∪ γ ∈ θ := ordinal_mem_of_subset_mem (subset_union_right _ _) hh
  exact ⟨θ, hθ, hc.1, (mem_hierarchy_iff_rank_mem _ _).mpr hrθ,
    ordinal_mem_of_subset_mem (subset_union_left _ _) hkγ,
    ordinal_mem_of_subset_mem (subset_union_right _ _) hkγ⟩

theorem uniform_prefixCollapse_rankDCThreshold {δ P R one κ γ θ : V}
    (hδ : IsWoodinSupercompact δ) (hP : P ∈ hierarchy δ) (hθδ : θ ∈ δ)
    (hγδ : γ ∈ δ) (hθ : Cn 1 θ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![checkName one κ])) :
    letI := hδ.1.1
    letI := IsOrdinal.of_mem hγδ
    letI := hθ.ordinal
    let h := boundedPrefixCollapse_iterand (κ := κ) (γ := γ) hR ht
      (IsOrdinal.toIsTransitive.mem_trans (show (∅ : V) ∈ ω by simp) hθ.omega_lt) hκ
    ∃ β ∈ δ, γ ∈ β ∧ ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G),
      let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
      ∀ (H : Set A.Model) (hH : IsExternalForcingGeneric
          (A.ofName ⟨boundedPrefixCollapseName P R one κ γ θ, h.posetName⟩)
          (A.ofName ⟨reverseInclusionOrderName P R
            (boundedPrefixCollapseName P R one κ γ θ), h.orderName⟩) H),
        IsRankDCThreshold ((TwoStepModel.iterandContext A h hH).check (A.check γ))
          ((TwoStepModel.iterandContext A h hH).check (A.check β)) := by
  let := hδ.1.1
  let := IsOrdinal.of_mem hγδ
  let := hθ.ordinal
  exact uniform_twoStep_rankDCThreshold hδ
    (boundedPrefixCollapse_twoStep_small hδ.inaccessible hP hθδ) hγδ hR ht _

end ZFVP
