import ZFVP.SetTheory.BoundedStarDependentChoiceBelow
import ZFVP.ModelTheory.LimitRankEmbedding

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem successorRankEmbedding_ordinal_bounds {ρ γ e κ : V}
    (hρ : Cn 1 ρ) (hγ : Cn 1 γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e) (hκ : κ ∈ ρ) :
    IsOrdinal (e ‘ κ) ∧ e ‘ κ ∈ γ := by
  let := hρ.ordinal
  let := hγ.ordinal
  let := IsOrdinal.of_mem hκ
  have hκV : κ ∈ hierarchy ρ := ordinal_mem_hierarchy_iff.mpr hκ
  have ho := (successorRankEmbedding_value_lower_hierarchy hρ hγ he inferInstance hκV).1
  let := ho
  have hm : e ‘ κ ∈ hierarchy γ := (successorRankElementaryMap he ⟨κ, hκV⟩).property
  exact ⟨ho, ordinal_mem_hierarchy_iff.mp hm⟩

theorem successorRankEmbedding_rankProxy_iff {ρ γ e κ : V}
    (hρ : Cn 1 ρ) (hγ : Cn 1 γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e)
    (hκ : κ ∈ ρ) {φ : SetTheorySemisentence 3} (hφ : IsBoundedSetFormula φ) :
    φ.Evalb ![κ, hierarchy (succ κ), hierarchy ρ] ↔
      φ.Evalb ![e ‘ κ, hierarchy (succ (e ‘ κ)), hierarchy γ] := by
  let := hρ.ordinal
  let := hγ.ordinal
  let := IsOrdinal.of_mem hκ
  let := hierarchy_transitive (succ ρ)
  let := hierarchy_transitive (succ γ)
  have hκV : κ ∈ hierarchy ρ := ordinal_mem_hierarchy_iff.mpr hκ
  have hsκV : succ κ ∈ hierarchy ρ := ordinal_mem_hierarchy_iff.mpr (hρ.successor_closed κ hκ)
  have hD : hierarchy (succ κ) ∈ hierarchy ρ := hρ.hierarchy_closed inferInstance hsκV
  have hinc : hierarchy ρ ⊆ hierarchy (succ ρ) := hierarchy_mono
    (by intro z hz; exact mem_succ_iff.mpr (Or.inr hz))
  have hH : hierarchy ρ ∈ hierarchy (succ ρ) := by rw [hierarchy_succ, mem_power_iff]
  have heD : e ‘ (hierarchy (succ κ)) = hierarchy (succ (e ‘ κ)) := by
    rw [(successorRankEmbedding_value_lower_hierarchy hρ hγ he inferInstance hsκV).2,
      he.value_succ (hinc _ hκV) (hinc _ hsκV)]
  have hh := he.bounded_formula_iff hφ ![κ, hierarchy (succ κ), hierarchy ρ]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hinc _ hκV, hinc _ hD, hH])
  have hv : (fun i ↦ e ‘ (![κ, hierarchy (succ κ), hierarchy ρ] i)) =
      ![e ‘ κ, hierarchy (succ (e ‘ κ)), hierarchy γ] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases heD
      (fun k ↦ Fin.cases (successorRankEmbedding_value_hierarchy he) (fun l ↦ Fin.elim0 l) k) j) i
  rw [hv] at hh
  exact hh

theorem successorRankEmbedding_dependentChoice_iff {δ ρ γ e κ : V}
    (hδ : IsWoodinSupercompact δ) (hρ : IsSigmaOneStarCorrect ρ) (hγ : IsSigmaOneStarCorrect γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e) (hκ : κ ∈ ρ) :
    InternalDependentChoiceAt κ ↔ InternalDependentChoiceAt (e ‘ κ) := by
  have hκγ := (successorRankEmbedding_ordinal_bounds hρ.1 hγ.1 he hκ).2
  exact (boundedStarDC_iff hδ hρ hκ).symm.trans
    ((successorRankEmbedding_rankProxy_iff hρ.1 hγ.1 he hκ boundedStarDCFormula_bounded).trans
      (boundedStarDC_iff hδ hγ hκγ))

theorem successorRankEmbedding_dependentChoiceBelow_iff {δ ρ γ e κ : V}
    (hδ : IsWoodinSupercompact δ) (hρ : IsSigmaOneStarCorrect ρ) (hγ : IsSigmaOneStarCorrect γ)
    (he : IsCodedMembershipEmbedding (hierarchy (succ ρ)) (hierarchy (succ γ)) e) (hκ : κ ∈ ρ) :
    (∀ η ∈ κ, InternalDependentChoiceAt η) ↔ ∀ η ∈ e ‘ κ, InternalDependentChoiceAt η := by
  have hκγ := (successorRankEmbedding_ordinal_bounds hρ.1 hγ.1 he hκ).2
  exact (boundedStarDCBelow_iff hδ hρ hκ).symm.trans
    ((successorRankEmbedding_rankProxy_iff hρ.1 hγ.1 he hκ boundedStarDCBelowFormula_bounded).trans
      (boundedStarDCBelow_iff hδ hγ hκγ))

end ZFVP
