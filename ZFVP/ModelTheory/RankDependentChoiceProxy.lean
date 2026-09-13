import ZFVP.ModelTheory.SuccessorRankFunctionClosure
import ZFVP.SetTheory.BoundedStarDependentChoice
import ZFVP.ModelTheory.SuccessorRankElementaryLift
import ZFVP.ModelTheory.SuccessorRankLiftTruth
import ZFVP.ModelTheory.ForcingCnOneTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def rankDCGuardFormula : SetTheorySemisentence 3 :=
  “κ D B. κ ∈ B ∧ D ∈ B ∧ !IsTransitive.dfn B ∧ !functionRestrictionClosedFormula B →
    ¬!boundedDependentChoiceFailureFormula κ B”

theorem rankDCGuardFormula_bounded : IsBoundedSetFormula rankDCGuardFormula :=
  .or (IsBoundedSetFormula.and (.rel _ _) (.and (.rel _ _) (.and (isTransitiveFormula_bounded.subst _)
    (functionRestrictionClosedFormula_bounded.subst _)))).neg
    (boundedDependentChoiceFailureFormula_bounded.subst _).neg

def rankDCProxyFormula : SetTheorySemisentence 2 :=
  “κ D. ∀ B, !piOneFunctionClosedFormula D B → !rankDCGuardFormula κ D B”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_rankDCGuardFormula (κ D B : V) :
    rankDCGuardFormula.Evalb ![κ, D, B] ↔
      (κ ∈ B → D ∈ B → IsTransitive B → IsFunctionRestrictionClosed B →
        ¬IsBoundedDependentChoiceFailure κ B) := by
  simp [rankDCGuardFormula]

theorem rankDCProxy_rank_iff {γ : V} (hγ : Cn 1 γ)
    (κ D : SetDomain (hierarchy γ)) :
    rankDCProxyFormula.Evalb ![κ, D] ↔
      boundedStarDCFormula.Evalb ![κ.val, D.val, hierarchy γ] := by
  let := hγ.ordinal
  let := hierarchy_transitive γ
  have he : rankDCProxyFormula.Evalb ![κ, D] ↔
      ∀ B : SetDomain (hierarchy γ), B.val ^ D.val ⊆ B.val →
        κ.val ∈ B.val → D.val ∈ B.val → IsTransitive B.val →
          IsFunctionRestrictionClosed B.val → ¬IsBoundedDependentChoiceFailure κ.val B.val := by
    simp only [rankDCProxyFormula]
    simp only [Semiformula.eval_all]
    apply forall_congr'
    intro B
    simp [Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
    have hc := hγ.pi_correct piOneFunctionClosedFormula_piOne ![D, B]
    have hg := bounded_formula_absolute (hierarchy γ) rankDCGuardFormula_bounded ![κ, D, B]
    have hcv : (fun i ↦ (![D, B] i).val) = ![D.val, B.val] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    have hgv : (fun i ↦ (![κ, D, B] i).val) = ![κ.val, D.val, B.val] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl
        (fun k ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) k) j) i
    rw [hcv] at hc
    rw [hgv] at hg
    rw [hc, hg, eval_rankDCGuardFormula]
    exact imp_congr (piOneFunctionClosedFormula_defined.iff _) Iff.rfl
  rw [he, eval_boundedStarDCFormula]
  constructor
  · intro h B hB hc
    exact h ⟨B, hB⟩ ((boundedFunctionClosed_rank_iff hγ D.property hB).mp hc)
  · intro h B hc
    exact h B.val B.property ((boundedFunctionClosed_rank_iff hγ D.property B.property).mpr hc)

theorem rankEmbedding_DCProxy_iff {ρ γ e κ D : V} (hρ : Cn 1 ρ) (hγ : Cn 1 γ)
    (he : IsCodedMembershipEmbedding (hierarchy ρ) (hierarchy γ) e)
    (hκ : κ ∈ hierarchy ρ) (hD : D ∈ hierarchy ρ) :
    boundedStarDCFormula.Evalb ![κ, D, hierarchy ρ] ↔
      boundedStarDCFormula.Evalb ![e ‘ κ, e ‘ D, hierarchy γ] := by
  let k : SetDomain (hierarchy ρ) := ⟨κ, hκ⟩
  let d : SetDomain (hierarchy ρ) := ⟨D, hD⟩
  have hh := he.eval_semisentence rankDCProxyFormula ![k, d]
  have hv : he.toFunction ∘ ![k, d] = ![he.toFunction k, he.toFunction d] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) j) i
  rw [hv] at hh
  exact (rankDCProxy_rank_iff hρ k d).symm.trans
    (hh.trans (rankDCProxy_rank_iff hγ (he.toFunction k) (he.toFunction d)))

theorem SuccessorRankLiftData.rankDCProxy_iff {A B : ForcingContext V} {δ ε e : V}
    (L : SuccessorRankLiftData A B δ ε e) (κ D : SetDomain (hierarchy (A.check δ))) :
    boundedStarDCFormula.Evalb ![κ.val, D.val, hierarchy (A.check δ)] ↔
      boundedStarDCFormula.Evalb
        ![(L.rankLiftFun κ).val, (L.rankLiftFun D).val, hierarchy (B.check ε)] := by
  have hs := A.cn_one_check L.source_correct L.poset_mem
  have ht := B.cn_one_check L.target_correct L.target_poset_mem
  have hh := L.rankLiftFun_formula_iff rankDCProxyFormula ![κ, D]
  have hv : L.rankLiftFun ∘ ![κ, D] = ![L.rankLiftFun κ, L.rankLiftFun D] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) j) i
  rw [hv] at hh
  exact (rankDCProxy_rank_iff hs κ D).symm.trans
    (hh.trans (rankDCProxy_rank_iff ht (L.rankLiftFun κ) (L.rankLiftFun D)))

end ZFVP
