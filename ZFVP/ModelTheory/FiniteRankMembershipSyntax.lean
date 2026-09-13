import ZFVP.ModelTheory.EndExtensionOpenModels
import ZFVP.ModelTheory.EmbeddingCodeFixation
import ZFVP.ModelTheory.LimitRankEmbeddingAction
import ZFVP.Syntax.SigmaOneMembershipFamily
import ZFVP.SetTheory.CorrectDomainReflection
import ZFVP.SetTheory.ChoicelessInaccessibleRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem inaccessible_membershipFormulaFamily_mem {η : V} (hη : IsChoicelessInaccessible η) :
    (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy η := by
  let := hη.1
  let := hierarchy_transitive η
  let := rankDomain_nonempty hη.2.1
  let := hη.rankCriterion.models_zf
  exact transitiveZF_membershipFormulaFamily_mem (hierarchy η)

theorem inaccessible_membershipFamily_witness {η : V} (hη : IsChoicelessInaccessible η) :
    membershipFamilyWitnessFormula.Evalb
      ![hierarchy η, (formulaFamily membershipLanguageCode ∅ : V)] := by
  let := hη.1
  let := hierarchy_isSequenceSupport hη.2.1 hη.rankCriterion.2.2.1
  have hF := inaccessible_membershipFormulaFamily_mem hη
  have hs : identity (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy η := by
    apply subset_mem_hierarchy_limit hη.rankCriterion.2.2.1
      (prod_mem_hierarchy_limit hη.rankCriterion.2.2.1 hF hF)
    intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_identity_iff.mp hz
    exact kpair_mem_iff.mpr ⟨hx, hx⟩
  have ht := (eval_membershipFixedPointFormula hF hs).mpr rfl
  simpa [membershipFamilyWitnessFormula, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def] using
    And.intro (inferInstance : IsCodingSupport (hierarchy η))
      (And.intro hF (And.intro (IsCodingSupport.omega_mem (U := hierarchy η)) (And.intro hs ht)))

theorem finiteRankEmbedding_value_membershipFamily {η B f : V}
    (hη : IsChoicelessInaccessible η) [IsTransitive B]
    (he : IsCodedMembershipEmbedding (hierarchy (ordinalAdd η (ω : V))) B f) :
    f ‘ (formulaFamily membershipLanguageCode ∅ : V) = formulaFamily membershipLanguageCode ∅ := by
  let := hη.1
  let := hierarchy_transitive (ordinalAdd η (ω : V))
  have hU : hierarchy η ∈ hierarchy (ordinalAdd η (ω : V)) := hierarchy_mem (ordinalAdd_omega_gt η)
  have hF := (hierarchy_transitive _).mem_trans (inaccessible_membershipFormulaFamily_mem hη) hU
  have ht := (he.bounded_formula_iff membershipFamilyWitnessFormula_bounded
    ![hierarchy η, formulaFamily membershipLanguageCode ∅] (by simp [hU, hF])).mp
      (inaccessible_membershipFamily_witness hη)
  have hv : (fun i ↦ f ‘ (![hierarchy η, formulaFamily membershipLanguageCode ∅] i)) =
      ![f ‘ (hierarchy η), f ‘ (formulaFamily membershipLanguageCode ∅ : V)] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  rw [hv] at ht
  apply (eval_sigmaOneMembershipFamilyFormula _).mp
  exact ⟨f ‘ (hierarchy η), ht⟩

end ZFVP

