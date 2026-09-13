import ZFVP.ModelTheory.FiniteRankLiftAssignments

import ZFVP.ModelTheory.InternalGenericTruth
import ZFVP.Syntax.EndExtensionMembershipNegation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace FiniteRankLiftData
variable {A B : ForcingContext V} {δ ε e : V} (L : FiniteRankLiftData A B δ ε e)

include L

theorem internal_formula_forward {n φ b : V} (hφ : IsMembershipFormulaCode n φ)
    (hb : b ∈ lowRankNameSet A.P δ ^ n)
    (ht : MembershipSatisfies (hierarchy (A.check δ)) (A.check n) (A.check φ)
      (A.sequenceValue b (A.nameSequence_of_mem_function (A.lowRankNameSet_names δ) hb))) :
    MembershipSatisfies (hierarchy (B.check ε)) (B.check n) (B.check φ)
      (B.sequenceValue (e ‘ b) (B.nameSequence_of_mem_function (B.lowRankNameSet_names ε) (L.image_assignment hφ.context hb))) := by
  let := L.source_inaccessible.1
  let := L.target_inaccessible.1
  obtain ⟨p, hp, hf⟩ := (A.lowRank_internalGenericTruth_of_coverage L.source_coverage hφ hb).mp ht
  have hpP := A.generic.1.1 p hp
  have hi := (finiteRankEmbedding_lowInternalForces_sameCode L.source_inaccessible L.target_inaccessible
    L.embedding L.height_image L.poset_subset L.relation_mem hφ hb hpP).mp ((mem_internalForcingSet hφ).mp hf)
  rw [L.poset_image, L.relation_image] at hi
  apply (B.lowRank_internalGenericTruth_of_coverage L.target_coverage hφ (L.image_assignment hφ.context hb)).mpr
  exact ⟨e ‘ p, L.generic p hp, (mem_internalForcingSet hφ).mpr hi⟩

theorem internal_formula_iff {n φ b : V} (hφ : IsMembershipFormulaCode n φ)
    (hb : b ∈ lowRankNameSet A.P δ ^ n) :
    MembershipSatisfies (hierarchy (A.check δ)) (A.check n) (A.check φ)
      (A.sequenceValue b (A.nameSequence_of_mem_function (A.lowRankNameSet_names δ) hb)) ↔
    MembershipSatisfies (hierarchy (B.check ε)) (B.check n) (B.check φ)
      (B.sequenceValue (e ‘ b) (B.nameSequence_of_mem_function (B.lowRankNameSet_names ε) (L.image_assignment hφ.context hb))) := by
  let := L.source_inaccessible.1
  let := L.target_inaccessible.1
  classical
  constructor
  · exact L.internal_formula_forward hφ hb
  · intro ht
    by_contra hs
    let ψ := negateFormula membershipLanguageCode ∅ n φ
    have hψ : IsMembershipFormulaCode n ψ := (mem_formulaSet_iff _ _ _ _).mp
      (negateFormula_mem membershipLanguageCode_valid hφ.valid)
    have negA : A.check ψ = negateFormula membershipLanguageCode ∅ (A.check n) (A.check φ) :=
      A.checkEmbedding.map_membershipNegation hφ
    have negB : B.check ψ = negateFormula membershipLanguageCode ∅ (B.check n) (B.check φ) :=
      B.checkEmbedding.map_membershipNegation hφ
    have hbA := A.sequenceValue_mem_evaluationRange (A.lowRankNameSet_names δ) hb
    rw [A.lowRankEvaluation_range_of_coverage L.source_coverage] at hbA
    have hbB := B.sequenceValue_mem_evaluationRange (B.lowRankNameSet_names ε) (L.image_assignment hφ.context hb)
    rw [B.lowRankEvaluation_range_of_coverage L.target_coverage] at hbB
    have hnot : MembershipSatisfies (hierarchy (A.check δ)) (A.check n) (A.check ψ)
        (A.sequenceValue b (A.nameSequence_of_mem_function (A.lowRankNameSet_names δ) hb)) := by
      rw [negA]
      exact (membershipSatisfies_negate ((A.checkEmbedding.membershipFormulaCode_iff n φ).mpr hφ).valid hbA).mpr hs
    have hi := L.internal_formula_forward hψ hb hnot
    rw [negB] at hi
    exact (membershipSatisfies_negate ((B.checkEmbedding.membershipFormulaCode_iff n φ).mpr hφ).valid hbB).mp hi ht

end FiniteRankLiftData
end ZFVP



