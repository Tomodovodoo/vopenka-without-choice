import ZFVP.ModelTheory.SuccessorRankLift
import ZFVP.ModelTheory.SuccessorRankNameAssignments
import ZFVP.ModelTheory.SuccessorRankCodeFixation
import ZFVP.ModelTheory.InternalGenericTruth
import ZFVP.Syntax.EndExtensionMembershipNegation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace SuccessorRankLiftData
variable {A B : ForcingContext V} {δ ε e : V} (L : SuccessorRankLiftData A B δ ε e)

include L

theorem target_poset_mem : B.P ∈ hierarchy ε := by
  let := L.source_correct.ordinal
  let := L.target_correct.ordinal
  rw [← L.poset_image]
  exact (successorRankElementaryMap L.embedding ⟨A.P, L.poset_mem⟩).property

theorem image_assignment {n b : V} (hn : n ∈ (ω : V)) (hb : b ∈ lowRankNameSet A.P δ ^ n) :
    e ‘ b ∈ lowRankNameSet B.P ε ^ n := by
  have hh := (successorRankEmbedding_nameAssignment L.source_correct L.target_correct L.embedding L.poset_mem hn hb).1
  rwa [L.poset_image] at hh

theorem internal_formula_forward {n φ b : V} (hφ : IsMembershipFormulaCode n φ)
    (hb : b ∈ lowRankNameSet A.P δ ^ n)
    (ht : MembershipSatisfies (hierarchy (A.check δ)) (A.check n) (A.check φ)
      (A.sequenceValue b (A.nameSequence_of_mem_function (A.lowRankNameSet_names δ) hb))) :
    MembershipSatisfies (hierarchy (B.check ε)) (B.check n) (B.check φ)
      (B.sequenceValue (e ‘ b) (B.nameSequence_of_mem_function (B.lowRankNameSet_names ε) (L.image_assignment hφ.context hb))) := by
  obtain ⟨p, hp, hf⟩ := (A.lowRank_internalGenericTruth L.source_correct L.poset_mem hφ hb).mp ht
  have hpP := A.generic.1.1 p hp
  have hi := (successorRankEmbedding_lowInternalForces_sameCode L.source_correct L.target_correct
    L.embedding L.poset_mem L.relation_mem hφ hb hpP).mp ((mem_internalForcingSet hφ).mp hf)
  rw [L.poset_image, L.relation_image] at hi
  apply (B.lowRank_internalGenericTruth L.target_correct L.target_poset_mem hφ (L.image_assignment hφ.context hb)).mpr
  exact ⟨e ‘ p, L.generic p hp, (mem_internalForcingSet hφ).mpr hi⟩

theorem internal_formula_iff {n φ b : V} (hφ : IsMembershipFormulaCode n φ)
    (hb : b ∈ lowRankNameSet A.P δ ^ n) :
    MembershipSatisfies (hierarchy (A.check δ)) (A.check n) (A.check φ)
      (A.sequenceValue b (A.nameSequence_of_mem_function (A.lowRankNameSet_names δ) hb)) ↔
    MembershipSatisfies (hierarchy (B.check ε)) (B.check n) (B.check φ)
      (B.sequenceValue (e ‘ b) (B.nameSequence_of_mem_function (B.lowRankNameSet_names ε) (L.image_assignment hφ.context hb))) := by
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
    rw [A.lowRankEvaluation_range L.source_correct L.poset_mem] at hbA
    have hbB := B.sequenceValue_mem_evaluationRange (B.lowRankNameSet_names ε) (L.image_assignment hφ.context hb)
    rw [B.lowRankEvaluation_range L.target_correct L.target_poset_mem] at hbB
    have hnot : MembershipSatisfies (hierarchy (A.check δ)) (A.check n) (A.check ψ)
        (A.sequenceValue b (A.nameSequence_of_mem_function (A.lowRankNameSet_names δ) hb)) := by
      rw [negA]
      exact (membershipSatisfies_negate ((A.checkEmbedding.membershipFormulaCode_iff n φ).mpr hφ).valid hbA).mpr hs
    have hi := L.internal_formula_forward hψ hb hnot
    rw [negB] at hi
    exact (membershipSatisfies_negate ((B.checkEmbedding.membershipFormulaCode_iff n φ).mpr hφ).valid hbB).mp hi ht

end SuccessorRankLiftData
end ZFVP
