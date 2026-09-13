import ZFVP.ModelTheory.FiniteRankLiftAssignmentCoverage
import ZFVP.Syntax.EndExtensionMembershipSatisfaction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace FiniteRankLiftData
variable {A B : ForcingContext V} {δ ε e π : V} (L : FiniteRankLiftData A B δ ε e)
  (hπ : IsForcingRetraction A.P A.R B.P B.R π)
  (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P) (hone : A.one = B.one)

include hG hone in
theorem graph_internal_formula_iff {n φ : V} (hφ : IsMembershipFormulaCode n φ) {b : B.Model}
    (hb : b ∈ domain (L.graph hπ) ^ B.check n) :
    MembershipSatisfies (domain (L.graph hπ)) (B.check n) (B.check φ) b ↔
      MembershipSatisfies (hierarchy (B.check ε)) (B.check n) (B.check φ) (compose b (L.graph hπ)) := by
  obtain ⟨s, hs, rfl⟩ := L.graph_assignment_representative hπ hG hone hφ.context hb
  let j := ForcingContext.retractionEmbedding A B hπ hG
  let hsN := A.nameSequence_of_mem_function (A.lowRankNameSet_names δ) hs
  have hjn : j (A.check n) = B.check n := ForcingContext.retractionInclusion_check A B hπ hG hone n
  have hjφ : j (A.check φ) = B.check φ := ForcingContext.retractionInclusion_check A B hπ hG hone φ
  have hjs : j (A.sequenceValue s hsN) = B.sequenceValue s (fun i hi ↦ (hsN i hi).mono hπ.inclusion) :=
    ForcingContext.retractionInclusion_sequenceValue A B hπ hG hone s hsN
  have hh := j.membershipSatisfies_iff (hierarchy (A.check δ)) (A.check n) (A.check φ) (A.sequenceValue s hsN)
  rw [hjn, hjφ, hjs] at hh
  have hd : j (hierarchy (A.check δ)) = domain (L.graph hπ) := (L.graph_domain_eq_rank_image hπ hG).symm
  rw [hd] at hh
  rw [L.graph_compose_sequence hπ hG hφ.context hs]
  exact hh.trans (L.internal_formula_iff hφ hs)

include hG hone in
/-- The lift is elementary for every formula and assignment internal to the larger generic quotient. -/
theorem graph_codedElementary :
    IsCodedMembershipEmbedding (domain (L.graph hπ)) (hierarchy (B.check ε)) (L.graph hπ) := by
  let := L.source_inaccessible.1
  let : IsSequenceSupport (hierarchy δ) := hierarchy_isSequenceSupport L.source_inaccessible.2.1 L.source_inaccessible.rankCriterion.2.2.1
  have h0 : (∅ : V) ∈ hierarchy δ := IsCodingSupport.empty_mem
  let τ : ForcingName A.P := ⟨∅, empty_forcingName A.P⟩
  have hx : B.ofName ⟨τ.val, τ.property.mono hπ.inclusion⟩ ∈ domain (L.graph hπ) :=
    (L.graph_domain hπ _).mpr ⟨τ, h0, rfl⟩
  have hsrc : IsNonempty (domain (L.graph hπ)) := ⟨_, hx⟩
  have htgt : IsNonempty (hierarchy (B.check ε)) := ⟨_, L.graph_value_mem_rank hπ hG hx⟩
  refine ⟨membershipStructureCode_valid hsrc, membershipStructureCode_valid htgt, ?_, ?_⟩
  · simpa only [membershipStructureCode_domain, L.graph_domain_eq_rank_image hπ hG] using L.graph_rank_function hπ hG
  · intro m hm φ hφ b hb
    have hc : IsMembershipFormulaCode m φ := (mem_formulaSet_iff _ _ _ _).mp hφ
    obtain ⟨n, ψ, hn, hψ, hground⟩ := B.checkEmbedding.membershipFormulaCode_preimages hc
    change m = B.check n at hn
    change φ = B.check ψ at hψ
    subst m φ
    have hb' : b ∈ domain (L.graph hπ) ^ B.check n := by simpa only [membershipStructureCode_domain] using hb
    exact L.graph_internal_formula_iff hπ hG hone hground hb'

end FiniteRankLiftData
end ZFVP

