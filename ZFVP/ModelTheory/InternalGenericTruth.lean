import ZFVP.ModelTheory.GenericTruthBooleanCases
import ZFVP.ModelTheory.GenericTruthQuantifierCases
import ZFVP.Syntax.EndExtensionDefinableInduction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext

/-- Generic truth for every internal formula code and every ground sequence of names. -/
theorem groundGenericTruth (A : ForcingContext V) (D : V)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) {n φ : V} (hφ : IsMembershipFormulaCode n φ) :
    A.GroundGenericTruth D hD n φ := by
  apply A.checkEmbedding.membershipFormula_induction_via (A.GroundGenericTruth D hD)
    (InternalGenericTruthAt (range (A.evaluationGraph D hD)) (A.sequenceEvaluationGraph D hD)
      (A.check (finiteSequences D)) A.genericSet (A.check (internalForcingTruthTable A.P A.R D)))
    (by infer_instance) ?_ (fun _ hn ↦ A.groundGenericTruth_constants D hD hn)
    (fun _ hn _ _ ha ↦ A.groundGenericTruth_atoms D hD hn ha)
    ?_ ?_ n φ hφ
  · intro n φ hφ
    exact A.internalGenericTruthAt_checked D hD _ hφ
  · intro n _ φ ψ hφ hψ ihφ ihψ
    exact A.groundGenericTruth_binary D hD hφ hψ ihφ ihψ
  · intro n hn φ hφ ihφ
    exact A.groundGenericTruth_quantifiers D hD hn hφ ihφ

theorem lowRank_internalGenericTruth (A : ForcingContext V) {δ n φ b : V}
    (hδ : Cn 1 δ) (hP : A.P ∈ hierarchy δ) (hφ : IsMembershipFormulaCode n φ)
    (hb : b ∈ lowRankNameSet A.P δ ^ n) :
    MembershipSatisfies (hierarchy (A.check δ)) (A.check n) (A.check φ)
      (A.sequenceValue b (A.nameSequence_of_mem_function (A.lowRankNameSet_names δ) hb)) ↔
        GenericMeets A.G (internalForcingSet A.P A.R (lowRankNameSet A.P δ) n φ b) := by
  have hh := A.groundGenericTruth (lowRankNameSet A.P δ) (A.lowRankNameSet_names δ) hφ b hb
  rwa [A.lowRankEvaluation_range hδ hP] at hh

end ForcingContext
end ZFVP
