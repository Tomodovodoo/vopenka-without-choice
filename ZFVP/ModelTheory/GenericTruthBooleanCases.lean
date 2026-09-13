import ZFVP.ModelTheory.GenericTruthBaseCases
import ZFVP.ModelTheory.CodedSequentSemantics

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext

theorem groundGenericTruth_binary (A : ForcingContext V) (D : V)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) {n φ ψ : V}
    (hφ : IsMembershipFormulaCode n φ) (hψ : IsMembershipFormulaCode n ψ)
    (ihφ : A.GroundGenericTruth D hD n φ) (ihψ : A.GroundGenericTruth D hD n ψ) :
    A.GroundGenericTruth D hD n (andCode φ ψ) ∧ A.GroundGenericTruth D hD n (orCode φ ψ) := by
  have hφ' : IsMembershipFormulaCode (A.check n) (A.check φ) :=
    (A.checkEmbedding.membershipFormulaCode_iff n φ).mpr hφ
  have hψ' : IsMembershipFormulaCode (A.check n) (A.check ψ) :=
    (A.checkEmbedding.membershipFormulaCode_iff n ψ).mpr hψ
  constructor
  · intro b hb
    have ht : A.check (andCode φ ψ) = andCode (A.check φ) (A.check ψ) := A.checkEmbedding.map_andCode φ ψ
    rw [ht, membershipSatisfies_and hφ'.context hφ'.valid hψ'.valid (A.sequenceValue_mem_evaluationRange hD hb),
      genericMeets_internalForcing_and A.order A.generic hφ hψ hb]
    exact and_congr (ihφ b hb) (ihψ b hb)
  · intro b hb
    have ht : A.check (orCode φ ψ) = orCode (A.check φ) (A.check ψ) := A.checkEmbedding.map_orCode φ ψ
    rw [ht, membershipSatisfies_or hφ'.context hφ'.valid hψ'.valid (A.sequenceValue_mem_evaluationRange hD hb),
      genericMeets_internalForcing_or A.order A.generic hφ hψ hb]
    exact or_congr (ihφ b hb) (ihψ b hb)

end ForcingContext
end ZFVP
