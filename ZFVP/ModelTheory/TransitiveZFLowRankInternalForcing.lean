import ZFVP.ModelTheory.SuccessorRankNameDomain
import ZFVP.ModelTheory.TransitiveZFNames
import ZFVP.ModelTheory.TransitiveZFRankOperations
import ZFVP.ModelTheory.EndExtensionOpenModels
import ZFVP.Syntax.EndExtensionInternalForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable {ξ : V} [IsOrdinal ξ]
  [Nonempty (SetDomain (hierarchy ξ))] [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Low-rank name pools computed in a rank model have exactly their ambient values. -/
theorem lowRankNameSet_val (P η : SetDomain (hierarchy ξ)) (hη : IsOrdinal η) :
    (lowRankNameSet P η).val = lowRankNameSet P.val η.val := by
  let := hierarchy_transitive ξ
  unfold lowRankNameSet
  rw [← rank_hierarchy_val η hη]
  apply sep_val (hierarchy ξ)
  intro τ _
  exact forcingName_iff (hierarchy ξ) P τ

/-- The full internal-code forcing computation over a resident prefix name pool
agrees with its ambient computation; this is not limited to bounded formula codes. -/
theorem internalForces_lowRankNameSet_iff
    (P R η n φ b p : SetDomain (hierarchy ξ)) (hη : IsOrdinal η)
    (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ lowRankNameSet P η ^ n) (hp : p ∈ P) :
    InternalForces P R (lowRankNameSet P η) n φ b p ↔
      InternalForces P.val R.val (lowRankNameSet P.val η.val) n.val φ.val b.val p.val := by
  let := hierarchy_transitive ξ
  have he := (setDomainEndExtension (hierarchy ξ)).internalForces_iff (R := R) hφ hb hp
  change InternalForces P R (lowRankNameSet P η) n φ b p ↔
    InternalForces P.val R.val (lowRankNameSet P η).val n.val φ.val b.val p.val at he
  rwa [lowRankNameSet_val P η hη] at he

end TransitiveZF
end ZFVP

