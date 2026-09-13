import ZFVP.ModelTheory.FiniteRankLiftElementarity
import ZFVP.ModelTheory.EndExtensionCodedMembershipEmbedding

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace FiniteRankLiftData
variable {A B : ForcingContext V} {δ ε e π : V} (L : FiniteRankLiftData A B δ ε e)
  (hπ : IsForcingRetraction A.P A.R B.P B.R π)
  (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P) (hone : A.one = B.one)

include hG hone in
theorem graph_codedElementary_in_extension {W : Type*} [SetStructure W] [Nonempty W]
    [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (j : MembershipEndExtension B.Model W) :
    IsCodedMembershipEmbedding (j (domain (L.graph hπ)))
      (j (hierarchy (B.check ε))) (j (L.graph hπ)) :=
  j.codedMembershipEmbedding_map (L.graph_codedElementary hπ hG hone)

end FiniteRankLiftData
end ZFVP

