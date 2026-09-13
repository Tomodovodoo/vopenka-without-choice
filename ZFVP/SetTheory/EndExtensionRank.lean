import ZFVP.SetTheory.EndExtensionLevy
import ZFVP.SetTheory.DeltaOneRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V W : Type*} [SetStructure V] [SetStructure W] [Nonempty V] [Nonempty W]
  [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem MembershipEndExtension.map_rank (j : MembershipEndExtension V W) (x : V) :
    j (rank x) = rank (j x) :=
  (j.deltaOne_defined sigmaOneRankFormula_sigmaOne piOneRankFormula_piOne
    (fun v ↦ v 0 = rank (v 1)) (fun v ↦ v 0 = rank (v 1)) ![rank x, x]).mp rfl

end ZFVP
