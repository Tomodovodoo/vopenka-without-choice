import ZFVP.ModelTheory.ForcingRealization
import ZFVP.ModelTheory.ForcingQuotientGeneric

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

noncomputable def genericSet (A : ForcingContext V) : A.Model :=
  forcingGenericSet A.P A.R A.G A.order A.generic.1 A.one A.top

theorem mem_genericSet_iff (A : ForcingContext V) (x : A.Model) :
    x ∈ A.genericSet ↔ ∃ p ∈ A.G, x = A.check p :=
  forcingGenericSet_mem_iff A.P A.R A.G A.order A.generic A.one A.top x

theorem check_mem_genericSet_iff (A : ForcingContext V) (p : V) :
    A.check p ∈ A.genericSet ↔ p ∈ A.G :=
  forcingCheck_mem_genericSet_iff A.P A.R A.G A.order A.generic A.one A.top p

theorem genericSet_subset (A : ForcingContext V) : A.genericSet ⊆ A.check A.P :=
  forcingGenericSet_subset_check A.P A.R A.G A.order A.generic A.one A.top

noncomputable def realization (A : ForcingContext V) : ForcingRealization A A.Model where
  ground := A.checkEmbedding
  genericSet := A.genericSet
  generic_subset := A.genericSet_subset
  generic_mem := A.check_mem_genericSet_iff

end ForcingContext
end ZFVP
