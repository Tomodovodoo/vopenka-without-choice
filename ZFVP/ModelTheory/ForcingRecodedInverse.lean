import ZFVP.ModelTheory.ForcingRecodedLimits
import ZFVP.ModelTheory.InverseCollapseCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {θ s Q T m U : V} [IsOrdinal θ]
variable (hs : IsForcingIterationCode θ s)
variable (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
  (Q ‘ i) (T ‘ i) (m ‘ i))
local notation "c" => forcingRecodedCode θ s Q T m
local notation "D" => forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) U

include hs hm in
theorem forcingRecoded_inverseCode_isomorphism
    (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
    (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T)
    (hU : ∀ i ∈ θ, (forcingCodeP s) ‘ i ⊆ U) :
    IsForcingIsomorphism D (forcingThreadOrder θ (forcingCodeR s) D)
      (forcingInverseCodePoset θ c) (forcingInverseCodeOrder θ c) (forcingThreadActionMap θ m D) := by
  have hc := forcingRecoded_code hs hm hT hQt hTt
  have hQ : ∀ i ∈ θ, Q ‘ i ⊆ forcingCodeUniverse c := by
    simpa only [forcingRecodedCode, forcingCodeP_code] using hc.subset_universe
  simpa only [forcingInverseCodePoset, forcingInverseCodeOrder, forcingRecodedCode,
    forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code] using
    forcingRecoded_inverseLimit_isomorphism hs hm hU hQ

end ZFVP
