import ZFVP.ModelTheory.ForcingClosedSequences
import ZFVP.SetTheory.LeastDependentChoiceFailure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingClosedAt_finite {P R one n : V} (hR : IsForcingPreorder P R)
    (hone : IsForcingTop P R one) (hn : n ∈ (ω : V)) : IsForcingClosedAt P R n := by
  apply naturalNumber_induction (IsForcingClosedAt P R) (by definability) ?_ ?_ n hn
  · intro f _
    exact ⟨one, hone.1, fun i hi ↦ False.elim (by simp [zero_def] at hi)⟩
  · intro i _ _ f hf
    have hiP := function_value_mem hf.1 (show i ∈ succ i by simp)
    refine ⟨f ‘ i, hiP, fun j hj ↦ ?_⟩
    rcases mem_succ_iff.mp hj with rfl | hj
    · exact hR.2.1 _ hiP
    · exact hf.2 i (by simp) j hj

namespace ForcingContext

theorem function_eq_check_of_finite (S : ForcingContext V) {n X : V} (hn : n ∈ (ω : V))
    {z : S.Model} (hz : z ∈ S.check X ^ S.check n) : ∃ s ∈ X ^ n, S.check s = z := by
  let := IsOrdinal.of_mem hn
  apply S.function_eq_check_of_closed (dependentChoiceAt_finite n hn) ?_ hz
  intro α hα hαn
  let := hα
  exact forcingClosedAt_finite S.order S.top (ordinal_mem_of_subset_mem hαn hn)

end ForcingContext
end ZFVP
