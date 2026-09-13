import ZFVP.ModelTheory.CollapseSerialHull
import ZFVP.ModelTheory.ForcingLowRankAssignments

/-! Countability of the values of a ground-model set of forcing names. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem internallyCountable_evaluation_range (S : ForcingContext V) {X C : V}
    (hX : IsInternallyCountable (S.check X)) (hCX : C ⊆ X)
    (hC : ∀ σ ∈ C, IsForcingName S.P σ) :
    IsInternallyCountable (range (S.evaluationGraph C hC)) := by
  have hc : S.check C ⊆ S.check X := by
    intro x hx
    obtain ⟨σ, hσ, rfl⟩ := (S.mem_check_iff C x).mp hx
    exact (S.check_mem_iff σ X).mpr (hCX σ hσ)
  exact internallyCountable_of_surjection (internallyCountable_subset hX hc)
    (S.evaluationGraph_mem_function C hC) rfl

theorem internallyCountable_checked_of_surjection (S : ForcingContext V) {D X e : V}
    (hD : IsInternallyCountable (S.check D)) (he : e ∈ X ^ D) (hr : range e = X) :
    IsInternallyCountable (S.check X) := by
  apply internallyCountable_of_surjection hD ((S.check_function_iff e D X).mpr he)
  let := IsFunction.of_mem he
  exact (S.checkEmbedding.map_range e).symm.trans (congrArg S.check hr)

theorem internallyCountable_evaluation_range_of_surjection (S : ForcingContext V)
    {D X C e : V} (hD : IsInternallyCountable (S.check D))
    (he : e ∈ X ^ D) (hr : range e = X) (hCX : C ⊆ X)
    (hC : ∀ σ ∈ C, IsForcingName S.P σ) :
    IsInternallyCountable (range (S.evaluationGraph C hC)) :=
  S.internallyCountable_evaluation_range (S.internallyCountable_checked_of_surjection hD he hr) hCX hC

end ForcingContext

namespace CollapseModel

theorem internallyCountable_evaluation_range {D X C e : V} {G : Set V}
    (hG : IsExternalForcingGeneric (collapseConditions D) (collapseOrder D) G)
    (hD : IsNonempty D) (he : e ∈ X ^ D) (hr : range e = X) (hCX : C ⊆ X)
    (hC : ∀ σ ∈ C, IsForcingName (collapseContext D G hG).P σ) :
    IsInternallyCountable (range ((collapseContext D G hG).evaluationGraph C hC)) :=
  (collapseContext D G hG).internallyCountable_evaluation_range_of_surjection
    (check_internallyCountable hG hD) he hr hCX hC

end CollapseModel
end ZFVP
