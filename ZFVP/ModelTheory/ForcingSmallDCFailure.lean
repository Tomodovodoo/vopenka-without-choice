import ZFVP.SetTheory.WoodinSupercompactStarCorrect
import ZFVP.ModelTheory.ForcingStarDCFailure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ForcingContext.small_dependentChoice_failure_certificate (A : ForcingContext V)
    {δ κ : V} (hδ : IsWoodinSupercompact δ) (hP : A.P ∈ hierarchy δ) (hκ : κ ∈ δ)
    (hf : ¬InternalDependentChoiceAt (A.check κ)) :
    ∃ B ∈ hierarchy (A.check δ), IsRankFunctionClosed (succ (A.check κ)) B ∧
      hierarchy (succ (A.check κ)) ∈ B ∧ A.check κ ∈ B ∧ IsTransitive B ∧
      IsFunctionRestrictionClosed B ∧ IsBoundedDependentChoiceFailure (A.check κ) B := by
  let := hδ.1.1
  let := IsOrdinal.of_mem hκ
  have h := A.starDC_failure_witness_at hδ hδ.sigmaOneStarCorrect hP
    (regularCardinal_succ_closed hδ.regular hκ) (mem_succ_self κ) hf
  simpa only [A.check_succ] using h

end ZFVP
