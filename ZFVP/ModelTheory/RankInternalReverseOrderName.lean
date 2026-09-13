import ZFVP.ModelTheory.ForcingRankInternalNames
import ZFVP.ModelTheory.ForcingSmallInaccessible
import ZFVP.ModelTheory.TransitiveZFWoodinCollapse
import ZFVP.ModelTheory.ForcingReverseOrderName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext
variable (A : ForcingContext V) {ξ : V} [IsOrdinal ξ]
  [Nonempty (SetDomain (hierarchy ξ))] [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankInternalReverseOrder_value (hξ : IsChoicelessInaccessible ξ)
    (P R one : SetDomain (hierarchy ξ)) (hP : P.val = A.P) (hR : R.val = A.R)
    (ho : one.val = A.one) (Q : ForcingName P) :
    A.ofName (A.rankInternalName P hP
      ⟨reverseInclusionOrderName P R Q.val, reverseInclusionOrderName_isName _ _ _⟩) =
      reverseInclusionOrder (A.ofName (A.rankInternalName P hP Q)) := by
  let := hierarchy_transitive ξ
  have hord : IsForcingPreorder P R := (TransitiveZF.forcingPreorder_iff (hierarchy ξ) P R).mpr
    (by simpa only [hP, hR] using A.order)
  have htop : IsForcingTop P R one := (TransitiveZF.forcingTop_iff (hierarchy ξ) P R one).mpr
    (by simpa only [hP, hR, ho] using A.top)
  let S : ForcingName P := ⟨reverseInclusionOrderName P R Q.val, reverseInclusionOrderName_isName _ _ _⟩
  let v : Fin 2 → ForcingName P := ![S, Q]
  have hf : ∀ p ∈ P, p ∈ forcingFormula P R piOneReverseInclusionOrderFormula
      (standardTuple (fun i ↦ (v i).val)) := by
    intro p hp
    have hn : (fun i ↦ (v i).val) = ![S.val, Q.val] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    rw [hn]
    exact reverseInclusionOrderName_forces hord htop hp Q
  have hi := A.check_inaccessible_of_small hξ (hP ▸ P.property)
  let := hi.1
  let := rankDomain_nonempty hi.2.1
  let := hi.rankCriterion.models_zf
  let := hierarchy_transitive (A.check ξ)
  let w : Fin 2 → SetDomain (hierarchy (A.check ξ)) := fun i ↦ A.rankInternalValue hξ P hP (v i)
  have he : w 0 = reverseInclusionOrder (w 1) :=
    (Defined.eval_iff (φ := piOneReverseInclusionOrderFormula) w).mp
      (A.rankInternalValue_eval_of_forces hξ P R hP hR piOneReverseInclusionOrderFormula v hf)
  have hv := congrArg Subtype.val he
  rw [TransitiveZF.reverseInclusionOrder_val] at hv
  exact hv

end ForcingContext
end ZFVP
