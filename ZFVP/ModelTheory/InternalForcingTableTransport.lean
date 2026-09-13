import ZFVP.Syntax.BoundedInternalForcingTable
import ZFVP.ModelTheory.LimitRankEmbedding

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsCodedMembershipEmbedding
variable {A B f U P R D H T : V} [IsTransitive A] [IsTransitive B]

theorem value_atomicTruthTable (h : IsCodedMembershipEmbedding A B f)
    [IsTransitive U] [IsTransitive (f ‘ U)]
    (hU : U ∈ A) (hP : P ∈ A) (hR : R ∈ A) (hH : H ∈ A)
    (ht : IsAtomicTruthTable P R U H) : IsAtomicTruthTable (f ‘ P) (f ‘ R) (f ‘ U) (f ‘ H) := by
  have he := (h.bounded_formula_iff boundedAtomicTruthTableFormula_bounded ![U, P, R, H]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hU, hP, hR, hH])).mp
      ((eval_boundedAtomicTruthTableFormula P R H).mpr ht)
  have hv : (fun i ↦ f ‘ (![U, P, R, H] i)) = ![f ‘ U, f ‘ P, f ‘ R, f ‘ H] := by
    funext i
    repeat' first | exact rfl | exact Fin.elim0 i | (refine Fin.cases ?_ (fun i ↦ ?_) i)
  rw [hv] at he
  exact (eval_boundedAtomicTruthTableFormula _ _ _).mp he

theorem value_internalForcingTruthTable (h : IsCodedMembershipEmbedding A B f)
    [IsSequenceSupport U] [IsSequenceSupport (f ‘ U)]
    (hU : U ∈ A) (hω : (ω : V) ∈ A)
    (hF : (formulaFamily membershipLanguageCode ∅ : V) ∈ A)
    (hfixF : f ‘ (formulaFamily membershipLanguageCode ∅ : V) = formulaFamily membershipLanguageCode ∅)
    (hP : P ∈ A) (hR : R ∈ A) (hD : D ∈ A) (hH : H ∈ A) (hT : T ∈ A)
    (hPU : P ⊆ U) (hDU : D ⊆ U) (ha : IsAtomicTruthTable P R U H)
    (ht : IsInternalForcingTruthTable P R D T) :
    IsInternalForcingTruthTable (f ‘ P) (f ‘ R) (f ‘ D) (f ‘ T) := by
  have hPi : f ‘ P ⊆ f ‘ U :=
    (h.bounded_defined_iff isSubsetOf_bounded (fun v ↦ v 0 ⊆ v 1) ![P, U]
      (by simp [hP, hU])).mp hPU
  have hDi : f ‘ D ⊆ f ‘ U :=
    (h.bounded_defined_iff isSubsetOf_bounded (fun v ↦ v 0 ⊆ v 1) ![D, U]
      (by simp [hD, hU])).mp hDU
  have hai := h.value_atomicTruthTable hU hP hR hH ha
  have hs := (eval_boundedInternalForcingTableFormula hPU hDU ha T).mpr ht
  have he := (h.bounded_formula_iff boundedInternalForcingTableFormula_bounded
    ![U, ω, formulaFamily membershipLanguageCode ∅, P, R, D, H, T]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hU, hω, hF, hP, hR, hD, hH, hT])).mp hs
  have hv : (fun i ↦ f ‘ (![U, ω, formulaFamily membershipLanguageCode ∅, P, R, D, H, T] i)) =
      ![f ‘ U, f ‘ (ω : V), f ‘ (formulaFamily membershipLanguageCode ∅ : V), f ‘ P, f ‘ R, f ‘ D, f ‘ H, f ‘ T] := by
    funext i
    repeat' first | exact rfl | exact Fin.elim0 i | (refine Fin.cases ?_ (fun i ↦ ?_) i)
  rw [hv, h.value_omega hω, hfixF] at he
  exact (eval_boundedInternalForcingTableFormula hPi hDi hai (f ‘ T)).mp he

end IsCodedMembershipEmbedding
end ZFVP
