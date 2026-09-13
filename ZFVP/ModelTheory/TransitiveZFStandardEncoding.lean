import ZFVP.ModelTheory.TransitiveZFConstructors
import ZFVP.Syntax.StandardCodeExpressions

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem encodeMembershipTerm_val {n : ℕ} (t : SetTheorySemiterm Empty n) :
    (encodeSemiterm (fun {k} ↦ membershipFunctionSymbol (V := SetDomain U) (k := k)) Empty.elim t).val =
      encodeSemiterm (fun {k} ↦ membershipFunctionSymbol (V := V) (k := k)) Empty.elim t := by
  rw [encodeMembershipTerm_index, boundVarCode_val, numeral_val, encodeMembershipTerm_index]

theorem membershipSymbol_val {k : ℕ} (r : Language.Set.Rel k) :
    (membershipSymbol (V := SetDomain U) r).val = membershipSymbol (V := V) r := by
  cases r
  · exact numeral_val U 0
  · exact numeral_val U 1

theorem encodeMembershipFormula_val {n : ℕ} (φ : SetTheorySemisentence n) :
    (encodeMembershipFormula (V := SetDomain U) φ).val = encodeMembershipFormula (V := V) φ := by
  induction φ with
  | verum => exact truthCode_val U
  | falsum => exact falsityCode_val U
  | rel r ts =>
    simp only [encodeMembershipFormula, encodeSemiformula, atomCode_val, relationToken_val, membershipSymbol_val,
      standardTuple_val, encodeMembershipTerm_val]
  | nrel r ts =>
    simp only [encodeMembershipFormula, encodeSemiformula, negAtomCode_val, relationToken_val, membershipSymbol_val,
      standardTuple_val, encodeMembershipTerm_val]
  | and φ ψ ihφ ihψ =>
    exact (andCode_val U _ _).trans (congrArg₂ andCode ihφ ihψ)
  | or φ ψ ihφ ihψ =>
    exact (orCode_val U _ _).trans (congrArg₂ orCode ihφ ihψ)
  | all φ ih => exact (allCode_val U _).trans (congrArg allCode ih)
  | exs φ ih => exact (existsCode_val U _).trans (congrArg existsCode ih)

end TransitiveZF
end ZFVP

