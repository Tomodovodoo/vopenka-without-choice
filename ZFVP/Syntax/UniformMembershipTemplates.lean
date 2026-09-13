import ZFVP.Syntax.MembershipTailTemplates
import ZFVP.Syntax.UniformPrefixTuples
import ZFVP.Syntax.UniformStandardCodes
import ZFVP.Syntax.UniformMembershipRenaming
import ZFVP.Syntax.UniformNegation

/-! A parameter-free dictionary for each finite template compiler, including parameter tails. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipTemplate

def compileFormula {a : ℕ} : {m : ℕ} → MembershipTemplate a m → SetTheorySemisentence 2
  | _, .fixed ψ => f“y φ. y = !(encodeMembershipFormulaFormula ψ)”
  | m, .hole r => f“y φ. y = !renameMembershipFormulaFormula (!(numeralFormula a)) (!(numeralFormula m))
      (!(standardTupleConstantFormula (fun i ↦ numeralFormula (r i).val))) φ”
  | _, .conj s t => f“y φ. y = !andCodeFormula (!(compileFormula s) φ) (!(compileFormula t) φ)”
  | _, .disj s t => f“y φ. y = !orCodeFormula (!(compileFormula s) φ) (!(compileFormula t) φ)”
  | m, .neg s => f“y φ. y = !negateFormulaFormula (!membershipLanguageCodeFormula) (!isEmpty)
      (!(numeralFormula m)) (!(compileFormula s) φ)”
  | _, .all s => f“y φ. y = !allCodeFormula (!(compileFormula s) φ)”
  | _, .exs s => f“y φ. y = !existsCodeFormula (!(compileFormula s) φ)”

def compileTailFormula {a : ℕ} : {m : ℕ} → MembershipTemplate a m → SetTheorySemisentence 3
  | m, .fixed ψ => f“y n φ. y = !renameMembershipFormulaFormula (!(numeralFormula m))
      (!(prefixSizeFormula m) n) (!(standardTupleConstantFormula (fun i : Fin m ↦ numeralFormula i.val)))
      (!(encodeMembershipFormulaFormula ψ))”
  | m, .hole r => f“y n φ. y = !renameMembershipFormulaFormula (!(prefixSizeFormula a) n)
      (!(prefixSizeFormula m) n) (!(prefixRenamingFormula r) n) φ”
  | _, .conj s t => f“y n φ. y = !andCodeFormula (!(compileTailFormula s) n φ) (!(compileTailFormula t) n φ)”
  | _, .disj s t => f“y n φ. y = !orCodeFormula (!(compileTailFormula s) n φ) (!(compileTailFormula t) n φ)”
  | m, .neg s => f“y n φ. y = !negateFormulaFormula (!membershipLanguageCodeFormula) (!isEmpty)
      (!(prefixSizeFormula m) n) (!(compileTailFormula s) n φ)”
  | _, .all s => f“y n φ. y = !allCodeFormula (!(compileTailFormula s) n φ)”
  | _, .exs s => f“y n φ. y = !existsCodeFormula (!(compileTailFormula s) n φ)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance compileFormula_defined {a m : ℕ} (t : MembershipTemplate a m) :
    ℒₛₑₜ-function₁[V] (fun φ ↦ t.compile φ) via compileFormula t := by
  induction t with
  | fixed ψ => exact ⟨fun v ↦ by simp [compileFormula, compile]⟩
  | hole r => exact ⟨fun v ↦ by simp [compileFormula, compile]⟩
  | conj s t ihs iht => exact ⟨fun v ↦ by simp [compileFormula, compile]⟩
  | disj s t ihs iht => exact ⟨fun v ↦ by simp [compileFormula, compile]⟩
  | neg s ih => exact ⟨fun v ↦ by simp [compileFormula, compile]⟩
  | all s ih => exact ⟨fun v ↦ by simp [compileFormula, compile]⟩
  | exs s ih => exact ⟨fun v ↦ by simp [compileFormula, compile]⟩

instance compileTailFormula_defined {a m : ℕ} (t : MembershipTemplate a m) :
    ℒₛₑₜ-function₂[V] (fun n φ ↦ t.compileTail n φ) via compileTailFormula t := by
  induction t with
  | fixed ψ => exact ⟨fun v ↦ by simp [compileTailFormula, compileTail]⟩
  | hole r => exact ⟨fun v ↦ by simp [compileTailFormula, compileTail]⟩
  | conj s t ihs iht => exact ⟨fun v ↦ by simp [compileTailFormula, compileTail]⟩
  | disj s t ihs iht => exact ⟨fun v ↦ by simp [compileTailFormula, compileTail]⟩
  | neg s ih => exact ⟨fun v ↦ by simp [compileTailFormula, compileTail]⟩
  | all s ih => exact ⟨fun v ↦ by simp [compileTailFormula, compileTail]⟩
  | exs s ih => exact ⟨fun v ↦ by simp [compileTailFormula, compileTail]⟩

end MembershipTemplate

end ZFVP
