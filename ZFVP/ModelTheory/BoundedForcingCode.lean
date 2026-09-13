import ZFVP.SetTheory.BoundedSextupleBinding
import ZFVP.SetTheory.ForcingIterationCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedForcingCodeFormula : SetTheorySemisentence 7 :=
  boundedSextupleBind (.bvar 0)
    “a b c d e f z P R π E L t. a = P ∧ b = R ∧ c = π ∧ d = E ∧ e = L ∧ f = t”

theorem boundedForcingCodeFormula_bounded : IsBoundedSetFormula boundedForcingCodeFormula :=
  (boundedSextupleBind_levy (p := .sigma) (k := 0) (.bvar 0)
    (.bounded (.and (.rel _ _) (.and (.rel _ _) (.and (.rel _ _)
      (.and (.rel _ _) (.and (.rel _ _) (.rel _ _)))))))).zero_bounded rfl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedForcingCodeFormula_defined : Defined
    (fun v : Fin 7 → V ↦ v 0 = forcingIterationCode (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    boundedForcingCodeFormula :=
  ⟨fun v ↦ by simp [boundedForcingCodeFormula, eval_boundedSextupleBind, forcingIterationCode]⟩

end ZFVP
