import ZFVP.SetTheory.StandardNaturals

/-! A shared parameter-free formula for each standard internal numeral. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def numeralFormula : ℕ → SetTheorySemisentence 1
  | 0 => isEmpty
  | n + 1 => f“x. x = !succ.dfn (!(numeralFormula n))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance numeralFormula_defined (n : ℕ) : ℒₛₑₜ-function₀[V] (n : V) via numeralFormula n := by
  induction n with
  | zero => exact ⟨fun v ↦ by simp [numeralFormula, isEmpty_iff_eq_empty, zero_def]⟩
  | succ n ih =>
    exact ⟨fun v ↦ by simp [numeralFormula, num_succ_def]⟩

end ZFVP
