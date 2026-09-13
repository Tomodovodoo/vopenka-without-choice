import ZFVP.Syntax.FoundationEquality

/-! A logical equality formula with two bound variables, for arbitrary coded languages. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def standardEqualityArguments : V :=
  standardTuple (fun i : Fin 2 ↦ boundVarCode (i.val : V))

noncomputable def standardEqualityCode : V := atomCode equalityToken standardEqualityArguments

theorem standardEqualityArguments_typed {L : V} (hL : IsLanguageCode L) (Γ : V) :
    standardEqualityArguments ∈ termSet L Γ (2 : V) ^ (2 : V) :=
  standardTuple_mem_function _ (fun i ↦
    (termSet_closed hL (by simp) Γ).1 _ (natCast_mem_of_lt i.isLt))

theorem standardEqualityCode_mem {L : V} (hL : IsLanguageCode L) (Γ : V) :
    standardEqualityCode ∈ formulaSet L Γ (2 : V) :=
  (atomCode_mem_iff hL).mpr ⟨by simp, Or.inl ⟨rfl, standardEqualityArguments_typed hL Γ⟩⟩

theorem satisfies_standardEqualityCode {L Γ M E b : V} (hM : IsStructureCode L M)
    (hb : b ∈ structureDomain M ^ (2 : V)) :
    Satisfies L Γ M E (2 : V) standardEqualityCode b ↔ b ‘ (0 : V) = b ‘ (1 : V) := by
  rw [standardEqualityCode, satisfies_atom hM.language (by simp)
    (Or.inl ⟨rfl, standardEqualityArguments_typed hM.language Γ⟩) hb, atomicHolds_equality]
  unfold evaluatedArguments evaluateWithFreeAssignment standardEqualityArguments
  rw [compose_standardTuple _ _ (fun i ↦ by
    simpa using (termSet_closed hM.language (by simp) Γ).1 _ (natCast_mem_of_lt i.isLt))]
  have hzero : (0 : V) = (((0 : Fin 2).val : ℕ) : V) := rfl
  have hone : (1 : V) = (((1 : Fin 2).val : ℕ) : V) := rfl
  rw [hzero, value_standardTuple, hone, value_standardTuple]
  rw [termEvaluation_boundVar hM.language (by simp) Γ M b E (by simp),
    termEvaluation_boundVar hM.language (by simp) Γ M b E (by simp)]

theorem standardTuple_equality_values (x y : V) :
    (standardTuple ![x, y]) ‘ (0 : V) = x ∧ (standardTuple ![x, y]) ‘ (1 : V) = y := by
  exact ⟨value_standardTuple ![x, y] 0, value_standardTuple ![x, y] 1⟩

end ZFVP
