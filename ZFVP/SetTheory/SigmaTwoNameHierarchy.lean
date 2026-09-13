import ZFVP.SetTheory.NameHierarchyTable

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaTwoNameHierarchyFormula : SetTheorySemisentence 3 :=
  “H P α. !IsOrdinal.dfn α ∧ ∃ a, ∃ f, ∃ T,
    !boundedSuccFormula a α ∧ !piOneNameHierarchyTableFormula f a T P ∧
      !boundedPairMemberFormula f α H”

theorem sigmaTwoNameHierarchyFormula_sigmaTwo :
    IsSigmaFormula 2 sigmaTwoNameHierarchyFormula :=
  .and (.bounded (isOrdinalFormula_bounded.subst _)) (.exs (.exs (.exs
    (.and (.bounded (boundedSuccFormula_bounded.subst _))
      (.and (.raise (piOneNameHierarchyTableFormula_piOne.subst _))
        (.bounded (boundedPairMemberFormula_bounded.subst _)))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaTwoNameHierarchyFormula (H P α : V) :
    sigmaTwoNameHierarchyFormula.Evalb ![H, P, α] ↔
      IsOrdinal α ∧ H = forcingNameHierarchy P α := by
  have he : sigmaTwoNameHierarchyFormula.Evalb ![H, P, α] ↔
      IsOrdinal α ∧ ∃ a f T : V, a = succ α ∧
        piOneNameHierarchyTableFormula.Evalb ![f, a, T, P] ∧ ⟨α, H⟩ₖ ∈ f := by
    simp [sigmaTwoNameHierarchyFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def]
  rw [he]
  constructor
  · rintro ⟨ha, a, f, T, rfl, ht, hp⟩
    let := ha
    exact ⟨ha, nameHierarchyTable_row_eq ht (by simp) hp⟩
  · rintro ⟨ha, rfl⟩
    let := ha
    exact ⟨ha, succ α, definableGraph (succ α) (forcingNameHierarchy P) (by definability),
      repl (forcingNameHierarchy P) (by definability) (succ α), rfl,
      nameHierarchyTable_exists P (succ α),
      (pair_mem_definableGraph_iff _ _ _ _ _).mpr ⟨by simp, rfl⟩⟩

def piTwoNameHierarchyFormula : SetTheorySemisentence 3 :=
  “H P α. !IsOrdinal.dfn α ∧ ∀ X, !sigmaTwoNameHierarchyFormula X P α → X = H”

theorem piTwoNameHierarchyFormula_piTwo : IsPiFormula 2 piTwoNameHierarchyFormula :=
  .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.all (.or (sigmaTwoNameHierarchyFormula_sigmaTwo.subst _).neg (.bounded (.rel _ _))))

theorem eval_piTwoNameHierarchyFormula (H P α : V) :
    piTwoNameHierarchyFormula.Evalb ![H, P, α] ↔
      IsOrdinal α ∧ H = forcingNameHierarchy P α := by
  have he : piTwoNameHierarchyFormula.Evalb ![H, P, α] ↔
      IsOrdinal α ∧ ∀ X : V, (IsOrdinal α ∧ X = forcingNameHierarchy P α) → X = H := by
    simp [piTwoNameHierarchyFormula, eval_sigmaTwoNameHierarchyFormula,
      Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
      Function.comp_def]
  rw [he]
  constructor
  · rintro ⟨ha, h⟩
    exact ⟨ha, (h _ ⟨ha, rfl⟩).symm⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨ha, fun _ h ↦ h.2⟩

end ZFVP

