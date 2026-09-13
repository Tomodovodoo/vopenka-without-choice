import ZFVP.ModelTheory.UsubaIterationStages
import ZFVP.ModelTheory.ForcingSuccessorUniform
import ZFVP.ModelTheory.ForcingLimitUniform
import ZFVP.ModelTheory.DeltaOneInitialCode
import ZFVP.ModelTheory.ClassForcingTowerDictionary

/-! One family of formulas defines Usuba's iteration in every model of ZF.
The recursion, including its successor and inverse-limit rules, is the
recursion used by `usubaForcingTower`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def usubaRestorationPosetNameFormula : SetTheorySemisentence 3 :=
  f“Q P R. !(formulaUniqueNameFormula usubaRestorationPosetFormula) Q P R (!isEmpty)”

@[irreducible] def usubaSaturatedPosetNameFormula : SetTheorySemisentence 3 :=
  f“Q P R. !forcingSaturatedNameFormula Q P R
    (!forcingCarrierPoolFormula P R (!usubaRestorationPosetNameFormula P R))
    (!usubaRestorationPosetNameFormula P R)”

@[irreducible] def usubaInitialCodeFormula : SetTheorySemisentence 1 :=
  f“z. !sigmaOneForcingInitialCodeFormula z (!singleton.dfn (!isEmpty))
    (!piOneReverseInclusionOrderFormula (!singleton.dfn (!isEmpty))) (!isEmpty)”

@[irreducible] def usubaIterationSuccessorFormula : SetTheorySemisentence 3 :=
  f“z k s. ∀ P R Q,
    P = !value.dfn (!forcingCodePFormula s) k →
    R = !value.dfn (!forcingCodeRFormula s) k →
    Q = !usubaSaturatedPosetNameFormula P R →
    !forcingSuccessorCodeFormula z k s Q (!reverseInclusionOrderNameFormula P R Q) (!isEmpty)”

@[irreducible] def usubaStageRuleFormula : SetTheorySemisentence 3 :=
  f“z θ s. (θ = !isEmpty ∧ !usubaInitialCodeFormula z) ∨
    (θ ≠ !isEmpty ∧ θ = !succ.dfn (!sUnion.dfn θ) ∧
      !usubaIterationSuccessorFormula z (!sUnion.dfn θ) s) ∨
    (θ ≠ !isEmpty ∧ θ ≠ !succ.dfn (!sUnion.dfn θ) ∧ !forcingInverseCodeFormula z θ s)”

@[irreducible] def usubaIterationStepFormula : SetTheorySemisentence 2 :=
  f“z H. !usubaStageRuleFormula z (!domain.dfn H)
    (!forcingIterationCodeUnionFormula (!domain.dfn H) H)”

@[irreducible] def usubaIterationRecFormula : SetTheorySemisentence 2 :=
  transfiniteRecFormula usubaIterationStepFormula

@[irreducible] def usubaTowerCarrierFormula : SetTheorySemisentence 2 :=
  f“P i. P = !value.dfn (!forcingCodePFormula (!usubaIterationRecFormula i)) i”

@[irreducible] def usubaTowerOrderFormula : SetTheorySemisentence 2 :=
  f“R i. R = !value.dfn (!forcingCodeRFormula (!usubaIterationRecFormula i)) i”

@[irreducible] def usubaTowerSectionFormula : SetTheorySemisentence 3 :=
  f“E i j. E = !value.dfn (!forcingCodeEFormula (!usubaIterationRecFormula j)) (!kpair.dfn i j)”

def usubaTowerDictionary : ClassForcingTowerDictionary :=
  ⟨usubaTowerCarrierFormula, usubaTowerOrderFormula, usubaTowerSectionFormula⟩

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance usubaRestorationPosetNameFormula_defined :
    ℒₛₑₜ-function₂[V] usubaRestorationPosetName via usubaRestorationPosetNameFormula :=
  ⟨fun v ↦ by simp [usubaRestorationPosetNameFormula, usubaRestorationPosetName]⟩

instance usubaSaturatedPosetNameFormula_defined :
    ℒₛₑₜ-function₂[V] usubaSaturatedPosetName via usubaSaturatedPosetNameFormula :=
  ⟨fun v ↦ by simp [usubaSaturatedPosetNameFormula, usubaSaturatedPosetName]⟩

instance usubaInitialCodeFormula_defined :
    ℒₛₑₜ-function₀[V] usubaInitialCode via usubaInitialCodeFormula :=
  ⟨fun v ↦ by simp [usubaInitialCodeFormula, usubaInitialCode]⟩

instance usubaIterationSuccessorFormula_defined :
    ℒₛₑₜ-function₂[V] usubaIterationSuccessor via usubaIterationSuccessorFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [usubaIterationSuccessorFormula, usubaIterationSuccessor]
  constructor
  · intro h
    exact h _ _ _ rfl rfl rfl
  · intro h P R Q hP hR hQ
    subst P R Q
    exact h

instance usubaStageRuleFormula_defined :
    ℒₛₑₜ-function₂[V] usubaStageRule via usubaStageRuleFormula := by
  refine ⟨fun v ↦ ?_⟩
  classical
  simp [usubaStageRuleFormula]
  simp only [← not_isEmpty_iff_isNonempty, isEmpty_iff_eq_empty]
  unfold usubaStageRule
  split_ifs <;> tauto

instance usubaIterationStepFormula_defined :
    ℒₛₑₜ-function₁[V] usubaIterationStep via usubaIterationStepFormula :=
  ⟨fun v ↦ by simp [usubaIterationStepFormula, usubaIterationStep]⟩

instance usubaIterationRecFormula_defined :
    ℒₛₑₜ-function₁[V] usubaIterationRec via usubaIterationRecFormula := by
  unfold usubaIterationRecFormula usubaIterationRec usubaCodeSequence
    DefinableForcingCodeSequence.ofRecursion
  exact transfiniteRecFormula_defined usubaIterationStep usubaIterationStepFormula

instance usubaTowerCarrierFormula_defined :
    ℒₛₑₜ-function₁[V] (usubaForcingTower (V := V)).P via usubaTowerCarrierFormula :=
  ⟨fun v ↦ by simp [usubaTowerCarrierFormula]; rfl⟩

instance usubaTowerOrderFormula_defined :
    ℒₛₑₜ-function₁[V] (usubaForcingTower (V := V)).R via usubaTowerOrderFormula :=
  ⟨fun v ↦ by simp [usubaTowerOrderFormula]; rfl⟩

instance usubaTowerSectionFormula_defined :
    ℒₛₑₜ-function₂[V] (usubaForcingTower (V := V)).sectionMap via usubaTowerSectionFormula :=
  ⟨fun v ↦ by simp [usubaTowerSectionFormula]; rfl⟩

theorem usubaTowerDictionary_defines : usubaTowerDictionary.Defines (usubaForcingTower (V := V)) :=
  ⟨usubaTowerCarrierFormula_defined, usubaTowerOrderFormula_defined, usubaTowerSectionFormula_defined⟩

/-- This fixed formula describes the forcing relation of the actual Usuba tower
in every ground model of ZF, without a countability or LS assumption. -/
theorem usubaForcingFormula_defined {n : ℕ} (φ : SetTheorySemisentence n) :
    ℒₛₑₜ-relation[V] ((usubaForcingTower (V := V)).towerFormula φ) via
      usubaTowerDictionary.formulaDictionary.compile φ :=
  ClassForcingTowerDictionary.forcingFormula_defined usubaTowerDictionary_defines φ

end ZFVP
