import ZFVP.ModelTheory.WoodinIterationInitial
import ZFVP.ModelTheory.WoodinSelectorUniform

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def woodinStageCodeFormula : SetTheorySemisentence 5 :=
  f“z P R o κ. z = !kpair.dfn P (!kpair.dfn R (!kpair.dfn o κ))”

@[irreducible] def woodinStagePosetFormula : SetTheorySemisentence 2 :=
  f“z x. z = !kpair.π₁.dfn x”

@[irreducible] def woodinStageOrderFormula : SetTheorySemisentence 2 :=
  f“z x. z = !kpair.π₁.dfn (!kpair.π₂.dfn x)”

@[irreducible] def woodinStageTopFormula : SetTheorySemisentence 2 :=
  f“z x. z = !kpair.π₁.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn x))”

@[irreducible] def woodinStageCardinalValueFormula : SetTheorySemisentence 2 :=
  f“z x. z = !kpair.π₂.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn x))”

@[irreducible] def woodinSuccessorAtFormula : SetTheorySemisentence 6 :=
  f“z P R o κ δ. !woodinStageCodeFormula z
    (!twoStepConditionsFormula P R (!saturatedWoodinPrefixPosetNameFormula P R o κ δ) (!isEmpty))
    (!twoStepOrderFormula P R (!saturatedWoodinPrefixPosetNameFormula P R o κ δ)
      (!saturatedWoodinPrefixOrderNameFormula P R o κ δ) (!isEmpty)) (!kpair.dfn o (!isEmpty)) δ”

@[irreducible] def woodinSuccessorStepFormula : SetTheorySemisentence 2 :=
  f“z x. !woodinSuccessorAtFormula z (!woodinStagePosetFormula x) (!woodinStageOrderFormula x)
    (!woodinStageTopFormula x) (!woodinStageCardinalValueFormula x)
    (!woodinPrefixCutoffValueFormula (!woodinStagePosetFormula x) (!woodinStageOrderFormula x)
      (!woodinStageTopFormula x) (!woodinStageCardinalValueFormula x))”

@[irreducible] def woodinIterationStageFormula : SetTheorySemisentence 4 :=
  f“z s K i. !woodinStageCodeFormula z (!value.dfn (!forcingCodePFormula s) i)
    (!value.dfn (!forcingCodeRFormula s) i) (!value.dfn (!forcingCodetFormula s) i) (!value.dfn K i)”

@[irreducible] def woodinIterationSuccessorFormula : SetTheorySemisentence 4 :=
  f“z k s K. ∀ P, !value.dfn P (!forcingCodePFormula s) k →
    ∀ R, !value.dfn R (!forcingCodeRFormula s) k → ∀ o, !value.dfn o (!forcingCodetFormula s) k →
    ∀ κ, !value.dfn κ K k → ∀ δ, !woodinPrefixCutoffValueFormula δ P R o κ →
    !forcingSuccessorCodeFormula z k s (!saturatedWoodinPrefixPosetNameFormula P R o κ δ)
      (!saturatedWoodinPrefixOrderNameFormula P R o κ δ) (!isEmpty)”

@[irreducible] def woodinIterationCardinalNextFormula : SetTheorySemisentence 4 :=
  f“z k s K. !forcingFamilyNextFormula z (!succ.dfn k) K
    (!woodinStageCardinalValueFormula (!woodinSuccessorStepFormula (!woodinIterationStageFormula s K k)))”

@[irreducible] def woodinLimitCardinalFormula : SetTheorySemisentence 2 :=
  f“z K. z = !sUnion.dfn (!range.dfn K)”

@[irreducible] def forcingInitialCodeFormula : SetTheorySemisentence 4 :=
  f“z P R o. !forcingIterationCodeFormula z
    (!forcingFamilyNextFormula (!isEmpty) (!isEmpty) P) (!forcingFamilyNextFormula (!isEmpty) (!isEmpty) R)
    (!forcingMatrixNextFormula (!isEmpty) (!isEmpty) (!isEmpty) (!identity.dfn P))
    (!forcingMatrixNextFormula (!isEmpty) (!isEmpty) (!isEmpty) (!identity.dfn P))
    (!forcingMatrixNextFormula (!isEmpty) (!isEmpty) (!isEmpty) (!forcingIdentityLiftFormula P))
    (!forcingFamilyNextFormula (!isEmpty) (!isEmpty) o)”

@[irreducible] def woodinSeedStageFormula : SetTheorySemisentence 1 :=
  f“z. !woodinStageCodeFormula z (!singleton.dfn (!isEmpty))
    (!prod.dfn (!singleton.dfn (!isEmpty)) (!singleton.dfn (!isEmpty))) (!isEmpty) (!woodinSeedCardinalFormula)”

@[irreducible] def woodinInitialStageFormula : SetTheorySemisentence 1 :=
  f“z. !woodinSuccessorStepFormula z (!woodinSeedStageFormula)”

@[irreducible] def woodinInitialCodeFormula : SetTheorySemisentence 1 :=
  f“z. !forcingInitialCodeFormula z (!woodinStagePosetFormula (!woodinInitialStageFormula))
    (!woodinStageOrderFormula (!woodinInitialStageFormula)) (!woodinStageTopFormula (!woodinInitialStageFormula))”

@[irreducible] def woodinInitialCardinalsFormula : SetTheorySemisentence 1 :=
  f“z. !forcingFamilyNextFormula z (!isEmpty) (!isEmpty)
    (!woodinStageCardinalValueFormula (!woodinInitialStageFormula))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinStageCodeFormula_defined : ℒₛₑₜ-function₄[V] woodinStageCode via woodinStageCodeFormula :=
  ⟨fun v ↦ by simp [woodinStageCodeFormula, woodinStageCode]⟩

instance woodinStagePosetFormula_defined : ℒₛₑₜ-function₁[V] woodinStagePoset via woodinStagePosetFormula :=
  ⟨fun v ↦ by simp [woodinStagePosetFormula, woodinStagePoset]⟩

instance woodinStageOrderFormula_defined : ℒₛₑₜ-function₁[V] woodinStageOrder via woodinStageOrderFormula :=
  ⟨fun v ↦ by simp [woodinStageOrderFormula, woodinStageOrder]⟩

instance woodinStageTopFormula_defined : ℒₛₑₜ-function₁[V] woodinStageTop via woodinStageTopFormula :=
  ⟨fun v ↦ by simp [woodinStageTopFormula, woodinStageTop]⟩

instance woodinStageCardinalValueFormula_defined : ℒₛₑₜ-function₁[V] woodinStageCardinal via woodinStageCardinalValueFormula :=
  ⟨fun v ↦ by simp [woodinStageCardinalValueFormula, woodinStageCardinal]⟩

instance woodinSuccessorAtFormula_defined : ℒₛₑₜ-function₅[V] woodinSuccessorAt via woodinSuccessorAtFormula :=
  ⟨fun v ↦ by simp [woodinSuccessorAtFormula, woodinSuccessorAt]⟩

instance woodinSuccessorStepFormula_defined : ℒₛₑₜ-function₁[V] woodinSuccessorStep via woodinSuccessorStepFormula :=
  ⟨fun v ↦ by simp [woodinSuccessorStepFormula, woodinSuccessorStep]⟩

instance woodinIterationStageFormula_defined : ℒₛₑₜ-function₃[V] woodinIterationStage via woodinIterationStageFormula :=
  ⟨fun v ↦ by simp [woodinIterationStageFormula, woodinIterationStage]⟩

instance woodinIterationSuccessorFormula_defined : ℒₛₑₜ-function₃[V] woodinIterationSuccessor via woodinIterationSuccessorFormula :=
  ⟨fun v ↦ by simp [woodinIterationSuccessorFormula, woodinIterationSuccessor]⟩

instance woodinIterationCardinalNextFormula_defined : ℒₛₑₜ-function₃[V] woodinIterationCardinalNext via woodinIterationCardinalNextFormula :=
  ⟨fun v ↦ by simp [woodinIterationCardinalNextFormula, woodinIterationCardinalNext]⟩

instance woodinLimitCardinalFormula_defined : ℒₛₑₜ-function₁[V] woodinLimitCardinal via woodinLimitCardinalFormula :=
  ⟨fun v ↦ by simp [woodinLimitCardinalFormula, woodinLimitCardinal]⟩

instance forcingInitialCodeFormula_defined : ℒₛₑₜ-function₃[V] forcingInitialCode via forcingInitialCodeFormula :=
  ⟨fun v ↦ by simp [forcingInitialCodeFormula, forcingInitialCode]⟩

instance woodinSeedStageFormula_defined : ℒₛₑₜ-function₀[V] woodinSeedStage via woodinSeedStageFormula :=
  ⟨fun v ↦ by simp [woodinSeedStageFormula, woodinSeedStage]⟩

instance woodinInitialStageFormula_defined : ℒₛₑₜ-function₀[V] woodinInitialStage via woodinInitialStageFormula :=
  ⟨fun v ↦ by simp [woodinInitialStageFormula, woodinInitialStage]⟩

instance woodinInitialCodeFormula_defined : ℒₛₑₜ-function₀[V] woodinInitialCode via woodinInitialCodeFormula :=
  ⟨fun v ↦ by simp [woodinInitialCodeFormula, woodinInitialCode]⟩

instance woodinInitialCardinalsFormula_defined : ℒₛₑₜ-function₀[V] woodinInitialCardinals via woodinInitialCardinalsFormula :=
  ⟨fun v ↦ by simp [woodinInitialCardinalsFormula, woodinInitialCardinals]⟩

end ZFVP
