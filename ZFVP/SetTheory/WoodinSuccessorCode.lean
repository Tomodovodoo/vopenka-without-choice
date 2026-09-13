import ZFVP.ModelTheory.SaturatedWoodinPrefix

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinPrefixCutoff_uniform_definable : ℒₛₑₜ-function₄[V] woodinPrefixCutoff := by
  have h : ℒₛₑₜ-relation₅[V] (fun c P R o κ ↦
      IsLeastOrdinal (IsWoodinPrefixCutoff P R o κ) c ∨
        (¬∃ δ, IsOrdinal δ ∧ IsWoodinPrefixCutoff P R o κ δ) ∧ c = 0) := by
    unfold IsLeastOrdinal
    apply Language.Definable.or
    · apply Language.Definable.and
      · definability
      · apply Language.Definable.and
        · apply Language.DefinableRel₅.comp <;> definability
        · apply Language.Definable.all
          apply Language.Definable.imp
          · definability
          · apply Language.Definable.imp
            · apply Language.DefinableRel₅.comp <;> definability
            · definability
    · apply Language.Definable.and
      · apply Language.Definable.not
        apply Language.Definable.exs
        apply Language.Definable.and
        · definability
        · apply Language.DefinableRel₅.comp <;> definability
      · definability
  apply Language.Definable.of_iff h
  intro v
  exact leastOrdinalOrZero_eq_iff (IsWoodinPrefixCutoff (v 1) (v 2) (v 3))
    (by definability) (v 4) (v 0)

instance woodinPrefixPosetName_uniform_definable : Language.DefinableFunction ℒₛₑₜ
    (fun v : Fin 5 → V ↦ woodinPrefixPosetName (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  woodinPrefixPosetNameFormula_defined.to_definable

instance woodinPrefixOrderName_uniform_definable : Language.DefinableFunction ℒₛₑₜ
    (fun v : Fin 5 → V ↦ woodinPrefixOrderName (v 0) (v 1) (v 2) (v 3) (v 4)) := by
  let := reverseInclusionOrderNameFormula_defined (V := V) |>.to_definable
  unfold woodinPrefixOrderName
  apply Language.DefinableFunction₃.comp
  · definability
  · definability
  · exact woodinPrefixPosetName_uniform_definable

noncomputable def woodinStageCode (P R one κ : V) : V := ⟨P, ⟨R, ⟨one, κ⟩ₖ⟩ₖ⟩ₖ
noncomputable def woodinStagePoset (x : V) : V := kpair.π₁ x
noncomputable def woodinStageOrder (x : V) : V := kpair.π₁ (kpair.π₂ x)
noncomputable def woodinStageTop (x : V) : V := kpair.π₁ (kpair.π₂ (kpair.π₂ x))
noncomputable def woodinStageCardinal (x : V) : V := kpair.π₂ (kpair.π₂ (kpair.π₂ x))

instance woodinStageCode_definable : ℒₛₑₜ-function₄[V] woodinStageCode := by unfold woodinStageCode; definability
instance woodinStagePoset_definable : ℒₛₑₜ-function₁[V] woodinStagePoset := by unfold woodinStagePoset; definability
instance woodinStageOrder_definable : ℒₛₑₜ-function₁[V] woodinStageOrder := by unfold woodinStageOrder; definability
instance woodinStageTop_definable : ℒₛₑₜ-function₁[V] woodinStageTop := by unfold woodinStageTop; definability
instance woodinStageCardinal_definable : ℒₛₑₜ-function₁[V] woodinStageCardinal := by unfold woodinStageCardinal; definability

@[simp] theorem woodinStagePoset_code (P R one κ : V) : woodinStagePoset (woodinStageCode P R one κ) = P := by
  simp [woodinStagePoset, woodinStageCode]
@[simp] theorem woodinStageOrder_code (P R one κ : V) : woodinStageOrder (woodinStageCode P R one κ) = R := by
  simp [woodinStageOrder, woodinStageCode]
@[simp] theorem woodinStageTop_code (P R one κ : V) : woodinStageTop (woodinStageCode P R one κ) = one := by
  simp [woodinStageTop, woodinStageCode]
@[simp] theorem woodinStageCardinal_code (P R one κ : V) : woodinStageCardinal (woodinStageCode P R one κ) = κ := by
  simp [woodinStageCardinal, woodinStageCode]

noncomputable def woodinSuccessorAt (P R one κ δ : V) : V :=
  woodinStageCode
    (twoStepConditions P R (saturatedWoodinPrefixPosetName P R one κ δ) ∅)
    (twoStepOrder P R (saturatedWoodinPrefixPosetName P R one κ δ) (saturatedWoodinPrefixOrderName P R one κ δ)
      ∅) ⟨one, ∅⟩ₖ δ

noncomputable def woodinSuccessorStep (x : V) : V :=
  woodinSuccessorAt (woodinStagePoset x) (woodinStageOrder x) (woodinStageTop x) (woodinStageCardinal x)
    (woodinPrefixCutoff (woodinStagePoset x) (woodinStageOrder x) (woodinStageTop x) (woodinStageCardinal x))

instance woodinSuccessorAt_definable : Language.DefinableFunction ℒₛₑₜ
    (fun v : Fin 5 → V ↦ woodinSuccessorAt (v 0) (v 1) (v 2) (v 3) (v 4)) := by
  unfold woodinSuccessorAt
  apply Language.DefinableFunction₄.comp
  · apply Language.DefinableFunction₄.comp
    · definability
    · definability
    · exact saturatedWoodinPrefixPosetName_definable
    · definability
  · apply Language.DefinableFunction₅.comp
    · definability
    · definability
    · exact saturatedWoodinPrefixPosetName_definable
    · exact saturatedWoodinPrefixOrderName_definable
    · definability
  · definability
  · definability

instance woodinSuccessorStep_definable : ℒₛₑₜ-function₁[V] woodinSuccessorStep := by
  unfold woodinSuccessorStep
  apply Language.DefinableFunction₅.comp
  · definability
  · definability
  · definability
  · definability
  · apply Language.DefinableFunction₄.comp <;> definability

@[simp] theorem woodinSuccessorStep_code (P R one κ : V) :
    woodinSuccessorStep (woodinStageCode P R one κ) =
      woodinSuccessorAt P R one κ (woodinPrefixCutoff P R one κ) := by
  simp [woodinSuccessorStep]

end ZFVP
