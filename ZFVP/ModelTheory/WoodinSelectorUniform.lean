import ZFVP.ModelTheory.ForcingInverseTwoStepUniform
import ZFVP.ModelTheory.WoodinInverseCodeDefinability
import ZFVP.SetTheory.WoodinSeedCardinal

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def woodinPrefixCutoffValueFormula : SetTheorySemisentence 5 :=
  f“z P R o κ. (!IsOrdinal.dfn z ∧ !woodinPrefixCutoffFormula P R o κ z ∧
    ∀ y, !IsOrdinal.dfn y → !woodinPrefixCutoffFormula P R o κ y → z ⊆ y) ∨
    ((∀ y, !IsOrdinal.dfn y → ¬!woodinPrefixCutoffFormula P R o κ y) ∧ !isEmpty z)”

@[irreducible] def woodinNamedPrefixCutoffValueFormula : SetTheorySemisentence 6 :=
  f“z P R o γ τ. (!IsOrdinal.dfn z ∧ !woodinNamedPrefixCutoffFormula P R o γ τ z ∧
    ∀ y, !IsOrdinal.dfn y → !woodinNamedPrefixCutoffFormula P R o γ τ y → z ⊆ y) ∨
    ((∀ y, !IsOrdinal.dfn y → ¬!woodinNamedPrefixCutoffFormula P R o γ τ y) ∧ !isEmpty z)”

@[irreducible] def woodinLeastDCFailureFormula : SetTheorySemisentence 1 :=
  f“z. (!IsOrdinal.dfn z ∧ ¬!dependentChoiceAtFormula z ∧
    ∀ y, !IsOrdinal.dfn y → ¬!dependentChoiceAtFormula y → z ⊆ y) ∨
    ((∀ y, !IsOrdinal.dfn y → !dependentChoiceAtFormula y) ∧ !isEmpty z)”

@[irreducible] def woodinSeedCardinalFormula : SetTheorySemisentence 1 :=
  f“z. ∀ c, !woodinLeastDCFailureFormula c →
    ((c = !isEmpty ∧ !isω z) ∨ (c ≠ !isEmpty ∧ z = c))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinPrefixCutoffValueFormula_defined :
    ℒₛₑₜ-function₄[V] woodinPrefixCutoff via woodinPrefixCutoffValueFormula := by
  refine ⟨fun v ↦ ?_⟩
  change woodinPrefixCutoffValueFormula.Evalb v ↔ v 0 = woodinPrefixCutoff (v 1) (v 2) (v 3) (v 4)
  have he : v 0 = woodinPrefixCutoff (v 1) (v 2) (v 3) (v 4) ↔
      IsLeastOrdinal (IsWoodinPrefixCutoff (v 1) (v 2) (v 3) (v 4)) (v 0) ∨
        (¬∃ y, IsOrdinal y ∧ IsWoodinPrefixCutoff (v 1) (v 2) (v 3) (v 4) y) ∧ v 0 = 0 :=
    leastOrdinalOrZero_eq_iff (IsWoodinPrefixCutoff (v 1) (v 2) (v 3)) (by definability) (v 4) (v 0)
  rw [he]
  simp [woodinPrefixCutoffValueFormula, IsLeastOrdinal, zero_def]

instance woodinNamedPrefixCutoffValueFormula_defined :
    ℒₛₑₜ-function₅[V] woodinNamedPrefixCutoff via woodinNamedPrefixCutoffValueFormula := by
  refine ⟨fun v ↦ ?_⟩
  change woodinNamedPrefixCutoffValueFormula.Evalb v ↔
    v 0 = woodinNamedPrefixCutoff (v 1) (v 2) (v 3) (v 4) (v 5)
  have he : v 0 = woodinNamedPrefixCutoff (v 1) (v 2) (v 3) (v 4) (v 5) ↔
      IsLeastOrdinal (IsWoodinNamedPrefixCutoff (v 1) (v 2) (v 3) (v 4) (v 5)) (v 0) ∨
        (¬∃ y, IsOrdinal y ∧ IsWoodinNamedPrefixCutoff (v 1) (v 2) (v 3) (v 4) (v 5) y) ∧ v 0 = 0 :=
    leastOrdinalOrZero_eq_iff (fun γ y ↦ IsWoodinNamedPrefixCutoff (v 1) (v 2) (v 3) γ (v 5) y)
      (by definability) (v 4) (v 0)
  rw [he]
  simp [woodinNamedPrefixCutoffValueFormula, IsLeastOrdinal, zero_def]

instance woodinLeastDCFailureFormula_defined :
    ℒₛₑₜ-function₀[V] woodinLeastDCFailure via woodinLeastDCFailureFormula := by
  refine ⟨fun v ↦ ?_⟩
  change woodinLeastDCFailureFormula.Evalb v ↔ v 0 = woodinLeastDCFailure
  rw [woodinLeastDCFailure, leastOrdinalOrZero_eq_iff]
  simp [woodinLeastDCFailureFormula, IsLeastOrdinal, zero_def]

instance woodinSeedCardinalFormula_defined :
    ℒₛₑₜ-function₀[V] woodinSeedCardinal via woodinSeedCardinalFormula := by
  refine ⟨fun v ↦ ?_⟩
  classical
  by_cases h : (woodinLeastDCFailure : V) = ∅ <;> simp [woodinSeedCardinalFormula, woodinSeedCardinal, h]
  exact fun _ ↦ not_isEmpty_iff_isNonempty.mp (fun he ↦ h (isEmpty_iff_eq_empty.mp he))

end ZFVP
