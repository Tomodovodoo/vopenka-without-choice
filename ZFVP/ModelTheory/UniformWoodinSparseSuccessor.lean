import ZFVP.ModelTheory.UniformSparseNormalizedTwoStep
import ZFVP.ModelTheory.WoodinSparseInitial
import ZFVP.ModelTheory.WoodinSparseSuccessor
import ZFVP.ModelTheory.WoodinRecursionUniform
import ZFVP.SetTheory.UniformCodingUniverse

/-! Uniform formulas for the actual initial and successor carrier and order.
These definitions are total, including outside the valid iteration regime. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sparseWoodinSourceIndexFormula : SetTheorySemisentence 2 :=
  f“z α. !ordinalAddFormula z (!(numeralFormula 1)) α”

def woodinSparseInitialCarrierFormula : SetTheorySemisentence 1 :=
  “C. ∃ o, ∃ a, ∃ P, ∃ R, ∃ κ, ∃ δ, ∃ Q,
    !isEmpty o ∧ !succ.dfn a o ∧ !singleton.dfn P o ∧ !prod.dfn R P P ∧
    !woodinSeedCardinalFormula κ ∧ !woodinPrefixCutoffValueFormula δ P R o κ ∧
    !saturatedWoodinPrefixPosetNameFormula Q P R o κ δ ∧
    !sparseNormalizedTwoStepFormula C a P R o δ Q”

def woodinSparseInitialOrderFormula : SetTheorySemisentence 1 :=
  “T. ∃ o, ∃ a, ∃ P, ∃ R, ∃ κ, ∃ δ, ∃ Q, ∃ S,
    !isEmpty o ∧ !succ.dfn a o ∧ !singleton.dfn P o ∧ !prod.dfn R P P ∧
    !woodinSeedCardinalFormula κ ∧ !woodinPrefixCutoffValueFormula δ P R o κ ∧
    !saturatedWoodinPrefixPosetNameFormula Q P R o κ δ ∧
    !saturatedWoodinPrefixOrderNameFormula S P R o κ δ ∧
    !sparseNormalizedTwoStepOrderFormula T a P R o δ Q S”

def woodinSparseInitialMapFormula : SetTheorySemisentence 1 :=
  “f. ∃ o, ∃ a, ∃ P, ∃ R, ∃ κ, ∃ δ, ∃ Q, ∃ W,
    !isEmpty o ∧ !succ.dfn a o ∧ !singleton.dfn P o ∧ !prod.dfn R P P ∧
    !woodinSeedCardinalFormula κ ∧ !woodinPrefixCutoffValueFormula δ P R o κ ∧
    !saturatedWoodinPrefixPosetNameFormula Q P R o κ δ ∧
    !normalizedNamePoolFormula W P R o δ Q ∧ !sparsePairEncodeFormula f a P W”

def woodinSparseSuccessorParametersFormula : SetTheorySemisentence 6 :=
  f“P R o κ k c. P = !value.dfn (!forcingCodePFormula c) k ∧
    R = !value.dfn (!forcingCodeRFormula c) k ∧
    o = !value.dfn (!forcingCodetFormula c) k ∧
    κ = !value.dfn (!kpair.π₂.dfn (!woodinIterationRecFormula k)) k”

def woodinSparseSuccessorPoolFormula : SetTheorySemisentence 3 :=
  “W k c. ∃ P, ∃ R, ∃ o, ∃ κ, ∃ δ, ∃ Q,
    !woodinSparseSuccessorParametersFormula P R o κ k c ∧
    !woodinPrefixCutoffValueFormula δ P R o κ ∧
    !saturatedWoodinPrefixPosetNameFormula Q P R o κ δ ∧
    !normalizedNamePoolFormula W P R o δ Q”

def woodinSparseSuccessorCarrierFormula : SetTheorySemisentence 3 :=
  f“C k c. ∃ a, ∃ W, !sparseWoodinSourceIndexFormula a (!succ.dfn k) ∧
    !woodinSparseSuccessorPoolFormula W k c ∧
    !sparsePairCarrierFormula C a (!value.dfn (!forcingCodePFormula c) k) W”

def woodinSparseRecodedSuccessorCarrierFormula : SetTheorySemisentence 3 :=
  “C k c. ∃ P, ∃ R, ∃ o, ∃ κ, ∃ δ, ∃ Q,
    !woodinSparseSuccessorParametersFormula P R o κ k c ∧
    !woodinPrefixCutoffValueFormula δ P R o κ ∧
    !saturatedWoodinPrefixPosetNameFormula Q P R o κ δ ∧
    !normalizedNameTwoStepFormula C P R o δ Q”

def woodinSparseRecodedSuccessorOrderFormula : SetTheorySemisentence 3 :=
  “T k c. ∃ P, ∃ R, ∃ o, ∃ κ, ∃ δ, ∃ S, ∃ C,
    !woodinSparseSuccessorParametersFormula P R o κ k c ∧
    !woodinPrefixCutoffValueFormula δ P R o κ ∧
    !saturatedWoodinPrefixOrderNameFormula S P R o κ δ ∧
    !woodinSparseRecodedSuccessorCarrierFormula C k c ∧ !nameTwoStepOrderOnFormula T P R S C”

def woodinSparseSuccessorOrderFormula : SetTheorySemisentence 3 :=
  f“T k c. ∃ a, ∃ W, ∃ C, ∃ O, ∃ f,
    !sparseWoodinSourceIndexFormula a (!succ.dfn k) ∧
    !woodinSparseSuccessorPoolFormula W k c ∧
    !woodinSparseSuccessorCarrierFormula C k c ∧ !woodinSparseRecodedSuccessorOrderFormula O k c ∧
    !sparsePairDecodeFormula f a (!value.dfn (!forcingCodePFormula c) k) W ∧
    !sparsePullbackOrderFormula T C O f”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sparseWoodinSourceIndexFormula_defined :
    ℒₛₑₜ-function₁[V] woodinSourceIndex via sparseWoodinSourceIndexFormula :=
  ⟨fun v ↦ by simp [sparseWoodinSourceIndexFormula, woodinSourceIndex]⟩

instance woodinSparseInitialCarrierFormula_defined :
    ℒₛₑₜ-function₀[V] woodinSparseInitialCarrier via woodinSparseInitialCarrierFormula :=
  ⟨fun v ↦ by simp [woodinSparseInitialCarrierFormula, woodinSparseInitialCarrier,
    isEmpty_iff_eq_empty]⟩

instance woodinSparseInitialOrderFormula_defined :
    ℒₛₑₜ-function₀[V] woodinSparseInitialOrder via woodinSparseInitialOrderFormula :=
  ⟨fun v ↦ by simp [woodinSparseInitialOrderFormula, woodinSparseInitialOrder,
    isEmpty_iff_eq_empty]⟩

instance woodinSparseInitialMapFormula_defined :
    ℒₛₑₜ-function₀[V] woodinSparseInitialMap via woodinSparseInitialMapFormula :=
  ⟨fun v ↦ by simp [woodinSparseInitialMapFormula, woodinSparseInitialMap,
    isEmpty_iff_eq_empty]⟩

instance woodinSparseSuccessorParametersFormula_defined :
    Defined (fun v : Fin 6 → V ↦
      v 0 = (forcingCodeP (v 5)) ‘ (v 4) ∧ v 1 = (forcingCodeR (v 5)) ‘ (v 4) ∧
      v 2 = (forcingCodet (v 5)) ‘ (v 4) ∧
      v 3 = (kpair.π₂ (woodinIterationRec (v 4))) ‘ (v 4)) woodinSparseSuccessorParametersFormula :=
  ⟨fun v ↦ by simp [woodinSparseSuccessorParametersFormula]⟩

instance woodinSparseSuccessorPoolFormula_defined :
    ℒₛₑₜ-function₂[V] woodinSparseSuccessorPool via woodinSparseSuccessorPoolFormula :=
  ⟨fun v ↦ by simp [woodinSparseSuccessorPoolFormula, woodinSparseSuccessorPool]⟩

instance woodinSparseSuccessorCarrierFormula_defined :
    ℒₛₑₜ-function₂[V] woodinSparseSuccessorCarrier via woodinSparseSuccessorCarrierFormula :=
  ⟨fun v ↦ by simp [woodinSparseSuccessorCarrierFormula, woodinSparseSuccessorCarrier]⟩

instance woodinSparseRecodedSuccessorCarrierFormula_defined :
    ℒₛₑₜ-function₂[V] woodinRecodedSuccessorCarrier via woodinSparseRecodedSuccessorCarrierFormula :=
  ⟨fun v ↦ by simp [woodinSparseRecodedSuccessorCarrierFormula, woodinRecodedSuccessorCarrier]⟩

instance woodinSparseRecodedSuccessorOrderFormula_defined :
    ℒₛₑₜ-function₂[V] woodinRecodedSuccessorOrder via woodinSparseRecodedSuccessorOrderFormula :=
  ⟨fun v ↦ by simp [woodinSparseRecodedSuccessorOrderFormula, woodinRecodedSuccessorOrder]⟩

instance woodinSparseSuccessorOrderFormula_defined :
    ℒₛₑₜ-function₂[V] woodinSparseSuccessorOrder via woodinSparseSuccessorOrderFormula :=
  ⟨fun v ↦ by simp [woodinSparseSuccessorOrderFormula, woodinSparseSuccessorOrder]⟩

def woodinSparseSuccessorDictionary : SetFormulaDictionary :=
  [⟨2, sparseWoodinSourceIndexFormula⟩, ⟨1, woodinSparseInitialCarrierFormula⟩,
   ⟨1, woodinSparseInitialOrderFormula⟩, ⟨1, woodinSparseInitialMapFormula⟩,
   ⟨6, woodinSparseSuccessorParametersFormula⟩, ⟨3, woodinSparseSuccessorPoolFormula⟩,
   ⟨3, woodinSparseSuccessorCarrierFormula⟩, ⟨3, woodinSparseRecodedSuccessorCarrierFormula⟩,
   ⟨3, woodinSparseRecodedSuccessorOrderFormula⟩, ⟨3, woodinSparseSuccessorOrderFormula⟩]

def woodinSparseSuccessorDictionaryBound : ℕ :=
  levyDictionaryBound woodinSparseSuccessorDictionary

theorem woodinSparseSuccessorDictionary_complexity {n : ℕ}
    {φ : SetTheorySemisentence n} (hφ : ⟨n, φ⟩ ∈ woodinSparseSuccessorDictionary)
    (p : LevyPolarity) : IsLevyFormula p woodinSparseSuccessorDictionaryBound φ :=
  isLevyFormula_dictionaryBound _ hφ p

end ZFVP
