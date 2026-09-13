import ZFVP.ModelTheory.LimitCodeDefinability
import ZFVP.ModelTheory.WoodinInverseStageBounds
import ZFVP.ModelTheory.ForcingHartogsUniform

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinCollapseNameUniformFormula : SetTheorySemisentence 5 :=
  f“Q P R κ δ. !(formulaUniqueNameFormula totalWoodinCollapseFormula) Q P R
    (!assignmentPrependFormula (!(numeralFormula 1))
      (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) δ) κ)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

private theorem namedPrefixCutoff_comp {n : ℕ}
    {a b c d e f : (Fin n → V) → V}
    (ha : Language.DefinableFunction ℒₛₑₜ a) (hb : Language.DefinableFunction ℒₛₑₜ b)
    (hc : Language.DefinableFunction ℒₛₑₜ c) (hd : Language.DefinableFunction ℒₛₑₜ d)
    (he : Language.DefinableFunction ℒₛₑₜ e) (hf : Language.DefinableFunction ℒₛₑₜ f) :
    Language.Definable ℒₛₑₜ (fun v ↦ IsWoodinNamedPrefixCutoff (a v) (b v) (c v) (d v) (e v) (f v)) :=
  Language.Definable.substitution (f := ![a, b, c, d, e, f]) woodinNamedPrefixCutoff_definable
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, ha, hb, hc, hd, he, hf])

attribute [local aesop 5 (rule_sets := [Definability]) safe] namedPrefixCutoff_comp

instance woodinNamedPrefixCutoff_uniform_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (woodinNamedPrefixCutoff (V := V)) := by
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun c P R o γ τ : V ↦
      IsLeastOrdinal (IsWoodinNamedPrefixCutoff P R o γ τ) c ∨
        (¬∃ δ, IsOrdinal δ ∧ IsWoodinNamedPrefixCutoff P R o γ τ δ) ∧ c = 0) := by
    unfold IsLeastOrdinal
    definability
  apply Language.Definable.of_iff h
  intro v
  exact leastOrdinalOrZero_eq_iff
    (fun γ δ ↦ IsWoodinNamedPrefixCutoff (v 1) (v 2) (v 3) γ (v 5) δ)
    (by definability) (v 4) (v 0)
instance forcingInverseCodePoset_definable : ℒₛₑₜ-function₂[V] forcingInverseCodePoset := by
  unfold forcingInverseCodePoset
  definability

instance forcingInverseCodeOrder_definable : ℒₛₑₜ-function₂[V] forcingInverseCodeOrder := by
  unfold forcingInverseCodeOrder
  definability

instance forcingInverseCodeTop_definable : ℒₛₑₜ-function₂[V] forcingInverseCodeTop := by
  unfold forcingInverseCodeTop
  definability

instance forcingInverseHartogsName_definable : ℒₛₑₜ-function₃[V] forcingInverseHartogsName := by
  unfold forcingInverseHartogsName
  definability

instance forcingInverseSourceCutoff_definable : ℒₛₑₜ-function₃[V] forcingInverseSourceCutoff := by
  unfold forcingInverseSourceCutoff
  definability

instance forcingInverseRestorationName_definable : ℒₛₑₜ-function₃[V] forcingInverseRestorationName := by
  unfold forcingInverseRestorationName
  definability

instance woodinCollapseName_uniform_definable : ℒₛₑₜ-function₄[V] woodinCollapseName := by
  have h : ℒₛₑₜ-function₄[V] woodinCollapseName via woodinCollapseNameUniformFormula :=
    ⟨fun v ↦ by simp [woodinCollapseNameUniformFormula, woodinCollapseName, standardTuple]⟩
  exact h.to_definable

instance reverseInclusionOrderName_uniform_definable : ℒₛₑₜ-function₃[V] reverseInclusionOrderName :=
  reverseInclusionOrderNameFormula_defined.to_definable

instance saturatedWoodinCollapseName_uniform_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (saturatedWoodinCollapseName (V := V)) := by
  unfold saturatedWoodinCollapseName
  apply Language.DefinableFunction₄.comp <;> definability

instance forcingInverseCollapseName_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (forcingInverseCollapseName (V := V)) := by
  unfold forcingInverseCollapseName
  definability

instance forcingInverseCollapseCode_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (forcingInverseCollapseCode (V := V)) := by
  unfold forcingInverseCollapseCode
  dsimp only
  apply Language.DefinableFunction₅.comp <;> definability

instance forcingInverseSourceCollapseCode_definable :
    ℒₛₑₜ-function₄[V] forcingInverseSourceCollapseCode := by
  unfold forcingInverseSourceCollapseCode
  apply Language.DefinableFunction₅.comp <;> definability

instance woodinInverseCardinalNext_definable : ℒₛₑₜ-function₃[V] woodinInverseCardinalNext := by
  unfold woodinInverseCardinalNext
  definability

instance woodinInverseSourceCode_definable : ℒₛₑₜ-function₃[V] woodinInverseSourceCode := by
  unfold woodinInverseSourceCode
  apply Language.DefinableFunction₄.comp <;> definability

end ZFVP
