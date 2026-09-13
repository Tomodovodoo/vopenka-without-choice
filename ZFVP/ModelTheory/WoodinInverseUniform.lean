import ZFVP.ModelTheory.WoodinStageUniform

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def forcingInverseCodePosetFormula : SetTheorySemisentence 3 :=
  f“z θ s. !forcingInverseLimitFormula z θ (!forcingCodePFormula s)
    (!forcingCodeπFormula s) (!forcingCodeUniverseFormula s)”

@[irreducible] def forcingInverseCodeOrderFormula : SetTheorySemisentence 3 :=
  f“z θ s. !forcingThreadOrderFormula z θ (!forcingCodeRFormula s) (!forcingInverseCodePosetFormula θ s)”

@[irreducible] def forcingInverseCodeTopFormula : SetTheorySemisentence 3 :=
  f“z θ s. !forcingSectionThreadFormula z θ (!forcingCodeπFormula s) (!forcingCodeEFormula s)
    (!isEmpty) (!value.dfn (!forcingCodetFormula s) (!isEmpty))”

@[irreducible] def forcingInverseHartogsNameFormula : SetTheorySemisentence 4 :=
  f“z θ s γ. !hartogsNumberNameFormula z (!forcingInverseCodePosetFormula θ s)
    (!forcingInverseCodeOrderFormula θ s) (!checkNameFormula (!forcingInverseCodeTopFormula θ s) γ)”

@[irreducible] def forcingInverseSourceCutoffFormula : SetTheorySemisentence 4 :=
  f“z θ s γ. !woodinNamedPrefixCutoffValueFormula z (!forcingInverseCodePosetFormula θ s)
    (!forcingInverseCodeOrderFormula θ s) (!forcingInverseCodeTopFormula θ s) γ (!forcingInverseHartogsNameFormula θ s γ)”

@[irreducible] def woodinInverseCardinalNextFormula : SetTheorySemisentence 4 :=
  f“z θ s K. !forcingFamilyNextFormula z θ K (!forcingInverseSourceCutoffFormula θ s (!woodinLimitCardinalFormula K))”

@[irreducible] def woodinInverseSourceCodeFormula : SetTheorySemisentence 4 :=
  f“z θ s K. ∀ γ, !woodinLimitCardinalFormula γ K →
    ∀ c, !forcingInverseSourceCutoffFormula c θ s γ →
    !forcingInverseTwoStepCodeFormula z θ s
      (!saturatedHartogsPosetNameFormula (!forcingInverseCodePosetFormula θ s)
        (!forcingInverseCodeOrderFormula θ s) (!forcingInverseCodeTopFormula θ s) γ c)
      (!saturatedHartogsOrderNameFormula (!forcingInverseCodePosetFormula θ s)
        (!forcingInverseCodeOrderFormula θ s) (!forcingInverseCodeTopFormula θ s) γ c) (!isEmpty)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingInverseCodePosetFormula_defined : ℒₛₑₜ-function₂[V] forcingInverseCodePoset via forcingInverseCodePosetFormula :=
  ⟨fun v ↦ by simp [forcingInverseCodePosetFormula, forcingInverseCodePoset]⟩

instance forcingInverseCodeOrderFormula_defined : ℒₛₑₜ-function₂[V] forcingInverseCodeOrder via forcingInverseCodeOrderFormula :=
  ⟨fun v ↦ by simp [forcingInverseCodeOrderFormula, forcingInverseCodeOrder]⟩

instance forcingInverseCodeTopFormula_defined : ℒₛₑₜ-function₂[V] forcingInverseCodeTop via forcingInverseCodeTopFormula :=
  ⟨fun v ↦ by simp [forcingInverseCodeTopFormula, forcingInverseCodeTop]⟩

instance forcingInverseHartogsNameFormula_defined : ℒₛₑₜ-function₃[V] forcingInverseHartogsName via forcingInverseHartogsNameFormula :=
  ⟨fun v ↦ by simp [forcingInverseHartogsNameFormula, forcingInverseHartogsName]⟩

instance forcingInverseSourceCutoffFormula_defined : ℒₛₑₜ-function₃[V] forcingInverseSourceCutoff via forcingInverseSourceCutoffFormula :=
  ⟨fun v ↦ by simp [forcingInverseSourceCutoffFormula, forcingInverseSourceCutoff]⟩

instance woodinInverseCardinalNextFormula_defined : ℒₛₑₜ-function₃[V] woodinInverseCardinalNext via woodinInverseCardinalNextFormula :=
  ⟨fun v ↦ by simp [woodinInverseCardinalNextFormula, woodinInverseCardinalNext]⟩

instance woodinInverseSourceCodeFormula_defined : ℒₛₑₜ-function₃[V] woodinInverseSourceCode via woodinInverseSourceCodeFormula :=
  ⟨fun v ↦ by simp [woodinInverseSourceCodeFormula, woodinInverseSourceCode, forcingInverseSourceCollapseCode, forcingInverseCollapseCode, forcingInverseCollapseName, saturatedHartogsPosetName, saturatedHartogsOrderName, forcingInverseRestorationName, forcingInverseHartogsName]⟩

end ZFVP
