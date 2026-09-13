import ZFVP.ModelTheory.DeltaOneHistoryTables
import ZFVP.ModelTheory.WoodinIterationRecursion
import ZFVP.SetTheory.BoundedRelationDomain
import ZFVP.SetTheory.DeltaOnePairProjections

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneHistoryExtractFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “G H. ∃ D, !boundedRelationDomainFormula D H ∧ !(graphAssemblyFormula (historyTableValueRow φ)) G D H”

def piOneHistoryExtractFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “G H. ∀ Q, !(sigmaOneHistoryExtractFormula φ) Q H → G = Q”

theorem sigmaOneHistoryExtractFormula_sigmaOne {φ : SetTheorySemisentence 2} (hφ : IsSigmaFormula 1 φ) :
    IsSigmaFormula 1 (sigmaOneHistoryExtractFormula φ) :=
  .exs (.and (.bounded (boundedRelationDomainFormula_bounded.subst _))
    ((graphAssemblyFormula_levy (historyTableValueRow_sigmaOne hφ)).subst _))

theorem piOneHistoryExtractFormula_piOne {φ : SetTheorySemisentence 2} (hφ : IsSigmaFormula 1 φ) :
    IsPiFormula 1 (piOneHistoryExtractFormula φ) :=
  .all (.or ((sigmaOneHistoryExtractFormula_sigmaOne hφ).subst _).neg (.bounded (.rel _ _)))

def sigmaOneWoodinHistoryCodesFormula : SetTheorySemisentence 2 :=
  sigmaOneHistoryExtractFormula sigmaOnePairFirstFormula

def piOneWoodinHistoryCodesFormula : SetTheorySemisentence 2 :=
  piOneHistoryExtractFormula sigmaOnePairFirstFormula

def sigmaOneWoodinHistoryCardinalsFormula : SetTheorySemisentence 2 :=
  sigmaOneHistoryExtractFormula sigmaOnePairSecondFormula

def piOneWoodinHistoryCardinalsFormula : SetTheorySemisentence 2 :=
  piOneHistoryExtractFormula sigmaOnePairSecondFormula

theorem sigmaOneWoodinHistoryCodesFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinHistoryCodesFormula :=
  sigmaOneHistoryExtractFormula_sigmaOne sigmaOnePairFirstFormula_sigmaOne

theorem piOneWoodinHistoryCodesFormula_piOne : IsPiFormula 1 piOneWoodinHistoryCodesFormula :=
  piOneHistoryExtractFormula_piOne sigmaOnePairFirstFormula_sigmaOne

theorem sigmaOneWoodinHistoryCardinalsFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinHistoryCardinalsFormula :=
  sigmaOneHistoryExtractFormula_sigmaOne sigmaOnePairSecondFormula_sigmaOne

theorem piOneWoodinHistoryCardinalsFormula_piOne : IsPiFormula 1 piOneWoodinHistoryCardinalsFormula :=
  piOneHistoryExtractFormula_piOne sigmaOnePairSecondFormula_sigmaOne

def historyValueIdentityFormula : SetTheorySemisentence 2 := “y x. y = x”

def sigmaOneWoodinHistoryCardinalUnionFormula : SetTheorySemisentence 3 :=
  sigmaOneHistoryTableFormula historyValueIdentityFormula

def piOneWoodinHistoryCardinalUnionFormula : SetTheorySemisentence 3 :=
  piOneHistoryTableFormula historyValueIdentityFormula

theorem sigmaOneWoodinHistoryCardinalUnionFormula_sigmaOne :
    IsSigmaFormula 1 sigmaOneWoodinHistoryCardinalUnionFormula :=
  sigmaOneHistoryTableFormula_sigmaOne (.bounded (.rel _ _))

theorem piOneWoodinHistoryCardinalUnionFormula_piOne : IsPiFormula 1 piOneWoodinHistoryCardinalUnionFormula :=
  piOneHistoryTableFormula_piOne (.bounded (.rel _ _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sigmaOneHistoryExtractFormula_defined (c : V → V) (φ : SetTheorySemisentence 2)
    [hc : ℒₛₑₜ-function₁ c via φ] :
    ℒₛₑₜ-function₁ (fun H ↦ definableGraph (domain H) (fun i ↦ c (H ‘ i))
      (by have := hc.to_definable; definability)) via sigmaOneHistoryExtractFormula φ :=
  ⟨fun v ↦ by
    have he := eval_historyTableValueGraph c φ (v 0) (domain (v 1)) (v 1)
    simp only [Semiformula.Evalb] at he
    simpa [sigmaOneHistoryExtractFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def] using he⟩

instance piOneHistoryExtractFormula_defined (c : V → V) (φ : SetTheorySemisentence 2)
    [hc : ℒₛₑₜ-function₁ c via φ] :
    ℒₛₑₜ-function₁ (fun H ↦ definableGraph (domain H) (fun i ↦ c (H ‘ i))
      (by have := hc.to_definable; definability)) via piOneHistoryExtractFormula φ :=
  ⟨fun v ↦ by
    simp [piOneHistoryExtractFormula]
    exact ⟨fun h ↦ h _ rfl, fun h _ he ↦ h.trans he.symm⟩⟩

instance sigmaOneWoodinHistoryCodesFormula_defined :
    ℒₛₑₜ-function₁[V] woodinHistoryCodes via sigmaOneWoodinHistoryCodesFormula :=
  sigmaOneHistoryExtractFormula_defined kpair.π₁ sigmaOnePairFirstFormula

instance piOneWoodinHistoryCodesFormula_defined :
    ℒₛₑₜ-function₁[V] woodinHistoryCodes via piOneWoodinHistoryCodesFormula :=
  piOneHistoryExtractFormula_defined kpair.π₁ sigmaOnePairFirstFormula

instance sigmaOneWoodinHistoryCardinalsFormula_defined :
    ℒₛₑₜ-function₁[V] woodinHistoryCardinals via sigmaOneWoodinHistoryCardinalsFormula :=
  sigmaOneHistoryExtractFormula_defined kpair.π₂ sigmaOnePairSecondFormula

instance piOneWoodinHistoryCardinalsFormula_defined :
    ℒₛₑₜ-function₁[V] woodinHistoryCardinals via piOneWoodinHistoryCardinalsFormula :=
  piOneHistoryExtractFormula_defined kpair.π₂ sigmaOnePairSecondFormula

instance historyValueIdentityFormula_defined : ℒₛₑₜ-function₁[V] (fun x ↦ x) via historyValueIdentityFormula :=
  ⟨fun v ↦ by simp [historyValueIdentityFormula]⟩

instance sigmaOneWoodinHistoryCardinalUnionFormula_defined :
    ℒₛₑₜ-function₂[V] woodinHistoryCardinalUnion via sigmaOneWoodinHistoryCardinalUnionFormula :=
  sigmaOneHistoryTableFormula_defined (fun x ↦ x) historyValueIdentityFormula

instance piOneWoodinHistoryCardinalUnionFormula_defined :
    ℒₛₑₜ-function₂[V] woodinHistoryCardinalUnion via piOneWoodinHistoryCardinalUnionFormula :=
  piOneHistoryTableFormula_defined (fun x ↦ x) historyValueIdentityFormula

end ZFVP
