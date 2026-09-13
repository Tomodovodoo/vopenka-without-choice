import ZFVP.Syntax.LowRankForcingTruth
import ZFVP.ModelTheory.RankDCForcingAgreementCountable
import ZFVP.ModelTheory.CountableZFTransfer

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def rankDCForcingAgreementFormula : SetTheorySemisentence 5 :=
  f“P R o γ ξ. ∀ p,
    (!(lowRankCheckedUnaryForcingFormula dependentChoiceBelowFormula) P R o ξ p γ ↔
      !(checkedUnaryForcingFormula dependentChoiceBelowFormula) P R o p γ)”

def eventualRankDCForcingAgreementFormula : SetTheorySemisentence 5 :=
  f“δ γ P R o. !woodinSupercompactFormula δ ∧ P ∈ !hierarchyFormula δ ∧ γ ∈ δ ∧
    !forcingPreorderFormula P R ∧ !forcingTopFormula P R o →
    ∃ β ∈ δ, γ ∈ β ∧ ∀ ξ, β ∈ ξ → !choicelessInaccessibleFormula ξ →
      P ∈ !hierarchyFormula ξ → !checkNameFormula o γ ∈ !hierarchyFormula ξ →
      !rankDCForcingAgreementFormula P R o γ ξ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance rankDCForcingAgreementFormula_defined :
    Defined (fun v : Fin 5 → V ↦
      classForcingFormula (v 0) (v 1) (IsLowRankForcingName (v 0) (v 4)) (by definability)
        dependentChoiceBelowFormula (standardTuple ![checkName (v 2) (v 3)]) =
      forcingFormula (v 0) (v 1) dependentChoiceBelowFormula (standardTuple ![checkName (v 2) (v 3)]))
      rankDCForcingAgreementFormula := by
  refine ⟨fun v ↦ ?_⟩
  rw [mem_ext_iff]
  simp [rankDCForcingAgreementFormula, Semiformula.eval_nestFormulae,
    Matrix.vecForall_iff, Fin.forall_fin_succ]
  apply forall_congr'
  intro p
  have he : (∀ a b c d e f : V, a = v 0 → b = v 1 → c = v 2 → d = v 4 → e = p → f = v 3 →
      e ∈ classForcingFormula a b (IsLowRankForcingName a d) (by definability)
        dependentChoiceBelowFormula (standardTuple ![checkName c f])) ↔
      p ∈ classForcingFormula (v 0) (v 1) (IsLowRankForcingName (v 0) (v 4)) (by definability)
        dependentChoiceBelowFormula (standardTuple ![checkName (v 2) (v 3)]) := by
    constructor
    · intro h
      exact h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    · rintro h a b c d e f rfl rfl rfl rfl rfl rfl
      exact h
  have hf : (∀ a b c d e : V, a = v 0 → b = v 1 → c = v 2 → d = p → e = v 3 →
      d ∈ forcingFormula a b dependentChoiceBelowFormula (standardTuple ![checkName c e])) ↔
      p ∈ forcingFormula (v 0) (v 1) dependentChoiceBelowFormula
        (standardTuple ![checkName (v 2) (v 3)]) := by
    constructor
    · intro h
      exact h _ _ _ _ _ rfl rfl rfl rfl rfl
    · rintro h a b c d e rfl rfl rfl rfl rfl
      exact h
  exact iff_congr he hf

theorem eval_eventualRankDCForcingAgreementFormula (v : Fin 5 → V) :
    eventualRankDCForcingAgreementFormula.Evalb v ↔
      (IsWoodinSupercompact (v 0) → v 2 ∈ hierarchy (v 0) → v 1 ∈ v 0 →
        IsForcingPreorder (v 2) (v 3) → IsForcingTop (v 2) (v 3) (v 4) →
        ∃ β ∈ v 0, v 1 ∈ β ∧ ∀ ξ, β ∈ ξ → IsChoicelessInaccessible ξ →
          v 2 ∈ hierarchy ξ → checkName (v 4) (v 1) ∈ hierarchy ξ →
          classForcingFormula (v 2) (v 3) (IsLowRankForcingName (v 2) ξ) (by definability)
            dependentChoiceBelowFormula (standardTuple ![checkName (v 4) (v 1)]) =
          forcingFormula (v 2) (v 3) dependentChoiceBelowFormula (standardTuple ![checkName (v 4) (v 1)])) := by
  simp [eventualRankDCForcingAgreementFormula]

theorem eventually_rankDCBelow_forcing_eq {δ γ P R one : V}
    (hδ : IsWoodinSupercompact δ) (hP : P ∈ hierarchy δ) (hγ : γ ∈ δ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) :
    ∃ β ∈ δ, γ ∈ β ∧ ∀ ξ, β ∈ ξ → IsChoicelessInaccessible ξ → P ∈ hierarchy ξ →
      checkName one γ ∈ hierarchy ξ →
      classForcingFormula P R (IsLowRankForcingName P ξ) (by definability)
        dependentChoiceBelowFormula (standardTuple ![checkName one γ]) =
      forcingFormula P R dependentChoiceBelowFormula (standardTuple ![checkName one γ]) := by
  have he := eval_of_countable_zf eventualRankDCForcingAgreementFormula (by
    intro W _ _ _ _ v
    apply (eval_eventualRankDCForcingAgreementFormula v).mpr
    intro hδ hP hγ hR ht
    exact eventually_rankDCBelow_forcing_eq_countable hδ hP hγ hR ht) ![δ, γ, P, R, one]
  exact (eval_eventualRankDCForcingAgreementFormula _).mp he hδ hP hγ hR ht

end ZFVP
