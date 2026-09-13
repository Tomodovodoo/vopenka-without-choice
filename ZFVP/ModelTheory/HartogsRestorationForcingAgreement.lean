import ZFVP.ModelTheory.HartogsRestorationForcingAgreementCountable
import ZFVP.Syntax.LowRankBinaryForcingTruth
import ZFVP.ModelTheory.CountableZFTransfer
import ZFVP.ModelTheory.ForcingHartogsUniform
import ZFVP.SetTheory.WoodinNamedPrefixCutoff

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def lowRankHartogsBinaryForcingFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 7 :=
  f“P R o ξ p a b. !(lowRankForcingTruthFormula φ) P R ξ ξ p
    (!assignmentPrependFormula (!(numeralFormula 1))
      (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) (!checkNameFormula o b))
      (!hartogsNumberNameFormula P R (!checkNameFormula o a)))”

def hartogsBinaryForcingFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 6 :=
  f“P R o p a b. !(namedCheckedBinaryForcingFormula φ) P R o p
    (!hartogsNumberNameFormula P R (!checkNameFormula o a)) b”

def hartogsRestorationForcingAgreementFormula : SetTheorySemisentence 6 :=
  f“P R o κ γ ξ. ∀ p,
    (!(lowRankHartogsBinaryForcingFormula woodinLocalRestorationFormula) P R o ξ p κ γ ↔
      !(hartogsBinaryForcingFormula woodinLocalRestorationFormula) P R o p κ γ)”

def eventualHartogsRestorationForcingAgreementFormula : SetTheorySemisentence 6 :=
  f“δ κ γ P R o. !woodinSupercompactFormula δ ∧ P ∈ !hierarchyFormula δ ∧ κ ∈ γ ∧ γ ∈ δ ∧
    !choicelessInaccessibleFormula γ ∧ P ∈ !hierarchyFormula γ ∧
    !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    (∀ p ∈ P, !(namedUnaryForcingFormula regularCardinalFormula) P R p (!hartogsNumberNameFormula P R (!checkNameFormula o κ))) →
    ∃ β ∈ δ, γ ∈ β ∧ ∀ ξ, β ∈ ξ → !choicelessInaccessibleFormula ξ →
      P ∈ !hierarchyFormula ξ → !hartogsNumberNameFormula P R (!checkNameFormula o κ) ∈ !hierarchyFormula ξ →
      !checkNameFormula o γ ∈ !hierarchyFormula ξ →
      !hartogsRestorationForcingAgreementFormula P R o κ γ ξ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem forall_six_eq_prefix {W : Type*} (a b c d e f : W)
    (F : W → W → W → W → W → W → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔
      F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

private theorem forall_three_eq_prefix {W : Type*} (a b c : W) (F : W → W → W → Prop) :
    (∀ u v w, u = a → v = b → w = c → F u v w) ↔ F a b c :=
  ⟨fun h ↦ h a b c rfl rfl rfl, fun h u v w hu hv hw ↦ by subst u v w; exact h⟩

private theorem forall_four_eq_prefix {W : Type*} (a b c d : W)
    (F : W → W → W → W → Prop) :
    (∀ u v w x, u = a → v = b → w = c → x = d → F u v w x) ↔ F a b c d :=
  ⟨fun h ↦ h a b c d rfl rfl rfl rfl,
    fun h u v w x hu hv hw hx ↦ by subst u v w x; exact h⟩

instance lowRankHartogsBinaryForcingFormula_defined (φ : SetTheorySemisentence 2) :
    Defined (fun v : Fin 7 → V ↦ v 4 ∈ classForcingFormula (v 0) (v 1)
      (IsLowRankForcingName (v 0) (v 3)) (by definability) φ
      (standardTuple ![hartogsNumberName (v 0) (v 1) (checkName (v 2) (v 5)),
        checkName (v 2) (v 6)])) (lowRankHartogsBinaryForcingFormula φ) :=
  ⟨fun v ↦ by
    simp [lowRankHartogsBinaryForcingFormula, standardTuple, Semiformula.eval_nestFormulae,
      Matrix.vecForall_iff, Fin.forall_fin_succ, forall_six_eq_prefix]⟩

instance hartogsBinaryForcingFormula_defined (φ : SetTheorySemisentence 2) :
    Defined (fun v : Fin 6 → V ↦ v 3 ∈ forcingFormula (v 0) (v 1) φ
      (standardTuple ![hartogsNumberName (v 0) (v 1) (checkName (v 2) (v 4)),
        checkName (v 2) (v 5)])) (hartogsBinaryForcingFormula φ) :=
  ⟨fun v ↦ by
    simp [hartogsBinaryForcingFormula, Semiformula.eval_nestFormulae,
      Matrix.vecForall_iff, Fin.forall_fin_succ, forall_six_eq_prefix]⟩

instance hartogsRestorationForcingAgreementFormula_defined :
    Defined (fun v : Fin 6 → V ↦
      classForcingFormula (v 0) (v 1) (IsLowRankForcingName (v 0) (v 5)) (by definability)
        woodinLocalRestorationFormula (standardTuple ![hartogsNumberName (v 0) (v 1) (checkName (v 2) (v 3)), checkName (v 2) (v 4)]) =
      forcingFormula (v 0) (v 1) woodinLocalRestorationFormula
        (standardTuple ![hartogsNumberName (v 0) (v 1) (checkName (v 2) (v 3)), checkName (v 2) (v 4)]))
      hartogsRestorationForcingAgreementFormula := by
  refine ⟨fun v ↦ ?_⟩
  rw [mem_ext_iff]
  simp [hartogsRestorationForcingAgreementFormula, Semiformula.eval_nestFormulae,
    Matrix.vecForall_iff, Fin.forall_fin_succ]
  apply forall_congr'
  intro p
  have he : (∀ a b c d e f g : V, a = v 0 → b = v 1 → c = v 2 → d = v 5 →
      e = p → f = v 3 → g = v 4 → e ∈ classForcingFormula a b (IsLowRankForcingName a d)
        (by definability) woodinLocalRestorationFormula (standardTuple ![hartogsNumberName a b (checkName c f), checkName c g])) ↔
      p ∈ classForcingFormula (v 0) (v 1) (IsLowRankForcingName (v 0) (v 5)) (by definability)
        woodinLocalRestorationFormula (standardTuple ![hartogsNumberName (v 0) (v 1) (checkName (v 2) (v 3)), checkName (v 2) (v 4)]) := by
    constructor
    · intro h
      exact h _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl
    · rintro h a b c d e f g rfl rfl rfl rfl rfl rfl rfl
      exact h
  have hf : (∀ a b c d e f : V, a = v 0 → b = v 1 → c = v 2 → d = p → e = v 3 → f = v 4 →
      d ∈ forcingFormula a b woodinLocalRestorationFormula (standardTuple ![hartogsNumberName a b (checkName c e), checkName c f])) ↔
      p ∈ forcingFormula (v 0) (v 1) woodinLocalRestorationFormula
        (standardTuple ![hartogsNumberName (v 0) (v 1) (checkName (v 2) (v 3)), checkName (v 2) (v 4)]) := by
    constructor
    · intro h
      exact h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    · rintro h a b c d e f rfl rfl rfl rfl rfl rfl
      exact h
  exact iff_congr he hf

theorem eval_eventualHartogsRestorationForcingAgreementFormula (v : Fin 6 → V) :
    eventualHartogsRestorationForcingAgreementFormula.Evalb v ↔
      (IsWoodinSupercompact (v 0) → v 3 ∈ hierarchy (v 0) → v 1 ∈ v 2 → v 2 ∈ v 0 →
        IsChoicelessInaccessible (v 2) → v 3 ∈ hierarchy (v 2) →
        IsForcingPreorder (v 3) (v 4) → IsForcingTop (v 3) (v 4) (v 5) →
        (∀ p ∈ v 3, p ∈ forcingFormula (v 3) (v 4) regularCardinalFormula
          (standardTuple ![hartogsNumberName (v 3) (v 4) (checkName (v 5) (v 1))])) →
        ∃ β ∈ v 0, v 2 ∈ β ∧ ∀ ξ, β ∈ ξ → IsChoicelessInaccessible ξ →
          v 3 ∈ hierarchy ξ → hartogsNumberName (v 3) (v 4) (checkName (v 5) (v 1)) ∈ hierarchy ξ →
          checkName (v 5) (v 2) ∈ hierarchy ξ →
          classForcingFormula (v 3) (v 4) (IsLowRankForcingName (v 3) ξ) (by definability)
            woodinLocalRestorationFormula (standardTuple ![hartogsNumberName (v 3) (v 4) (checkName (v 5) (v 1)), checkName (v 5) (v 2)]) =
          forcingFormula (v 3) (v 4) woodinLocalRestorationFormula
            (standardTuple ![hartogsNumberName (v 3) (v 4) (checkName (v 5) (v 1)), checkName (v 5) (v 2)])) := by
  simp [eventualHartogsRestorationForcingAgreementFormula, Semiformula.eval_nestFormulae,
    Matrix.vecForall_iff, Fin.forall_fin_succ, forall_six_eq_prefix,
    forall_three_eq_prefix, forall_four_eq_prefix]

theorem eventually_hartogsRestoration_forcing_eq {δ κ γ P R one : V}
    (hδ : IsWoodinSupercompact δ) (hP : P ∈ hierarchy δ) (hκγ : κ ∈ γ) (hγδ : γ ∈ δ)
    (hγ : IsChoicelessInaccessible γ) (hPγ : P ∈ hierarchy γ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![hartogsNumberName P R (checkName one κ)])) :
    ∃ β ∈ δ, γ ∈ β ∧ ∀ ξ, β ∈ ξ → IsChoicelessInaccessible ξ → P ∈ hierarchy ξ →
      hartogsNumberName P R (checkName one κ) ∈ hierarchy ξ → checkName one γ ∈ hierarchy ξ →
      classForcingFormula P R (IsLowRankForcingName P ξ) (by definability)
        woodinLocalRestorationFormula (standardTuple ![hartogsNumberName P R (checkName one κ), checkName one γ]) =
      forcingFormula P R woodinLocalRestorationFormula
        (standardTuple ![hartogsNumberName P R (checkName one κ), checkName one γ]) := by
  have he := eval_of_countable_zf eventualHartogsRestorationForcingAgreementFormula (by
    intro W _ _ _ _ v
    apply (eval_eventualHartogsRestorationForcingAgreementFormula v).mpr
    intro hδ hP hκγ hγδ hγ hPγ hR ht hκ
    exact eventually_hartogsRestoration_forcing_eq_countable hδ hP hκγ hγδ hγ hPγ hR ht hκ)
    ![δ, κ, γ, P, R, one]
  exact (eval_eventualHartogsRestorationForcingAgreementFormula _).mp he hδ hP hκγ hγδ hγ hPγ hR ht hκ

end ZFVP
