import ZFVP.ModelTheory.PrefixRestorationForcingAgreementCountable
import ZFVP.Syntax.LowRankBinaryForcingTruth
import ZFVP.ModelTheory.CountableZFTransfer

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def prefixRestorationForcingAgreementFormula : SetTheorySemisentence 6 :=
  f“P R o κ γ ξ. ∀ p,
    (!(lowRankCheckedBinaryForcingFormula woodinLocalRestorationFormula) P R o ξ p κ γ ↔
      !(checkedBinaryForcingFormula woodinLocalRestorationFormula) P R o p κ γ)”

def eventualPrefixRestorationForcingAgreementFormula : SetTheorySemisentence 6 :=
  f“δ κ γ P R o. !woodinSupercompactFormula δ ∧ P ∈ !hierarchyFormula δ ∧ κ ∈ δ ∧ γ ∈ δ ∧
    !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    (∀ p ∈ P, !(checkedUnaryForcingFormula regularCardinalFormula) P R o p κ) →
    ∃ β ∈ δ, γ ∈ β ∧ ∀ ξ, β ∈ ξ → !choicelessInaccessibleFormula ξ →
      P ∈ !hierarchyFormula ξ → !checkNameFormula o κ ∈ !hierarchyFormula ξ →
      !checkNameFormula o γ ∈ !hierarchyFormula ξ →
      !prefixRestorationForcingAgreementFormula P R o κ γ ξ”

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

private theorem forall_five_eq_prefix {W : Type*} (a b c d e : W)
    (F : W → W → W → W → W → Prop) :
    (∀ u v w x y, u = a → v = b → w = c → x = d → y = e → F u v w x y) ↔ F a b c d e :=
  ⟨fun h ↦ h a b c d e rfl rfl rfl rfl rfl,
    fun h u v w x y hu hv hw hx hy ↦ by subst u v w x y; exact h⟩

instance prefixRestorationForcingAgreementFormula_defined :
    Defined (fun v : Fin 6 → V ↦
      classForcingFormula (v 0) (v 1) (IsLowRankForcingName (v 0) (v 5)) (by definability)
        woodinLocalRestorationFormula (standardTuple ![checkName (v 2) (v 3), checkName (v 2) (v 4)]) =
      forcingFormula (v 0) (v 1) woodinLocalRestorationFormula
        (standardTuple ![checkName (v 2) (v 3), checkName (v 2) (v 4)]))
      prefixRestorationForcingAgreementFormula := by
  refine ⟨fun v ↦ ?_⟩
  rw [mem_ext_iff]
  simp [prefixRestorationForcingAgreementFormula, Semiformula.eval_nestFormulae,
    Matrix.vecForall_iff, Fin.forall_fin_succ]
  apply forall_congr'
  intro p
  have he : (∀ a b c d e f g : V, a = v 0 → b = v 1 → c = v 2 → d = v 5 →
      e = p → f = v 3 → g = v 4 → e ∈ classForcingFormula a b (IsLowRankForcingName a d)
        (by definability) woodinLocalRestorationFormula (standardTuple ![checkName c f, checkName c g])) ↔
      p ∈ classForcingFormula (v 0) (v 1) (IsLowRankForcingName (v 0) (v 5)) (by definability)
        woodinLocalRestorationFormula (standardTuple ![checkName (v 2) (v 3), checkName (v 2) (v 4)]) := by
    constructor
    · intro h
      exact h _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl
    · rintro h a b c d e f g rfl rfl rfl rfl rfl rfl rfl
      exact h
  have hf : (∀ a b c d e f : V, a = v 0 → b = v 1 → c = v 2 → d = p → e = v 3 → f = v 4 →
      d ∈ forcingFormula a b woodinLocalRestorationFormula (standardTuple ![checkName c e, checkName c f])) ↔
      p ∈ forcingFormula (v 0) (v 1) woodinLocalRestorationFormula
        (standardTuple ![checkName (v 2) (v 3), checkName (v 2) (v 4)]) := by
    constructor
    · intro h
      exact h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    · rintro h a b c d e f rfl rfl rfl rfl rfl rfl
      exact h
  exact iff_congr he hf

theorem eval_eventualPrefixRestorationForcingAgreementFormula (v : Fin 6 → V) :
    eventualPrefixRestorationForcingAgreementFormula.Evalb v ↔
      (IsWoodinSupercompact (v 0) → v 3 ∈ hierarchy (v 0) → v 1 ∈ v 0 → v 2 ∈ v 0 →
        IsForcingPreorder (v 3) (v 4) → IsForcingTop (v 3) (v 4) (v 5) →
        (∀ p ∈ v 3, p ∈ forcingFormula (v 3) (v 4) regularCardinalFormula
          (standardTuple ![checkName (v 5) (v 1)])) →
        ∃ β ∈ v 0, v 2 ∈ β ∧ ∀ ξ, β ∈ ξ → IsChoicelessInaccessible ξ →
          v 3 ∈ hierarchy ξ → checkName (v 5) (v 1) ∈ hierarchy ξ →
          checkName (v 5) (v 2) ∈ hierarchy ξ →
          classForcingFormula (v 3) (v 4) (IsLowRankForcingName (v 3) ξ) (by definability)
            woodinLocalRestorationFormula (standardTuple ![checkName (v 5) (v 1), checkName (v 5) (v 2)]) =
          forcingFormula (v 3) (v 4) woodinLocalRestorationFormula
            (standardTuple ![checkName (v 5) (v 1), checkName (v 5) (v 2)])) := by
  simp [eventualPrefixRestorationForcingAgreementFormula, Semiformula.eval_nestFormulae,
    Matrix.vecForall_iff, Fin.forall_fin_succ, forall_six_eq_prefix,
    forall_three_eq_prefix, forall_five_eq_prefix]

theorem eventually_prefixRestoration_forcing_eq {δ κ γ P R one : V}
    (hδ : IsWoodinSupercompact δ) (hP : P ∈ hierarchy δ) (hκδ : κ ∈ δ) (hγδ : γ ∈ δ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![checkName one κ])) :
    ∃ β ∈ δ, γ ∈ β ∧ ∀ ξ, β ∈ ξ → IsChoicelessInaccessible ξ → P ∈ hierarchy ξ →
      checkName one κ ∈ hierarchy ξ → checkName one γ ∈ hierarchy ξ →
      classForcingFormula P R (IsLowRankForcingName P ξ) (by definability)
        woodinLocalRestorationFormula (standardTuple ![checkName one κ, checkName one γ]) =
      forcingFormula P R woodinLocalRestorationFormula
        (standardTuple ![checkName one κ, checkName one γ]) := by
  have he := eval_of_countable_zf eventualPrefixRestorationForcingAgreementFormula (by
    intro W _ _ _ _ v
    apply (eval_eventualPrefixRestorationForcingAgreementFormula v).mpr
    intro hδ hP hκδ hγδ hR ht hκ
    exact eventually_prefixRestoration_forcing_eq_countable hδ hP hκδ hγδ hR ht hκ)
    ![δ, κ, γ, P, R, one]
  exact (eval_eventualPrefixRestorationForcingAgreementFormula _).mp he hδ hP hκδ hγδ hR ht hκ

end ZFVP
