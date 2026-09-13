import ZFVP.SetTheory.FixedLevyForcing
import ZFVP.SetTheory.SigmaThreeLeastPrefixCutoff

/-! Fixed positive and negative tests for successful prefix cutoffs.
The least-witness certificate has both third-level bounds. The total selector's
default-zero branch is not included in that complexity assertion. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

noncomputable def fixedPiTwoDCForcingFormula : SetTheorySemisentence 5 :=
  checkedLevyForcingFormula
    (fixedOrdinaryForcingFormula piTwoOrdinalDependentChoiceBelowFormula_piTwo (by decide))

theorem fixedPiTwoDCForcingFormula_piTwo : IsPiFormula 2 fixedPiTwoDCForcingFormula :=
  checkedLevyForcingFormula_piTwo
    (fixedOrdinaryForcingFormula_levy piTwoOrdinalDependentChoiceBelowFormula_piTwo (by decide))

noncomputable def fixedPiTwoLocalRestorationFormula : SetTheorySemisentence 2 :=
  piTwoLocalRestorationBody fixedPiTwoDCForcingFormula

theorem fixedPiTwoLocalRestorationFormula_piTwo : IsPiFormula 2 fixedPiTwoLocalRestorationFormula :=
  piTwoLocalRestorationBody_piTwo fixedPiTwoDCForcingFormula_piTwo

noncomputable def fixedPiTwoPrefixForcingFormula : SetTheorySemisentence 6 :=
  checkedBinaryLevyForcingFormula
    (fixedOrdinaryForcingFormula fixedPiTwoLocalRestorationFormula_piTwo (by decide))

theorem fixedPiTwoPrefixForcingFormula_piTwo : IsPiFormula 2 fixedPiTwoPrefixForcingFormula :=
  checkedBinaryLevyForcingFormula_piTwo
    (fixedOrdinaryForcingFormula_levy fixedPiTwoLocalRestorationFormula_piTwo (by decide))

noncomputable def fixedPiTwoPrefixCutoffFormula : SetTheorySemisentence 5 :=
  piTwoPrefixCutoffBody fixedPiTwoPrefixForcingFormula

theorem fixedPiTwoPrefixCutoffFormula_piTwo : IsPiFormula 2 fixedPiTwoPrefixCutoffFormula :=
  piTwoPrefixCutoffBody_piTwo fixedPiTwoPrefixForcingFormula_piTwo

noncomputable def fixedSigmaTwoPrefixFailureFormula : SetTheorySemisentence 5 :=
  ∼fixedPiTwoPrefixCutoffFormula

theorem fixedSigmaTwoPrefixFailureFormula_sigmaTwo : IsSigmaFormula 2 fixedSigmaTwoPrefixFailureFormula :=
  fixedPiTwoPrefixCutoffFormula_piTwo.neg

noncomputable def fixedSigmaTwoSmallerPrefixFailuresFormula : SetTheorySemisentence 5 :=
  “P R one κ δ. ∀ β ∈ δ, !fixedSigmaTwoPrefixFailureFormula P R one κ β”

theorem fixedSigmaTwoSmallerPrefixFailuresFormula_sigmaTwo :
    IsSigmaFormula 2 fixedSigmaTwoSmallerPrefixFailuresFormula :=
  .boundedAll (.bvar 4) (fixedSigmaTwoPrefixFailureFormula_sigmaTwo.subst _)

noncomputable def fixedLeastPrefixCutoffFormula : SetTheorySemisentence 5 :=
  leastPrefixCutoffBody fixedPiTwoPrefixCutoffFormula

theorem fixedLeastPrefixCutoffFormula_levy (pol : LevyPolarity) :
    IsLevyFormula pol 3 fixedLeastPrefixCutoffFormula :=
  leastPrefixCutoffBody_levy fixedPiTwoPrefixCutoffFormula_piTwo pol

/-- Output-first orientation for the successful branch of the actual selector. -/
noncomputable def fixedSuccessfulPrefixSelectorFormula : SetTheorySemisentence 5 :=
  “δ P R one κ. !fixedLeastPrefixCutoffFormula P R one κ δ”

theorem fixedSuccessfulPrefixSelectorFormula_levy (pol : LevyPolarity) :
    IsLevyFormula pol 3 fixedSuccessfulPrefixSelectorFormula :=
  (fixedLeastPrefixCutoffFormula_levy pol).subst _

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_fixedPiTwoDCForcingFormula {P R one p κ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hp : p ∈ P) (hk : IsOrdinal κ) :
    fixedPiTwoDCForcingFormula.Evalb ![P, R, one, p, κ] ↔
      p ∈ forcingFormula P R dependentChoiceBelowFormula (standardTuple ![checkName one κ]) := by
  unfold fixedPiTwoDCForcingFormula
  rw [eval_checkedLevyForcingFormula]
  exact (eval_fixedOrdinaryForcingFormula piTwoOrdinalDependentChoiceBelowFormula_piTwo
    (by decide) hR ![checkName one κ]
    (by intro i; exact Fin.cases (checkName_isName ht.1 κ) (fun j ↦ Fin.elim0 j) i) p).trans
      (forcing_piTwoDependentChoiceBelow_iff hR ht hp hk)

theorem eval_fixedPiTwoLocalRestorationFormula (κ δ : V) (hk : (∅ : V) ∈ κ) :
    fixedPiTwoLocalRestorationFormula.Evalb ![κ, δ] ↔ IsWoodinLocalRestoration κ δ := by
  unfold fixedPiTwoLocalRestorationFormula
  rw [eval_piTwoLocalRestorationBody]
  unfold IsWoodinLocalRestoration
  apply and_congr_right
  intro hd
  exact forall_congr' fun p ↦ forall_congr' fun hp ↦
    eval_fixedPiTwoDCForcingFormula (woodinCollapse_poset κ δ).1 (woodinCollapse_top hk δ) hp hd

theorem eval_fixedPiTwoPrefixForcingFormula {P R one p κ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hp : p ∈ P) (hk : (∅ : V) ∈ κ) :
    fixedPiTwoPrefixForcingFormula.Evalb ![P, R, one, p, κ, δ] ↔
      p ∈ forcingFormula P R woodinLocalRestorationFormula
        (standardTuple ![checkName one κ, checkName one δ]) := by
  unfold fixedPiTwoPrefixForcingFormula
  rw [eval_checkedBinaryLevyForcingFormula]
  have hnames : ∀ i : Fin 2, IsForcingName P (![checkName one κ, checkName one δ] i) := by
    intro i
    exact Fin.cases (checkName_isName ht.1 κ)
      (fun j ↦ Fin.cases (checkName_isName ht.1 δ) (fun k ↦ Fin.elim0 k) j) i
  apply (eval_fixedOrdinaryForcingFormula fixedPiTwoLocalRestorationFormula_piTwo (by decide)
    hR ![checkName one κ, checkName one δ] hnames p).trans
  let guard : SetTheorySemisentence 2 := boundedZeroMemberFormula.subst
    (fun i ↦ .bvar ((![0] : Fin 1 → Fin 2) i))
  let c : Fin 2 → ForcingName P := fun i ↦ ⟨![checkName one κ, checkName one δ] i, hnames i⟩
  have hg : p ∈ forcingFormula P R guard (standardTuple ![checkName one κ, checkName one δ]) := by
    unfold guard
    rw [forcingFormula_rename]
    exact forces_checked_bounded boundedZeroMemberFormula boundedZeroMemberFormula_bounded hR ht
      (by simpa [boundedZeroMemberFormula, Semiformula.Evalb] using hk) hp
  apply forcingFormula_iff_under guard fixedPiTwoLocalRestorationFormula woodinLocalRestorationFormula
    (fun W _ _ _ v hv ↦ ?_) hR ht hp c hg
  have hk' : (∅ : W) ∈ v 0 := by
    simpa [guard, boundedZeroMemberFormula, Semiformula.eval_substs] using hv
  have hv' : ![v 0, v 1] = v := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  rw [← hv']
  exact (eval_fixedPiTwoLocalRestorationFormula (v 0) (v 1) hk').trans
    (woodinLocalRestorationFormula_defined.iff ![v 0, v 1]).symm

theorem eval_fixedPiTwoPrefixCutoffFormula {P R one κ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hk : (∅ : V) ∈ κ) :
    fixedPiTwoPrefixCutoffFormula.Evalb ![P, R, one, κ, δ] ↔ IsWoodinPrefixCutoff P R one κ δ := by
  have hb : fixedPiTwoPrefixCutoffFormula.Evalb ![P, R, one, κ, δ] ↔
      κ ∈ δ ∧ IsChoicelessInaccessible δ ∧
        ∀ p ∈ P, fixedPiTwoPrefixForcingFormula.Evalb ![P, R, one, p, κ, δ] := by
    simp [fixedPiTwoPrefixCutoffFormula, piTwoPrefixCutoffBody, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb,
      rankCriterionHeight_iff_choicelessInaccessible]
  rw [hb]
  unfold IsWoodinPrefixCutoff
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  exact forall_congr' fun p ↦ forall_congr' fun hp ↦ eval_fixedPiTwoPrefixForcingFormula hR ht hp hk

theorem eval_fixedSigmaTwoPrefixFailureFormula {P R one κ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hk : (∅ : V) ∈ κ) :
    fixedSigmaTwoPrefixFailureFormula.Evalb ![P, R, one, κ, δ] ↔
      ¬IsWoodinPrefixCutoff P R one κ δ := by
  simpa [fixedSigmaTwoPrefixFailureFormula, Semiformula.Evalb] using
    not_congr (eval_fixedPiTwoPrefixCutoffFormula (δ := δ) hR ht hk)

theorem eval_fixedSigmaTwoSmallerPrefixFailuresFormula {P R one κ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hk : (∅ : V) ∈ κ) :
    fixedSigmaTwoSmallerPrefixFailuresFormula.Evalb ![P, R, one, κ, δ] ↔
      ∀ β ∈ δ, ¬IsWoodinPrefixCutoff P R one κ β := by
  have hb : fixedSigmaTwoSmallerPrefixFailuresFormula.Evalb ![P, R, one, κ, δ] ↔
      ∀ β ∈ δ, fixedSigmaTwoPrefixFailureFormula.Evalb ![P, R, one, κ, β] := by
    simp [fixedSigmaTwoSmallerPrefixFailuresFormula, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  rw [hb]
  exact forall_congr' fun β ↦ forall_congr' fun _ ↦ eval_fixedSigmaTwoPrefixFailureFormula hR ht hk

theorem eval_fixedLeastPrefixCutoffFormula {P R one κ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hk : (∅ : V) ∈ κ) :
    fixedLeastPrefixCutoffFormula.Evalb ![P, R, one, κ, δ] ↔
      IsLeastOrdinal (IsWoodinPrefixCutoff P R one κ) δ := by
  have hb : fixedLeastPrefixCutoffFormula.Evalb ![P, R, one, κ, δ] ↔
      IsOrdinal δ ∧ fixedPiTwoPrefixCutoffFormula.Evalb ![P, R, one, κ, δ] ∧
        ∀ β ∈ δ, ¬fixedPiTwoPrefixCutoffFormula.Evalb ![P, R, one, κ, β] := by
    simp [fixedLeastPrefixCutoffFormula, leastPrefixCutoffBody, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  rw [hb, isLeastOrdinal_iff_no_smaller]
  simp only [eval_fixedPiTwoPrefixCutoffFormula hR ht hk]

theorem eval_fixedSuccessfulPrefixSelectorFormula {P R one κ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hk : (∅ : V) ∈ κ)
    (hex : ∃ η, IsWoodinPrefixCutoff P R one κ η) :
    fixedSuccessfulPrefixSelectorFormula.Evalb ![δ, P, R, one, κ] ↔
      δ = woodinPrefixCutoff P R one κ := by
  have hb : fixedSuccessfulPrefixSelectorFormula.Evalb ![δ, P, R, one, κ] ↔
      fixedLeastPrefixCutoffFormula.Evalb ![P, R, one, κ, δ] := by
    simp [fixedSuccessfulPrefixSelectorFormula, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  rw [hb, eval_fixedLeastPrefixCutoffFormula hR ht hk]
  exact (woodinPrefixCutoff_eq_iff_least_of_exists hex).symm

end ZFVP
