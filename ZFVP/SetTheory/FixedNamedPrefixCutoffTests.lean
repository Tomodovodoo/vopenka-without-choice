import ZFVP.SetTheory.FixedPrefixCutoffTests
import ZFVP.SetTheory.PiTwoNamedPrefixCutoff

/-! Fixed tests for the named-parameter restoration cutoff. The positive test is
Π₂, bounded smaller failures are Σ₂, and the successful least-witness certificate
has both third-level bounds. These bounds do not cover the default-zero branch. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

noncomputable def fixedPiTwoNamedPrefixForcingFormula : SetTheorySemisentence 6 :=
  namedCheckedLevyForcingFormula
    (fixedOrdinaryForcingFormula fixedPiTwoLocalRestorationFormula_piTwo (by decide))

theorem fixedPiTwoNamedPrefixForcingFormula_piTwo : IsPiFormula 2 fixedPiTwoNamedPrefixForcingFormula :=
  namedCheckedLevyForcingFormula_piTwo
    (fixedOrdinaryForcingFormula_levy fixedPiTwoLocalRestorationFormula_piTwo (by decide))

noncomputable def fixedPiTwoNamedPrefixCutoffFormula : SetTheorySemisentence 6 :=
  piTwoNamedPrefixCutoffBody fixedPiTwoNamedPrefixForcingFormula

theorem fixedPiTwoNamedPrefixCutoffFormula_piTwo : IsPiFormula 2 fixedPiTwoNamedPrefixCutoffFormula :=
  piTwoNamedPrefixCutoffBody_piTwo fixedPiTwoNamedPrefixForcingFormula_piTwo

noncomputable def fixedSigmaTwoNamedPrefixFailureFormula : SetTheorySemisentence 6 :=
  ∼fixedPiTwoNamedPrefixCutoffFormula

theorem fixedSigmaTwoNamedPrefixFailureFormula_sigmaTwo : IsSigmaFormula 2 fixedSigmaTwoNamedPrefixFailureFormula :=
  fixedPiTwoNamedPrefixCutoffFormula_piTwo.neg

noncomputable def fixedSigmaTwoSmallerNamedPrefixFailuresFormula : SetTheorySemisentence 6 :=
  “P R one γ τ δ. ∀ β ∈ δ, !fixedSigmaTwoNamedPrefixFailureFormula P R one γ τ β”

theorem fixedSigmaTwoSmallerNamedPrefixFailuresFormula_sigmaTwo :
    IsSigmaFormula 2 fixedSigmaTwoSmallerNamedPrefixFailuresFormula :=
  .boundedAll (.bvar 5) (fixedSigmaTwoNamedPrefixFailureFormula_sigmaTwo.subst _)

noncomputable def fixedLeastNamedPrefixCutoffFormula : SetTheorySemisentence 6 :=
  leastNamedPrefixCutoffBody fixedPiTwoNamedPrefixCutoffFormula

theorem fixedLeastNamedPrefixCutoffFormula_levy (pol : LevyPolarity) :
    IsLevyFormula pol 3 fixedLeastNamedPrefixCutoffFormula :=
  leastNamedPrefixCutoffBody_levy fixedPiTwoNamedPrefixCutoffFormula_piTwo pol

noncomputable def fixedSuccessfulNamedPrefixSelectorFormula : SetTheorySemisentence 6 :=
  “δ P R one γ τ. !fixedLeastNamedPrefixCutoffFormula P R one γ τ δ”

theorem fixedSuccessfulNamedPrefixSelectorFormula_levy (pol : LevyPolarity) :
    IsLevyFormula pol 3 fixedSuccessfulNamedPrefixSelectorFormula :=
  (fixedLeastNamedPrefixCutoffFormula_levy pol).subst _

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_fixedPiTwoNamedPrefixForcingFormula {P R one p τ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hp : p ∈ P)
    (hτ : IsForcingName P τ)
    (hz : p ∈ forcingFormula P R boundedZeroMemberFormula (standardTuple ![τ])) :
    fixedPiTwoNamedPrefixForcingFormula.Evalb ![P, R, one, p, τ, δ] ↔
      p ∈ forcingFormula P R woodinLocalRestorationFormula (standardTuple ![τ, checkName one δ]) := by
  unfold fixedPiTwoNamedPrefixForcingFormula
  rw [eval_namedCheckedLevyForcingFormula]
  have hnames : ∀ i : Fin 2, IsForcingName P (![τ, checkName one δ] i) := by
    intro i
    exact Fin.cases hτ (fun j ↦ Fin.cases (checkName_isName ht.1 δ) (fun k ↦ Fin.elim0 k) j) i
  apply (eval_fixedOrdinaryForcingFormula fixedPiTwoLocalRestorationFormula_piTwo (by decide)
    hR ![τ, checkName one δ] hnames p).trans
  let guard : SetTheorySemisentence 2 := boundedZeroMemberFormula.subst
    (fun i ↦ .bvar ((![0] : Fin 1 → Fin 2) i))
  let c : Fin 2 → ForcingName P := fun i ↦ ⟨![τ, checkName one δ] i, hnames i⟩
  have hg : p ∈ forcingFormula P R guard (standardTuple ![τ, checkName one δ]) := by
    unfold guard
    rw [forcingFormula_rename]
    exact hz
  apply forcingFormula_iff_under guard fixedPiTwoLocalRestorationFormula woodinLocalRestorationFormula
    (fun W _ _ _ v hv ↦ ?_) hR ht hp c hg
  have hk : (∅ : W) ∈ v 0 := by
    simpa [guard, boundedZeroMemberFormula, Semiformula.eval_substs] using hv
  have hv' : ![v 0, v 1] = v := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  rw [← hv']
  exact (eval_fixedPiTwoLocalRestorationFormula (v 0) (v 1) hk).trans
    (woodinLocalRestorationFormula_defined.iff ![v 0, v 1]).symm

theorem eval_fixedPiTwoNamedPrefixCutoffFormula {P R one γ τ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hτ : IsForcingName P τ)
    (hz : ∀ p ∈ P, p ∈ forcingFormula P R boundedZeroMemberFormula (standardTuple ![τ])) :
    fixedPiTwoNamedPrefixCutoffFormula.Evalb ![P, R, one, γ, τ, δ] ↔
      IsWoodinNamedPrefixCutoff P R one γ τ δ := by
  have hb : fixedPiTwoNamedPrefixCutoffFormula.Evalb ![P, R, one, γ, τ, δ] ↔
      γ ∈ δ ∧ IsChoicelessInaccessible δ ∧
        ∀ p ∈ P, fixedPiTwoNamedPrefixForcingFormula.Evalb ![P, R, one, p, τ, δ] := by
    simp [fixedPiTwoNamedPrefixCutoffFormula, piTwoNamedPrefixCutoffBody, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb,
      rankCriterionHeight_iff_choicelessInaccessible]
  rw [hb]
  unfold IsWoodinNamedPrefixCutoff
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  exact forall_congr' fun p ↦ forall_congr' fun hp ↦ eval_fixedPiTwoNamedPrefixForcingFormula hR ht hp hτ (hz p hp)

theorem eval_fixedSigmaTwoNamedPrefixFailureFormula {P R one γ τ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hτ : IsForcingName P τ)
    (hz : ∀ p ∈ P, p ∈ forcingFormula P R boundedZeroMemberFormula (standardTuple ![τ])) :
    fixedSigmaTwoNamedPrefixFailureFormula.Evalb ![P, R, one, γ, τ, δ] ↔
      ¬IsWoodinNamedPrefixCutoff P R one γ τ δ := by
  simpa [fixedSigmaTwoNamedPrefixFailureFormula, Semiformula.Evalb] using
    not_congr (eval_fixedPiTwoNamedPrefixCutoffFormula (δ := δ) hR ht hτ hz)

theorem eval_fixedSigmaTwoSmallerNamedPrefixFailuresFormula {P R one γ τ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hτ : IsForcingName P τ)
    (hz : ∀ p ∈ P, p ∈ forcingFormula P R boundedZeroMemberFormula (standardTuple ![τ])) :
    fixedSigmaTwoSmallerNamedPrefixFailuresFormula.Evalb ![P, R, one, γ, τ, δ] ↔
      ∀ β ∈ δ, ¬IsWoodinNamedPrefixCutoff P R one γ τ β := by
  have hb : fixedSigmaTwoSmallerNamedPrefixFailuresFormula.Evalb ![P, R, one, γ, τ, δ] ↔
      ∀ β ∈ δ, fixedSigmaTwoNamedPrefixFailureFormula.Evalb ![P, R, one, γ, τ, β] := by
    simp [fixedSigmaTwoSmallerNamedPrefixFailuresFormula, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  rw [hb]
  exact forall_congr' fun β ↦ forall_congr' fun _ ↦ eval_fixedSigmaTwoNamedPrefixFailureFormula hR ht hτ hz

theorem eval_fixedLeastNamedPrefixCutoffFormula {P R one γ τ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hτ : IsForcingName P τ)
    (hz : ∀ p ∈ P, p ∈ forcingFormula P R boundedZeroMemberFormula (standardTuple ![τ])) :
    fixedLeastNamedPrefixCutoffFormula.Evalb ![P, R, one, γ, τ, δ] ↔
      IsLeastOrdinal (IsWoodinNamedPrefixCutoff P R one γ τ) δ := by
  have hb : fixedLeastNamedPrefixCutoffFormula.Evalb ![P, R, one, γ, τ, δ] ↔
      IsOrdinal δ ∧ fixedPiTwoNamedPrefixCutoffFormula.Evalb ![P, R, one, γ, τ, δ] ∧
        ∀ β ∈ δ, ¬fixedPiTwoNamedPrefixCutoffFormula.Evalb ![P, R, one, γ, τ, β] := by
    simp [fixedLeastNamedPrefixCutoffFormula, leastNamedPrefixCutoffBody, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  rw [hb, isLeastOrdinal_iff_no_smaller]
  simp only [eval_fixedPiTwoNamedPrefixCutoffFormula hR ht hτ hz]

theorem eval_fixedSuccessfulNamedPrefixSelectorFormula {P R one γ τ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hτ : IsForcingName P τ)
    (hz : ∀ p ∈ P, p ∈ forcingFormula P R boundedZeroMemberFormula (standardTuple ![τ]))
    (hex : ∃ η, IsWoodinNamedPrefixCutoff P R one γ τ η) :
    fixedSuccessfulNamedPrefixSelectorFormula.Evalb ![δ, P, R, one, γ, τ] ↔
      δ = woodinNamedPrefixCutoff P R one γ τ := by
  have hb : fixedSuccessfulNamedPrefixSelectorFormula.Evalb ![δ, P, R, one, γ, τ] ↔
      fixedLeastNamedPrefixCutoffFormula.Evalb ![P, R, one, γ, τ, δ] := by
    simp [fixedSuccessfulNamedPrefixSelectorFormula, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]
  rw [hb, eval_fixedLeastNamedPrefixCutoffFormula hR ht hτ hz]
  exact (woodinNamedPrefixCutoff_eq_iff_least_of_exists hex).symm

end ZFVP
