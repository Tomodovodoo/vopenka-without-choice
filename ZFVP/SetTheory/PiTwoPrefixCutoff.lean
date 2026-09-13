import ZFVP.SetTheory.PiTwoLocalRestoration
import ZFVP.SetTheory.PiOneRegularInaccessible
import ZFVP.SetTheory.ForcingRenaming

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def boundedZeroMemberFormula : SetTheorySemisentence 1 :=
  “κ. ∃ z ∈ κ, !boundedEmptyFormula z”

theorem boundedZeroMemberFormula_bounded : IsBoundedSetFormula boundedZeroMemberFormula :=
  .exs (.bvar 0) (boundedEmptyFormula_bounded.subst _)

def checkedBinaryLevyForcingFormula (θ : SetTheorySemisentence 5) : SetTheorySemisentence 6 :=
  “P R one p κ δ. ∀ τ υ, !(sigmaOneCheckNameFormula true) one κ τ →
    !(sigmaOneCheckNameFormula true) one δ υ → !θ P R p τ υ”

theorem checkedBinaryLevyForcingFormula_piTwo {θ : SetTheorySemisentence 5}
    (hθ : IsPiFormula 2 θ) : IsPiFormula 2 (checkedBinaryLevyForcingFormula θ) :=
  .all (.all (.or (.raise ((sigmaOneCheckNameFormula_sigmaOne true).subst _).neg)
    (.or (.raise ((sigmaOneCheckNameFormula_sigmaOne true).subst _).neg) (hθ.subst _))))

def piTwoPrefixCutoffBody (Ψ : SetTheorySemisentence 6) : SetTheorySemisentence 5 :=
  “P R one κ δ. κ ∈ δ ∧ !rankCriterionFormula δ ∧ ∀ p ∈ P, !Ψ P R one p κ δ”

theorem piTwoPrefixCutoffBody_piTwo {Ψ : SetTheorySemisentence 6} (hΨ : IsPiFormula 2 Ψ) :
    IsPiFormula 2 (piTwoPrefixCutoffBody Ψ) :=
  .and (.bounded (.rel _ _)) (.and (.raise (rankCriterionFormula_piOne.subst _))
    (.boundedAll (.bvar 0) (hΨ.subst _)))

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedZeroMemberFormula (κ : V) :
    boundedZeroMemberFormula.Evalb ![κ] ↔ (∅ : V) ∈ κ := by
  simp [boundedZeroMemberFormula]

theorem eval_checkedBinaryLevyForcingFormula (θ : SetTheorySemisentence 5) (P R one p κ δ : V) :
    (checkedBinaryLevyForcingFormula θ).Evalb ![P, R, one, p, κ, δ] ↔
      θ.Evalb ![P, R, p, checkName one κ, checkName one δ] := by
  simp [checkedBinaryLevyForcingFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, eval_sigmaOneCheckNameFormula, TruthAnswer]

theorem forcing_localRestoration_piTwo_uniform :
    ∃ Ψ : SetTheorySemisentence 6, IsPiFormula 2 Ψ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ P R one p κ δ : V, IsForcingPreorder P R → IsForcingTop P R one →
          p ∈ P → (∅ : V) ∈ κ →
          (Ψ.Evalb ![P, R, one, p, κ, δ] ↔
            p ∈ forcingFormula P R woodinLocalRestorationFormula
              (standardTuple ![checkName one κ, checkName one δ])) := by
  obtain ⟨Φ, hΦ, hlocal⟩ := woodinLocalRestoration_piTwo_uniform.{u}
  obtain ⟨θ, hθ, he⟩ := IsLevyFormula.ordinaryForcing_definition_uniform.{u} hΦ (by omega)
  refine ⟨checkedBinaryLevyForcingFormula θ, checkedBinaryLevyForcingFormula_piTwo hθ, ?_⟩
  intro V _ _ _ P R one p κ δ hR ht hp hk
  rw [eval_checkedBinaryLevyForcingFormula]
  have hnames : ∀ i : Fin 2, IsForcingName P (![checkName one κ, checkName one δ] i) := by
    intro i
    exact Fin.cases (checkName_isName ht.1 κ)
      (fun j ↦ Fin.cases (checkName_isName ht.1 δ) (fun k ↦ Fin.elim0 k) j) i
  apply (he V P R hR ![checkName one κ, checkName one δ] hnames p).trans
  let guard : SetTheorySemisentence 2 := boundedZeroMemberFormula.subst
    (fun i ↦ .bvar ((![0] : Fin 1 → Fin 2) i))
  let c : Fin 2 → ForcingName P := fun i ↦ ⟨![checkName one κ, checkName one δ] i, hnames i⟩
  have hg : p ∈ forcingFormula P R guard (standardTuple ![checkName one κ, checkName one δ]) := by
    unfold guard
    rw [forcingFormula_rename]
    exact forces_checked_bounded boundedZeroMemberFormula boundedZeroMemberFormula_bounded hR ht
      (by simpa [boundedZeroMemberFormula, Semiformula.Evalb] using hk) hp
  apply forcingFormula_iff_under guard Φ woodinLocalRestorationFormula
    (fun W _ _ _ v hv ↦ ?_) hR ht hp c hg
  have hk' : (∅ : W) ∈ v 0 := by
    simpa [guard, boundedZeroMemberFormula, Semiformula.eval_substs] using hv
  have hv' : ![v 0, v 1] = v := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  rw [← hv']
  exact (hlocal W (v 0) (v 1) hk').trans
    (woodinLocalRestorationFormula_defined.iff ![v 0, v 1]).symm

theorem woodinPrefixCutoff_piTwo_uniform :
    ∃ Ξ : SetTheorySemisentence 5, IsPiFormula 2 Ξ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        ∀ P R one κ δ : V, IsForcingPreorder P R → IsForcingTop P R one →
          (∅ : V) ∈ κ → (Ξ.Evalb ![P, R, one, κ, δ] ↔ IsWoodinPrefixCutoff P R one κ δ) := by
  obtain ⟨Ψ, hΨ, he⟩ := forcing_localRestoration_piTwo_uniform.{u}
  refine ⟨piTwoPrefixCutoffBody Ψ, piTwoPrefixCutoffBody_piTwo hΨ, ?_⟩
  intro V _ _ _ P R one κ δ hR ht hk
  have hb : (piTwoPrefixCutoffBody Ψ).Evalb ![P, R, one, κ, δ] ↔
      κ ∈ δ ∧ IsChoicelessInaccessible δ ∧ ∀ p ∈ P, Ψ.Evalb ![P, R, one, p, κ, δ] := by
    simp [piTwoPrefixCutoffBody, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb,
      rankCriterionHeight_iff_choicelessInaccessible]
  rw [hb]
  unfold IsWoodinPrefixCutoff
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  exact forall_congr' fun p ↦ forall_congr' fun hp ↦ he V P R one p κ δ hR ht hp hk

end ZFVP
