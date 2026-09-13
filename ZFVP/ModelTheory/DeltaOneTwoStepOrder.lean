import ZFVP.ModelTheory.DeltaOneTwoStepConditions
import ZFVP.SetTheory.DeltaOnePairProjections
import ZFVP.SetTheory.DeltaOneBoundedForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def twoStepOrderCertificateRow (φ : BoundedFormulaTree 3) : SetTheorySemisentence 6 :=
  “T P R S a b. ∃ p, !sigmaOnePairFirstFormula p a ∧
    ∃ q, !sigmaOnePairFirstFormula q b ∧
    ∃ σ, !sigmaOnePairSecondFormula σ a ∧
    ∃ τ, !sigmaOnePairSecondFormula τ b ∧
    ((!boundedPairMemberFormula T a b ∧ !boundedPairMemberFormula R p q ∧
      !(φ.forcingCertificate true) P R p S σ τ) ∨
     (¬!boundedPairMemberFormula T a b ∧ (¬!boundedPairMemberFormula R p q ∨
      !(φ.forcingCertificate false) P R p S σ τ)))”

theorem twoStepOrderCertificateRow_sigmaOne (φ : BoundedFormulaTree 3) :
    IsSigmaFormula 1 (twoStepOrderCertificateRow φ) := by
  unfold twoStepOrderCertificateRow
  repeat' first
    | exact sigmaOnePairFirstFormula_sigmaOne.subst _
    | exact sigmaOnePairSecondFormula_sigmaOne.subst _
    | exact (φ.forcingCertificate_sigmaOne true).subst _
    | exact (φ.forcingCertificate_sigmaOne false).subst _
    | exact IsLevyFormula.bounded (boundedPairMemberFormula_bounded.subst _)
    | exact IsLevyFormula.bounded (boundedPairMemberFormula_bounded.subst _).neg
    | apply IsLevyFormula.exs
    | apply IsLevyFormula.and
    | apply IsLevyFormula.or

def sigmaOneTwoStepOrderSetFormula (φ : BoundedFormulaTree 3) : SetTheorySemisentence 6 :=
  “T P R Q S t. ∃ C, !sigmaOneTwoStepConditionSetFormula C P R Q t ∧
    (∀ z ∈ T, ∃ a ∈ C, ∃ b ∈ C, !boundedKpairFormula z a b) ∧
    (∀ a ∈ C, ∀ b ∈ C, !(twoStepOrderCertificateRow φ) T P R S a b)”

theorem sigmaOneTwoStepOrderSetFormula_sigmaOne (φ : BoundedFormulaTree 3) :
    IsSigmaFormula 1 (sigmaOneTwoStepOrderSetFormula φ) :=
  .exs (.and (sigmaOneTwoStepConditionSetFormula_sigmaOne.subst _)
    (.and (.bounded (.all (.bvar 1) (.exs (.bvar 1) (.exs (.bvar 2) (boundedKpairFormula_bounded.subst _)))))
      (.boundedAll _ (.boundedAll _ ((twoStepOrderCertificateRow_sigmaOne φ).subst _)))))

def piOneTwoStepOrderSetFormula (φ : BoundedFormulaTree 3) : SetTheorySemisentence 6 :=
  “T P R Q S t. ∀ U, !(sigmaOneTwoStepOrderSetFormula φ) U P R Q S t → T = U”

theorem piOneTwoStepOrderSetFormula_piOne (φ : BoundedFormulaTree 3) :
    IsPiFormula 1 (piOneTwoStepOrderSetFormula φ) :=
  .all (.or ((sigmaOneTwoStepOrderSetFormula_sigmaOne φ).subst _).neg (.bounded (.rel _ _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_twoStepOrderCertificateRow (φ : BoundedFormulaTree 3)
    (hφ : φ.formula = boundedPairMemberFormula) {P R Q S t : V}
    (hR : IsForcingPreorder P R) (h : IsForcingIterand P R Q S t)
    (T : V) {a b : V} (ha : a ∈ twoStepConditions P R Q t)
    (hb : b ∈ twoStepConditions P R Q t) :
    (twoStepOrderCertificateRow φ).Evalb ![T, P, R, S, a, b] ↔
      (⟨a, b⟩ₖ ∈ T ↔ ⟨a, b⟩ₖ ∈ twoStepOrder P R Q S t) := by
  obtain ⟨p, hp, σ, hσ, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp ha
  obtain ⟨q, hq, τ, hτ, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp hb
  have hn : ∀ i, IsForcingName P (![S, σ, τ] i) := by
    simp only [Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.forall_fin_zero, and_true]
    exact ⟨h.orderName, h.name hσ, h.name hτ⟩
  have he (answer : Bool) := φ.forcingCertificate_ordinary_meaning hR ![S, σ, τ] hn answer p
  rw [hφ] at he
  simp only [Semiformula.Evalb] at he
  simp [twoStepOrderCertificateRow, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he, TruthAnswer,
    kpair_mem_twoStepOrder, ha, hb]
  tauto

theorem eval_sigmaOneTwoStepOrderSetFormula (φ : BoundedFormulaTree 3)
    (hφ : φ.formula = boundedPairMemberFormula) {P R Q S t : V}
    (hR : IsForcingPreorder P R) (h : IsForcingIterand P R Q S t) (T : V) :
    (sigmaOneTwoStepOrderSetFormula φ).Evalb ![T, P, R, Q, S, t] ↔
      T = twoStepOrder P R Q S t := by
  simp [sigmaOneTwoStepOrderSetFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def]
  constructor
  · rintro ⟨hs, ht⟩
    apply mem_ext
    intro z
    constructor
    · intro hz
      obtain ⟨a, ha, b, hb, rfl⟩ := hs z hz
      exact ((eval_twoStepOrderCertificateRow φ hφ hR h T ha hb).mp (ht a ha b hb)).mp hz
    · intro hz
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
      exact ((eval_twoStepOrderCertificateRow φ hφ hR h T ha hb).mp (ht a ha b hb)).mpr hz
  · intro hT
    rw [hT]
    exact ⟨fun z hz ↦ mem_prod_iff.mp (mem_sep_iff.mp hz).1,
      fun _ ha _ hb ↦ (eval_twoStepOrderCertificateRow φ hφ hR h _ ha hb).mpr Iff.rfl⟩

theorem eval_piOneTwoStepOrderSetFormula (φ : BoundedFormulaTree 3)
    (hφ : φ.formula = boundedPairMemberFormula) {P R Q S t : V}
    (hR : IsForcingPreorder P R) (h : IsForcingIterand P R Q S t) (T : V) :
    (piOneTwoStepOrderSetFormula φ).Evalb ![T, P, R, Q, S, t] ↔
      T = twoStepOrder P R Q S t := by
  have he := eval_sigmaOneTwoStepOrderSetFormula φ hφ hR h
  simp only [Semiformula.Evalb] at he
  simp [piOneTwoStepOrderSetFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he]

theorem twoStepOrder_deltaOne_formulas :
    ∃ σ π : SetTheorySemisentence 6, IsSigmaFormula 1 σ ∧ IsPiFormula 1 π ∧
      ∀ P R Q S t : V, IsForcingPreorder P R → IsForcingIterand P R Q S t → ∀ T,
        (σ.Evalb ![T, P, R, Q, S, t] ↔ T = twoStepOrder P R Q S t) ∧
        (π.Evalb ![T, P, R, Q, S, t] ↔ T = twoStepOrder P R Q S t) := by
  obtain ⟨φ, hφ⟩ := boundedFormulaTree_exists boundedPairMemberFormula_bounded
  exact ⟨sigmaOneTwoStepOrderSetFormula φ, piOneTwoStepOrderSetFormula φ,
    sigmaOneTwoStepOrderSetFormula_sigmaOne φ, piOneTwoStepOrderSetFormula_piOne φ,
    fun _ _ _ _ _ hR h T ↦ ⟨eval_sigmaOneTwoStepOrderSetFormula φ hφ hR h T,
      eval_piOneTwoStepOrderSetFormula φ hφ hR h T⟩⟩

end ZFVP
