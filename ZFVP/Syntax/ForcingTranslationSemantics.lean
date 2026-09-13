import ZFVP.Syntax.ForcingTranslation
import ZFVP.SetTheory.ForcingFormulaWitnesses

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem classForcingFormula_subset (P R : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N)
    {n : ℕ} (φ : SetTheorySemisentence n) (b : V) : classForcingFormula P R N hN φ b ⊆ P := by
  induction φ generalizing b with
  | verum => exact fun _ h ↦ h
  | falsum => exact fun _ h ↦ False.elim (not_mem_empty h)
  | rel r ts =>
    cases r with
    | eq => exact atomicEquality_subset _ _ _ _
    | mem => exact atomicMembership_subset _ _ _ _
  | nrel r ts => exact forcingNegation_subset _ _ _
  | and φ ψ ihφ _ => exact fun p hp ↦ ihφ b p (mem_inter_iff.mp hp).1
  | or φ ψ _ _ => exact forcingClosure_subset _ _ _
  | all φ _ =>
    rw [classForcingFormula_all]
    exact fun p h ↦ (mem_forcingClassIntersection_iff P N hN _ _ p).mp h |>.1
  | exs φ _ => exact forcingClosure_subset _ _ _

private theorem forall_four_eq {α : Type*} (a b c d : α) (Q : α → α → α → α → Prop) :
    (∀ u v w x, u = a → v = b → w = c → x = d → Q u v w x) ↔ Q a b c d :=
  ⟨fun h ↦ h a b c d rfl rfl rfl rfl, by rintro h u v w x rfl rfl rfl rfl; exact h⟩

private theorem forall_six_eq {α : Type*} (a b c d e f : α)
    (Q : α → α → α → α → α → α → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → Q u v w x y z) ↔ Q a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl, by rintro h u v w x y z rfl rfl rfl rfl rfl rfl; exact h⟩

theorem forcingTranslation_defined (χ : SetTheorySemisentence 4)
    (N : V → V → V → V → Prop) (hN : ℒₛₑₜ-relation₄ N)
    [Defined (fun v : Fin 4 → V ↦ N (v 0) (v 1) (v 2) (v 3)) χ]
    {n : ℕ} (φ : SetTheorySemisentence n) :
    Defined (fun v : Fin 6 → V ↦ v 4 ∈ classForcingFormula (v 0) (v 1)
      (N (v 0) (v 2) (v 3)) (by definability) φ (v 5)) (forcingTranslation χ φ) := by
  induction φ with
  | verum => exact ⟨fun v ↦ by simp [forcingTranslation, classForcingFormula_verum]⟩
  | falsum => exact ⟨fun v ↦ by simp [forcingTranslation, classForcingFormula_falsum]⟩
  | rel r ts => exact forcingAtomicTranslation_defined r ts
  | nrel r ts =>
    exact ⟨fun v ↦ by simp [forcingTranslation, forcingNegationTranslation,
      classForcingFormula_nrel, mem_forcingNegation_iff, Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ, forall_six_eq]⟩
  | and φ ψ ihφ ihψ =>
    have := ihφ
    have := ihψ
    exact ⟨fun v ↦ by simp [forcingTranslation, forcingConjunctionTranslation, classForcingFormula_and, Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ, forall_six_eq]⟩
  | or φ ψ ihφ ihψ =>
    have := ihφ
    have := ihψ
    refine ⟨fun v ↦ ?_⟩
    simp [forcingTranslation, forcingDisjunctionTranslation, classForcingFormula_or,
      mem_forcingClosure_iff, Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ, forall_six_eq]
    intro _
    apply forall_congr'
    intro q
    apply forall_congr'
    intro _
    apply forall_congr'
    intro _
    constructor
    · rintro ⟨r, _, hrq, hrF⟩
      exact ⟨r, hrF, hrq⟩
    · rintro ⟨r, hrF, hrq⟩
      refine ⟨r, ?_, hrq, hrF⟩
      rcases hrF with hφ | hψ
      · exact classForcingFormula_subset (v 0) (v 1) (N (v 0) (v 2) (v 3)) (by definability) φ (v 5) r hφ
      · exact classForcingFormula_subset (v 0) (v 1) (N (v 0) (v 2) (v 3)) (by definability) ψ (v 5) r hψ

  | all φ ih =>
    have := ih
    exact ⟨fun v ↦ by simp [forcingTranslation, forcingUniversalTranslation, classForcingFormula_all,
      mem_forcingClassIntersection_iff, Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ, forall_six_eq, forall_four_eq]⟩
  | exs φ ih =>
    have := ih
    exact ⟨fun v ↦ by simp [forcingTranslation, forcingExistentialTranslation,
      classForcingFormula_exs_dense_iff, Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ, forall_six_eq, forall_four_eq]⟩

instance ordinaryForcingTranslation_defined {n : ℕ} (φ : SetTheorySemisentence n) :
    Defined (fun v : Fin 6 → V ↦ v 4 ∈ forcingFormula (v 0) (v 1) φ (v 5)) (ordinaryForcingTranslation φ) :=
  forcingTranslation_defined ordinaryNameClassFormula (fun P _ _ τ ↦ IsForcingName P τ) (by definability) φ

instance symmetricForcingTranslation_defined {n : ℕ} (φ : SetTheorySemisentence n) :
    Defined (fun v : Fin 6 → V ↦ v 4 ∈ symmetricForcingFormula (v 0) (v 1) (v 2) (v 3) φ (v 5))
      (symmetricForcingTranslation φ) :=
  forcingTranslation_defined hereditarilySymmetricNameFormula IsHereditarilySymmetricName (by definability) φ

theorem ordinaryForcingTranslation_eval (P R Γ F p b : V) {n : ℕ} (φ : SetTheorySemisentence n) :
    (ordinaryForcingTranslation φ).Evalb ![P, R, Γ, F, p, b] ↔ p ∈ forcingFormula P R φ b :=
  Defined.eval_iff (φ := ordinaryForcingTranslation φ) ![P, R, Γ, F, p, b]

theorem symmetricForcingTranslation_eval (P R Γ F p b : V) {n : ℕ} (φ : SetTheorySemisentence n) :
    (symmetricForcingTranslation φ).Evalb ![P, R, Γ, F, p, b] ↔ p ∈ symmetricForcingFormula P R Γ F φ b :=
  Defined.eval_iff (φ := symmetricForcingTranslation φ) ![P, R, Γ, F, p, b]

end ZFVP
