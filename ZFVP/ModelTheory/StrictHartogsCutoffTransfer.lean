import ZFVP.ModelTheory.StrictHartogsPrefixCutoff
import ZFVP.ModelTheory.ForcingHartogsUniform

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

private theorem forall_eq_args3 {α : Type*} (x0 x1 x2 : α) (F : α → α → α → Prop) :
    (∀ (a0 a1 a2 : α), a0 = x0 → a1 = x1 → a2 = x2 → F a0 a1 a2) ↔ F x0 x1 x2 :=
  ⟨fun h ↦ h x0 x1 x2 rfl rfl rfl, fun h a0 a1 a2 h0 h1 h2 ↦ by subst a0 a1 a2; exact h⟩

private theorem forall_eq_args4 {α : Type*} (x0 x1 x2 x3 : α) (F : α → α → α → α → Prop) :
    (∀ (a0 a1 a2 a3 : α), a0 = x0 → a1 = x1 → a2 = x2 → a3 = x3 → F a0 a1 a2 a3) ↔ F x0 x1 x2 x3 :=
  ⟨fun h ↦ h x0 x1 x2 x3 rfl rfl rfl rfl, fun h a0 a1 a2 a3 h0 h1 h2 h3 ↦ by subst a0 a1 a2 a3; exact h⟩

private theorem forall_eq_args6 {α : Type*} (x0 x1 x2 x3 x4 x5 : α) (F : α → α → α → α → α → α → Prop) :
    (∀ (a0 a1 a2 a3 a4 a5 : α), a0 = x0 → a1 = x1 → a2 = x2 → a3 = x3 → a4 = x4 → a5 = x5 → F a0 a1 a2 a3 a4 a5) ↔ F x0 x1 x2 x3 x4 x5 :=
  ⟨fun h ↦ h x0 x1 x2 x3 x4 x5 rfl rfl rfl rfl rfl rfl, fun h a0 a1 a2 a3 a4 a5 h0 h1 h2 h3 h4 h5 ↦ by subst a0 a1 a2 a3 a4 a5; exact h⟩

def strictHartogsPrefixCutoffFormula : SetTheorySemisentence 6 :=
  f“P R o a δ τ. !woodinSupercompactFormula δ ∧ !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    P ∈ !hierarchyFormula δ ∧ R ∈ !hierarchyFormula δ ∧ a ∈ δ ∧
    !hartogsNumberNameFormula τ P R (!checkNameFormula o a) ∧
    (∀ p ∈ P, !(namedUnaryForcingFormula regularCardinalFormula) P R p τ) ∧
    (∀ p ∈ P, !(namedUnaryForcingFormula dependentChoiceBelowFormula) P R p τ) →
      ∃ c ∈ δ, !woodinNamedPrefixCutoffFormula P R o a τ c”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_strictHartogsPrefixCutoffFormula (v : Fin 6 → V) :
    strictHartogsPrefixCutoffFormula.Evalb v ↔
      (IsWoodinSupercompact (v 4) → IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
        v 0 ∈ hierarchy (v 4) → v 1 ∈ hierarchy (v 4) → v 3 ∈ v 4 →
        v 5 = hartogsNumberName (v 0) (v 1) (checkName (v 2) (v 3)) →
        (∀ p ∈ v 0, p ∈ forcingFormula (v 0) (v 1) regularCardinalFormula (standardTuple ![v 5])) →
        (∀ p ∈ v 0, p ∈ forcingFormula (v 0) (v 1) dependentChoiceBelowFormula (standardTuple ![v 5])) →
        ∃ c ∈ v 4, IsWoodinNamedPrefixCutoff (v 0) (v 1) (v 2) (v 3) (v 5) c) := by
  simp [strictHartogsPrefixCutoffFormula, Semiformula.eval_nestFormulae,
    Matrix.vecForall_iff, Fin.forall_fin_succ, forall_eq_args3, forall_eq_args4, forall_eq_args6]

theorem IsWoodinSupercompact.strictHartogsPrefixCutoff {P R one a δ : V}
    (hδ : IsWoodinSupercompact δ) (hord : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hP : P ∈ hierarchy δ) (hR : R ∈ hierarchy δ) (haδ : a ∈ δ)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![hartogsNumberName P R (checkName one a)]))
    (hDC : ∀ p ∈ P, p ∈ forcingFormula P R dependentChoiceBelowFormula
      (standardTuple ![hartogsNumberName P R (checkName one a)])) :
    ∃ c ∈ δ, IsWoodinNamedPrefixCutoff P R one a (hartogsNumberName P R (checkName one a)) c := by
  have hh := eval_of_countable_zf strictHartogsPrefixCutoffFormula (by
    intro W _ _ _ _ v
    apply (eval_strictHartogsPrefixCutoffFormula v).mpr
    intro hδ ho ht hP hR ha he hk hDC
    rw [he] at hk hDC ⊢
    exact hδ.strictHartogsPrefixCutoff_countable ho ht hP hR ha hk hDC)
    ![P, R, one, a, δ, hartogsNumberName P R (checkName one a)]
  exact (eval_strictHartogsPrefixCutoffFormula _).mp hh hδ hord htop hP hR haδ rfl hκ hDC

end ZFVP
