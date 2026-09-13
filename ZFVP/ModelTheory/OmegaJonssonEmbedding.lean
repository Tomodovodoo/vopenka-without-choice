import ZFVP.ModelTheory.EmbeddingCnTransfer
import ZFVP.SetTheory.LevyComplexityBound

/-! The omega-Jonsson predicate used by Kunen's inconsistency argument, its defining formula,
a crude Levy bound for that formula, and transfer of the predicate along a coded self-embedding
of a C(n) rank stage. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- `F` is a function whose arguments are subsets of `l` with values in `l`, and every subset `A`
of `l` that `l` injects into carries, for each `c ∈ l`, a countably enumerated subset in the domain
of `F` with value `c`. -/
def omegaJonssonFormula : SetTheorySemisentence 2 :=
  f“F l. !IsFunction.dfn F ∧ (∀ x ∈ !domain.dfn F, x ⊆ l ∧ !value.dfn F x ∈ l) ∧
    ∀ A, A ⊆ l → !CardLE.dfn l A → ∀ c ∈ l, ∃ a ∈ !domain.dfn F, a ⊆ A ∧
      (∃ g, g ∈ !function.dfn a (!isω) ∧ !range.dfn g = a) ∧ !value.dfn F a = c”

/-- The crude syntactic Levy bound of `omegaJonssonFormula`. -/
def omegaJonssonBound : ℕ := levySyntacticBound omegaJonssonFormula

theorem omegaJonssonFormula_complexity (p : LevyPolarity) :
    IsLevyFormula p omegaJonssonBound omegaJonssonFormula :=
  isLevyFormula_syntacticBound _ p

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `F` is an omega-Jonsson function for `lam`. -/
def IsOmegaJonsson (F lam : V) : Prop :=
  IsFunction F ∧ (∀ x ∈ domain F, x ⊆ lam ∧ F ‘ x ∈ lam) ∧
    ∀ A, A ⊆ lam → lam ≤# A →
      ∀ γ ∈ lam, ∃ a ∈ domain F, a ⊆ A ∧ (∃ g, g ∈ a ^ (ω : V) ∧ range g = a) ∧ F ‘ a = γ

instance omegaJonssonFormula_defined :
    ℒₛₑₜ-relation[V] IsOmegaJonsson via omegaJonssonFormula :=
  ⟨fun v ↦ by simp [omegaJonssonFormula, IsOmegaJonsson, CardLE]⟩

theorem eval_omegaJonssonFormula (F lam : V) :
    omegaJonssonFormula.Evalb ![F, lam] ↔ IsOmegaJonsson F lam :=
  (omegaJonssonFormula_defined (V := V)).iff ![F, lam]

instance omegaJonsson_definable : ℒₛₑₜ-relation[V] IsOmegaJonsson :=
  omegaJonssonFormula_defined.to_definable

/-- A coded self-embedding of a correct rank stage preserves and reflects every relation defined
by a formula within the correctness level of the stage. -/
theorem rankSelfEmbedding_defined_iff {m n : ℕ} {δ f : V} (hδ : Cn (m + 1) δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
    {φ : SetTheorySemisentence n} (hφ : IsPiFormula (m + 1) φ) (R : (Fin n → V) → Prop)
    [Defined R φ] (v : Fin n → V) (hv : ∀ i, v i ∈ hierarchy δ) :
    R v ↔ R (fun i ↦ f ‘ (v i)) := by
  let b : Fin n → SetDomain (hierarchy δ) := fun i ↦ ⟨v i, hv i⟩
  have hs := hδ.defined_correct hφ R b
  have ht := hδ.defined_correct hφ R (h.toFunction ∘ b)
  exact hs.symm.trans ((h.eval_semisentence φ b).trans ht)

/-- The image of an omega-Jonsson function under a coded self-embedding of a correct rank stage is
omega-Jonsson for the image of the ordinal. -/
theorem IsOmegaJonsson.value {m : ℕ} {δ f F lam : V} (hδ : Cn (m + 1) δ)
    (hm : omegaJonssonBound ≤ m + 1)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
    (hF : F ∈ hierarchy δ) (hlam : lam ∈ hierarchy δ) (hJ : IsOmegaJonsson F lam) :
    IsOmegaJonsson (f ‘ F) (f ‘ lam) := by
  have hv : ∀ i, (![F, lam] : Fin 2 → V) i ∈ hierarchy δ := by
    intro i
    exact Fin.cases hF (fun j ↦ Fin.cases hlam (fun t ↦ Fin.elim0 t) j) i
  have hiff := rankSelfEmbedding_defined_iff hδ h
    ((omegaJonssonFormula_complexity .pi).mono hm)
    (fun w ↦ IsOmegaJonsson (w 0) (w 1)) ![F, lam] hv
  exact hiff.mp hJ

end ZFVP
