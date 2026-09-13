import ZFVP.SetTheory.CnCofinalUnbounded
import ZFVP.SetTheory.CnExtendible

/-! Reflection of unboundedness statements below a correct rank stage.

This is the step of the finite restoration theorem that turns global unboundedness of the
`E_s`-cardinals and of `C(c)` into unboundedness below the stage `Λ`, using only that `Λ` is
`Σ_{k+1}`-correct and that the defining formula is `Σ_{k+1}`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- `∃ δ, η ∈ δ ∧ φ δ`, in the free variable `η`. -/
def existsAboveFormula (φ : SetTheorySemisentence 1) : SetTheorySemisentence 1 :=
  “η. ∃ δ, η ∈ δ ∧ !φ δ”

theorem existsAboveFormula_sigma {k : ℕ} {φ : SetTheorySemisentence 1}
    (hφ : IsSigmaFormula (k + 1) φ) : IsSigmaFormula (k + 1) (existsAboveFormula φ) := by
  unfold existsAboveFormula
  exact .exs (.and (.bounded (.rel _ _)) (hφ.subst _))

theorem eval_existsAboveFormula {W : Type*} [SetStructure W] (φ : SetTheorySemisentence 1)
    (η : W) : (existsAboveFormula φ).Evalb ![η] ↔ ∃ δ : W, η ∈ δ ∧ φ.Evalb ![δ] := by
  simp [existsAboveFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Function.comp_def, Matrix.constant_eq_singleton]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_singleton_val {δ : V} (d : SetDomain (hierarchy δ)) :
    (fun i : Fin 1 ↦ (![d] i).val) = ![d.val] := by
  funext i
  exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i

/-- If a class of ordinals is defined by a `Σ_{k+1}` formula and is unbounded in `V`, then it is
unbounded below every `Σ_{k+1}`-correct stage `Λ`. -/
theorem exists_sigma_witness_mem_of_cn {k : ℕ} {Λ η : V} (hΛ : Cn (k + 1) Λ)
    {φ : SetTheorySemisentence 1} (hφ : IsSigmaFormula (k + 1) φ)
    {P : V → Prop} (hP : ∀ x : V, φ.Evalb ![x] ↔ P x)
    (hord : ∀ x : V, P x → IsOrdinal x)
    (hun : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ P κ)
    (hη : η ∈ Λ) : ∃ δ : V, δ ∈ Λ ∧ η ∈ δ ∧ P δ := by
  let := hΛ.ordinal
  let : IsOrdinal η := IsOrdinal.of_mem hη
  let b : SetDomain (hierarchy Λ) := ⟨η, ordinal_subset_hierarchy Λ η hη⟩
  obtain ⟨κ, hηκ, hκ⟩ := hun η inferInstance
  have hglobal : (existsAboveFormula φ).Evalb ![η] :=
    (eval_existsAboveFormula φ η).mpr ⟨κ, hηκ, (hP κ).mpr hκ⟩
  have hcorrect := hΛ.sigma_correct (existsAboveFormula_sigma hφ) ![b]
  rw [eval_singleton_val b] at hcorrect
  obtain ⟨d, hηd, hd⟩ := (eval_existsAboveFormula φ b).mp (hcorrect.mpr hglobal)
  have hlift := hΛ.sigma_correct hφ ![d]
  rw [eval_singleton_val d] at hlift
  have hPd : P d.val := (hP d.val).mp (hlift.mp hd)
  let := hord d.val hPd
  exact ⟨d.val, ordinal_mem_hierarchy_iff.mp d.property, hηd, hPd⟩

/-- The `E_s`-cardinals are unbounded below a `Σ_{k+1}`-correct stage. -/
theorem exists_cnExtendible_mem_of_cn {s k : ℕ} {Λ η : V} (hΛ : Cn (k + 1) Λ)
    (hs : IsSigmaFormula (k + 1) (cnExtendibleFormula s))
    (hUE : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsCnExtendible s κ)
    (hη : η ∈ Λ) : ∃ δ : V, δ ∈ Λ ∧ η ∈ δ ∧ IsCnExtendible s δ :=
  exists_sigma_witness_mem_of_cn hΛ hs (eval_cnExtendibleFormula s)
    (fun _ h ↦ h.1.1) hUE hη

/-- `C(c)` is unbounded below a `Σ_{k+1}`-correct stage. -/
theorem exists_cn_mem_of_cn {c k : ℕ} {Λ η : V} (hΛ : Cn (k + 1) Λ)
    (hc : IsSigmaFormula (k + 1) (cnFormula c)) (hη : η ∈ Λ) :
    ∃ ρ : V, ρ ∈ Λ ∧ η ∈ ρ ∧ Cn c ρ :=
  exists_sigma_witness_mem_of_cn hΛ hc (eval_cnFormula c) (fun _ h ↦ h.ordinal)
    (fun α hα ↦ by let := hα; exact cn_unbounded c α) hη

end ZFVP
