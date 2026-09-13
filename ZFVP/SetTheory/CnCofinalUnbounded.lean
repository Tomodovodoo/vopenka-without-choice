import ZFVP.SetTheory.CnCofinal

/-! One further correctness level supplies cofinally many correct heights. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def cnAboveFormula (n : ℕ) : SetTheorySemisentence 1 :=
  “β. ∃ δ, β ∈ δ ∧ !(cnFormula n) δ”

theorem cnAboveFormula_sigma (n : ℕ) : IsSigmaFormula (n + 3) (cnAboveFormula (n + 2)) := by
  unfold cnAboveFormula
  exact .exs (.and (.bounded (.rel _ _)) (((cnFormula_pi (by omega : 2 ≤ n + 2)).raise).subst _))

theorem eval_cnAbove_components {W : Type*} [SetStructure W] (n : ℕ) (β : W) :
    (cnAboveFormula n).Evalb ![β] ↔ ∃ δ : W, β ∈ δ ∧ (cnFormula n).Evalb ![δ] := by
  simp [cnAboveFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Function.comp_def, Matrix.constant_eq_singleton]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem Cn.cnCofinal {n : ℕ} {θ : V} (hθ : Cn (n + 3) θ) : CnCofinal (n + 2) θ := by
  let := hθ.ordinal
  intro β hβ
  let : IsOrdinal β := IsOrdinal.of_mem hβ
  let b : SetDomain (hierarchy θ) := ⟨β, ordinal_subset_hierarchy θ β hβ⟩
  obtain ⟨δ, hβδ, hδ⟩ := cn_unbounded (n + 2) β
  have hglobal : (cnAboveFormula (n + 2)).Evalb ![β] :=
    (eval_cnAbove_components _ β).mpr ⟨δ, hβδ, (eval_cnFormula _ δ).mpr hδ⟩
  have hcorrect := hθ.sigma_correct (cnAboveFormula_sigma n) ![b]
  have hv : (fun i : Fin 1 ↦ (![b] i).val) = ![β] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  rw [hv] at hcorrect
  have hsource := hcorrect.mpr hglobal
  obtain ⟨d, hβd, hd⟩ := (eval_cnAbove_components _ b).mp hsource
  have hdC := (hθ.formula_absolute (by omega : max 2 (n + 2) ≤ n + 3) d).mp hd
  let := hdC.ordinal
  exact ⟨d.val, ordinal_mem_hierarchy_iff.mp d.property, hβd, hdC⟩

theorem cnCofinal_unbounded (n : ℕ) (β : V) [IsOrdinal β] :
    ∃ θ : V, β ∈ θ ∧ Cn (n + 2) θ ∧ CnCofinal (n + 2) θ := by
  obtain ⟨θ, hβθ, hθ⟩ := cn_unbounded (n + 3) β
  exact ⟨θ, hβθ, hθ.of_le (by omega), hθ.cnCofinal⟩

end ZFVP
