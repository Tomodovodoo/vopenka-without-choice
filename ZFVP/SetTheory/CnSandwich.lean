import ZFVP.SetTheory.CorrectDomainSandwich

/-! The correctness sandwich of Mohammd Lemma 6.3 at positive lower levels. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

theorem eval_cnFormula_successor {W : Type*} [SetStructure W] (k : ℕ) (α : W) :
    (cnFormula (k + 1)).Evalb ![α] ↔ IsOrdinal.dfn.Evalb ![α] ∧
      ∀ A : W, piOneHierarchyFormula.Evalb ![A, α] → (correctDomainFormula (k + 1)).Evalb ![A] := by
  simp [cnFormula, piCorrectRankStageFormula]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem cn_sandwich {k : ℕ} {α β γ : V} (hγ : Cn (k + 1) γ) (hβ : Cn (k + 2) β)
    (hαβ : α ∈ β) (hβγ : β ∈ γ)
    (hα : (cnFormula (k + 2)).Evalb (M := SetDomain (hierarchy γ))
      ![⟨α, by
        let := hγ.ordinal
        exact ordinal_subset_hierarchy γ α (IsOrdinal.toIsTransitive.mem_trans hαβ hβγ)⟩]) :
    Cn (k + 2) α := by
  let := hγ.ordinal
  let := hβ.ordinal
  let : IsOrdinal α := IsOrdinal.of_mem hαβ
  have hαγ : α ∈ γ := IsOrdinal.toIsTransitive.mem_trans hαβ hβγ
  have hαV := ordinal_subset_hierarchy γ α hαγ
  have hAV := hierarchy_mem hαγ
  have hBV := hierarchy_mem hβγ
  let a : SetDomain (hierarchy γ) := ⟨α, hαV⟩
  let A : SetDomain (hierarchy γ) := ⟨hierarchy α, hAV⟩
  have hAE := ((eval_cnFormula_successor (k + 1) a).mp hα).2 A
    ((hγ.hierarchy_formula_correct A a).mpr ⟨inferInstance, rfl⟩)
  apply (cn_successor_iff (k + 1) α).mpr
  refine ⟨inferInstance, ?_⟩
  exact correctDomain_sandwich hγ hAV hBV
    (hierarchy_mono (IsOrdinal.toIsTransitive.transitive α hαβ))
    ((cn_successor_iff (k + 1) β).mp hβ).2 hAE

theorem Cn.into_lower_rank {k : ℕ} {α γ : V}
    (hα : Cn (k + 2) α) (hγ : Cn (k + 1) γ) (hαγ : α ∈ γ) :
    (cnFormula (k + 2)).Evalb (M := SetDomain (hierarchy γ))
      ![⟨α, by
        let := hγ.ordinal
        exact ordinal_subset_hierarchy γ α hαγ⟩] := by
  let := hα.ordinal
  let := hγ.ordinal
  let a : SetDomain (hierarchy γ) := ⟨α, ordinal_subset_hierarchy γ α hαγ⟩
  apply (eval_cnFormula_successor (k + 1) a).mpr
  refine ⟨?_, ?_⟩
  · exact (hγ.defined_correct (p := .pi) (.bounded isOrdinalFormula_bounded)
      (fun v ↦ IsOrdinal (v 0)) ![a]).mpr hα.ordinal
  · intro A hA
    have hEq : A.val = hierarchy α := ((hγ.hierarchy_formula_correct A a).mp hA).2
    have hAC : CorrectDomain (k + 2) A.val := by
      rw [hEq]
      exact ((cn_successor_iff (k + 1) α).mp hα).2
    exact correctDomain_into_rank hγ A.property hAC

end ZFVP
