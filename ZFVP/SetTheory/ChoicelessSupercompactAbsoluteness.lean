import ZFVP.SetTheory.ChoicelessSupercompact
import ZFVP.ModelTheory.EmbeddingAbsoluteness

/-! Witnesses below a correct target rank can be read in a surrounding rank
with one less correctness level. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

theorem eval_choicelessSupercompactWitness_components {W : Type*} [SetStructure W]
    (n : ℕ) (α γ μ a : W) :
    (choicelessSupercompactWitnessFormula n).Evalb ![α, γ, μ, a] ↔
      ∃ ν A B x e κ : W, ν ∈ γ ∧ (cnFormula n).Evalb ![ν] ∧
        piOneHierarchyFormula.Evalb ![A, ν] ∧ piOneHierarchyFormula.Evalb ![B, μ] ∧
        x ∈ A ∧ piOneMembershipEmbeddingFormula.Evalb ![A, B, e] ∧
        boundedCriticalPointFormula.Evalb ![A, e, κ] ∧ α ∈ κ ∧
        boundedPairMemberFormula.Evalb ![e, x, a] := by
  simp [choicelessSupercompactWitnessFormula, Semiformula.eval_substs,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem Cn.choicelessSupercompactWitness_absolute {k : ℕ} {δ : V}
    (hδ : Cn (k + 1) δ) (α γ μ a : SetDomain (hierarchy δ))
    (hμ : Cn (k + 2) μ.val) (hγμ : γ.val ∈ μ.val) :
    (choicelessSupercompactWitnessFormula (k + 2)).Evalb ![α, γ, μ, a] ↔
      ChoicelessSupercompactWitness (k + 2) α.val γ.val μ.val a.val := by
  let := hδ.ordinal
  let := hμ.ordinal
  let : IsOrdinal γ.val := IsOrdinal.of_mem hγμ
  let := hierarchy_transitive δ
  have hμδ : μ.val ∈ δ := ordinal_mem_hierarchy_iff.mp μ.property
  rw [eval_choicelessSupercompactWitness_components]
  constructor
  · rintro ⟨ν, A, B, x, e, κ, hνγ, hν, hA, hB, hx, he, hc, hακ, hp⟩
    have hAA := (hδ.hierarchy_formula_correct A ν).mp hA
    have hBB := (hδ.hierarchy_formula_correct B μ).mp hB
    let := hAA.1
    let := hierarchy_transitive ν.val
    have hνμ : ν.val ∈ μ.val := IsOrdinal.toIsTransitive.mem_trans hνγ hγμ
    have hνC : Cn (k + 2) ν.val := cn_sandwich hδ hμ hνμ hμδ hν
    have hef := (hδ.membershipEmbedding_absolute A B e).mp he
    rw [hAA.2, hBB.2] at hef
    have hcg : CriticalPointGraphSpec A.val e.val κ.val :=
      (hδ.defined_correct (p := .pi) (.bounded boundedCriticalPointFormula_bounded)
        (fun v ↦ CriticalPointGraphSpec (v 0) (v 1) (v 2)) ![A, e, κ]).mp hc
    rw [hAA.2] at hcg
    have hp' : ⟨x.val, a.val⟩ₖ ∈ e.val :=
      (hδ.defined_correct (p := .pi) (.bounded boundedPairMemberFormula_bounded)
        (fun v ↦ ⟨v 1, v 2⟩ₖ ∈ v 0) ![e, x, a]).mp hp
    have hx' : x.val ∈ hierarchy ν.val := hAA.2 ▸ hx
    let := IsFunction.of_mem hef.function
    exact ⟨hμ.ordinal, ν.val, x.val, e.val, κ.val, hνγ, hνC, hx', hef,
      (criticalPoint_iff_graphSpec hef.function).mpr hcg, hακ, value_eq_of_kpair_mem hp'⟩
  · rintro ⟨_, ν, x, e, κ, hνγ, hν, hx, he, hc, hακ, hv⟩
    let := hν.ordinal
    let := hierarchy_transitive ν
    let := IsFunction.of_mem he.function
    have hνμ : ν ∈ μ.val := IsOrdinal.toIsTransitive.mem_trans hνγ hγμ
    have hνδ : ν ∈ δ := IsOrdinal.toIsTransitive.mem_trans hνμ hμδ
    have hAV := hierarchy_mem hνδ
    have hBV := hierarchy_mem hμδ
    have hxV := (hierarchy_transitive δ).mem_trans hx hAV
    have heV := (hierarchy_transitive δ).mem_trans he.function
      (function_mem_hierarchy_limit hδ.successor_closed hAV hBV)
    have hκV := (hierarchy_transitive δ).mem_trans hc.mem_domain hAV
    let v : SetDomain (hierarchy δ) := ⟨ν, ordinal_subset_hierarchy δ ν hνδ⟩
    let A : SetDomain (hierarchy δ) := ⟨hierarchy ν, hAV⟩
    let B : SetDomain (hierarchy δ) := ⟨hierarchy μ.val, hBV⟩
    let xx : SetDomain (hierarchy δ) := ⟨x, hxV⟩
    let ee : SetDomain (hierarchy δ) := ⟨e, heV⟩
    let kk : SetDomain (hierarchy δ) := ⟨κ, hκV⟩
    refine ⟨v, A, B, xx, ee, kk, hνγ, hν.into_lower_rank hδ hνδ,
      (hδ.hierarchy_formula_correct A v).mpr ⟨hν.ordinal, rfl⟩,
      (hδ.hierarchy_formula_correct B μ).mpr ⟨hμ.ordinal, rfl⟩, hx,
      (hδ.membershipEmbedding_absolute A B ee).mpr he, ?_, hακ, ?_⟩
    · exact (hδ.defined_correct (p := .pi) (.bounded boundedCriticalPointFormula_bounded)
        (fun v ↦ CriticalPointGraphSpec (v 0) (v 1) (v 2)) ![A, ee, kk]).mpr
          ((criticalPoint_iff_graphSpec he.function).mp hc)
    · apply (hδ.defined_correct (p := .pi) (.bounded boundedPairMemberFormula_bounded)
        (fun v ↦ ⟨v 1, v 2⟩ₖ ∈ v 0) ![ee, xx, a]).mpr
      change ⟨x, a.val⟩ₖ ∈ e
      apply kpair_mem_iff_value.mpr
      exact ⟨by rw [domain_eq_of_mem_function he.function]; exact hx, hv⟩

end ZFVP
