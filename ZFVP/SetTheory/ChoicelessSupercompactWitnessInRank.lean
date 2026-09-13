import ZFVP.SetTheory.ChoicelessSupercompactAbsoluteness

/-! A supercompactness witness can be read inside a lower-correct rank
without requiring external correctness of its target height. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem Cn.supercompactWitness_into_rank {n : ℕ} {θ : V} (hθ : Cn (n + 1) θ)
    (α γ μ a : SetDomain (hierarchy θ))
    (h : ChoicelessSupercompactWitness (n + 2) α.val γ.val μ.val a.val) :
    (choicelessSupercompactWitnessFormula (n + 2)).Evalb ![α, γ, μ, a] := by
  let := hθ.ordinal
  let := hierarchy_transitive θ
  obtain ⟨hμ, ν, x, e, κ, hνγ, hν, hx, he, hc, hακ, hv⟩ := h
  let := hμ
  let := hν.ordinal
  let := hierarchy_transitive ν
  let := IsFunction.of_mem he.function
  have hνV := (hierarchy_transitive θ).mem_trans hνγ γ.property
  have hAV := hθ.hierarchy_closed hν.ordinal hνV
  have hBV := hθ.hierarchy_closed hμ μ.property
  have hxV := (hierarchy_transitive θ).mem_trans hx hAV
  have heV := (hierarchy_transitive θ).mem_trans he.function
    (function_mem_hierarchy_limit hθ.successor_closed hAV hBV)
  have hκV := (hierarchy_transitive θ).mem_trans hc.mem_domain hAV
  let v : SetDomain (hierarchy θ) := ⟨ν, hνV⟩
  let A : SetDomain (hierarchy θ) := ⟨hierarchy ν, hAV⟩
  let B : SetDomain (hierarchy θ) := ⟨hierarchy μ.val, hBV⟩
  let xx : SetDomain (hierarchy θ) := ⟨x, hxV⟩
  let ee : SetDomain (hierarchy θ) := ⟨e, heV⟩
  let kk : SetDomain (hierarchy θ) := ⟨κ, hκV⟩
  apply (eval_choicelessSupercompactWitness_components _ α γ μ a).mpr
  refine ⟨v, A, B, xx, ee, kk, hνγ,
    hν.into_lower_rank hθ (ordinal_mem_hierarchy_iff.mp hνV),
    (hθ.hierarchy_formula_correct A v).mpr ⟨hν.ordinal, rfl⟩,
    (hθ.hierarchy_formula_correct B μ).mpr ⟨hμ, rfl⟩, hx,
    (hθ.membershipEmbedding_absolute A B ee).mpr he, ?_, hακ, ?_⟩
  · exact (hθ.defined_correct (p := .pi) (.bounded boundedCriticalPointFormula_bounded)
      (fun v ↦ CriticalPointGraphSpec (v 0) (v 1) (v 2)) ![A, ee, kk]).mpr
        ((criticalPoint_iff_graphSpec he.function).mp hc)
  · apply (hθ.defined_correct (p := .pi) (.bounded boundedPairMemberFormula_bounded)
      (fun v ↦ ⟨v 1, v 2⟩ₖ ∈ v 0) ![ee, xx, a]).mpr
    change ⟨x, a.val⟩ₖ ∈ e
    apply kpair_mem_iff_value.mpr
    exact ⟨by rw [domain_eq_of_mem_function he.function]; exact hx, hv⟩

end ZFVP
