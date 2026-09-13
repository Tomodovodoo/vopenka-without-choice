import ZFVP.SetTheory.LeastRankCriterionCode
import ZFVP.SetTheory.LeastWitnessCodeBounds

/-! The least-rank-criterion certificate belongs to V_(theta+omega), as needed by the fragment structure. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem leastRankCriterionCertificate_mem {θ d b : V}
    (h : leastRankCriterionCertificateFormula.Evalb ![θ, d, b]) :
    d ∈ hierarchy (ordinalAdd θ ω) := by
  obtain ⟨hθ, _, hd⟩ := (eval_leastRankCriterionCertificateFormula θ d b).mp h
  let := hθ.1
  have hn := ((leastRankCriterionAbove_iff b θ).mp (leastRankCriterionCertificate_sound h)).2.2
  have hw := boundedNoEarlierRankCriterionMatrix_complete hθ.2.2.1 hn
  exact ((eval_leastWitnessCodeFormula _ _ _).mp hd).mem_hierarchy_limit
    (fun _ ↦ ordinalAdd_omega_succ_closed θ) (hierarchy_mem (ordinalAdd_omega_gt θ)) hw

theorem leastRankCriterionCode_mem {c b : V}
    (h : leastRankCriterionCodeFormula.Evalb ![c, b]) :
    ∃ θ d : V, c = ⟨θ, d⟩ₖ ∧ IsLeastRankCriterionAbove b θ ∧
      d ∈ hierarchy (ordinalAdd θ ω) ∧ c ∈ hierarchy (ordinalAdd θ ω) := by
  obtain ⟨θ, d, rfl, hd⟩ := (eval_leastRankCriterionCodeFormula c b).mp h
  have hθ := leastRankCriterionCertificate_sound hd
  let := hθ.1
  have hm := leastRankCriterionCertificate_mem hd
  refine ⟨θ, d, rfl, hθ, hm, ?_⟩
  exact kpair_mem_hierarchy_limit (fun _ ↦ ordinalAdd_omega_succ_closed θ)
    (ordinal_subset_hierarchy _ _ (ordinalAdd_omega_gt θ)) hm

end ZFVP
