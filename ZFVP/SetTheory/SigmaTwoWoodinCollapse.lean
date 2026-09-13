import ZFVP.SetTheory.WoodinCollapseFormula

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaTwoWoodinCollapseFormula : SetTheorySemisentence 3 :=
  “P κ δ. ∃ H, !piOneHierarchyFormula H δ ∧
    (∀ p ∈ P, !sigmaOneWoodinConditionFormula p κ δ H) ∧
    ∀ p, !sigmaOneWoodinConditionFormula p κ δ H → p ∈ P”

theorem sigmaTwoWoodinCollapseFormula_sigmaTwo : IsSigmaFormula 2 sigmaTwoWoodinCollapseFormula :=
  .exs (.and (.raise (piOneHierarchyFormula_piOne.subst _))
    (.and (.raise (.boundedAll (.bvar 1) (sigmaOneWoodinConditionFormula_sigmaOne.subst _)))
      (.raise (IsLevyFormula.all (.or (sigmaOneWoodinConditionFormula_sigmaOne.subst _).neg
        (.bounded (.rel _ _)))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaTwoWoodinCollapseFormula (P κ δ : V) :
    sigmaTwoWoodinCollapseFormula.Evalb ![P, κ, δ] ↔
      IsOrdinal δ ∧ P = woodinCollapse κ δ := by
  have he : sigmaTwoWoodinCollapseFormula.Evalb ![P, κ, δ] ↔
      ∃ H : V, (IsOrdinal δ ∧ H = hierarchy δ) ∧
        (∀ p ∈ P, sigmaOneWoodinConditionFormula.Evalb ![p, κ, δ, H]) ∧
        ∀ p, sigmaOneWoodinConditionFormula.Evalb ![p, κ, δ, H] → p ∈ P := by
    simp [sigmaTwoWoodinCollapseFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, IsHierarchySegment, Semiformula.Evalb]
  rw [he]
  constructor
  · rintro ⟨H, ⟨hd, rfl⟩, hf, hb⟩
    let := hd
    refine ⟨hd, mem_ext fun p ↦ ?_⟩
    exact ⟨fun hp ↦ (eval_sigmaOneWoodinConditionFormula p κ δ).mp (hf p hp),
      fun hp ↦ hb p ((eval_sigmaOneWoodinConditionFormula p κ δ).mpr hp)⟩
  · rintro ⟨hd, rfl⟩
    let := hd
    exact ⟨hierarchy δ, ⟨hd, rfl⟩,
      fun p ↦ (eval_sigmaOneWoodinConditionFormula p κ δ).mpr,
      fun p ↦ (eval_sigmaOneWoodinConditionFormula p κ δ).mp⟩

end ZFVP
