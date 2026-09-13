import ZFVP.SetTheory.PiWitnessMarkedParameters

/-! A Pi class of the paper's eight-marker witness structures. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def piWitnessRankClassBodyFormula {n : ℕ} (k : ℕ) (ψ : SetTheorySemisentence (n + 2)) :
    SetTheorySemisentence (n + 5) :=
  boundedSetExs (.bvar 0) (boundedSetExs (.bvar 1) (boundedSetExs (.bvar 2) (boundedSetExs (.bvar 3)
    (boundedSetExs (.bvar 4) (boundedSetExs (.bvar 5) (boundedSetExs (.bvar 6) (boundedSetExs (.bvar 7)
      ((piWitnessMarkedParametersFormula k ψ).subst
        (.bvar 7 :> .bvar 6 :> .bvar 5 :> .bvar 4 :> .bvar 3 :> .bvar 2 :> .bvar 1 :> .bvar 0 :>
          .bvar 8 :> .bvar 10 :> .bvar 11 :> .bvar 12 :>
            fun i : Fin n ↦ .bvar ⟨i.val + 13, by omega⟩)))))))))

def piWitnessRankClassFormula {n : ℕ} (k : ℕ) (ψ : SetTheorySemisentence (n + 2)) :
    SetTheorySemisentence (n + 3) := boundedPairBind (.bvar 0) (piWitnessRankClassBodyFormula k ψ)

theorem piWitnessRankClassBodyFormula_pi {n k : ℕ} {ψ : SetTheorySemisentence (n + 2)}
    (hψ : IsPiFormula (k + 1) ψ) : IsPiFormula (k + 1) (piWitnessRankClassBodyFormula k ψ) := by
  refine .boundedExs (.bvar 0) (.boundedExs (.bvar 1) (.boundedExs (.bvar 2) (.boundedExs (.bvar 3) ?_)))
  refine .boundedExs (.bvar 4) (.boundedExs (.bvar 5) (.boundedExs (.bvar 6) (.boundedExs (.bvar 7) ?_)))
  exact (piWitnessMarkedParametersFormula_pi hψ).subst _

theorem piWitnessRankClassFormula_pi {n k : ℕ} {ψ : SetTheorySemisentence (n + 2)}
    (hψ : IsPiFormula (k + 1) ψ) : IsPiFormula (k + 1) (piWitnessRankClassFormula k ψ) :=
  boundedPairBind_levy _ (piWitnessRankClassBodyFormula_pi hψ)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_piWitnessRankClassBodyFormula {n k : ℕ} (ψ : SetTheorySemisentence (n + 2))
    (A C M ρ B : V) [IsOrdinal ρ] (v : Fin n → V) :
    (piWitnessRankClassBodyFormula k ψ).Evalb (A :> C :> M :> ρ :> B :> v) ↔
      ∃ α ∈ A, ∃ ν ∈ A, ∃ U ∈ A, ∃ W ∈ A, ∃ X ∈ A, ∃ c ∈ A, ∃ θ ∈ A, ∃ d ∈ A,
        B ⊆ A ∧ IsPiWitnessRankStage k ψ ρ α ⟨ν, ⟨U, ⟨W, ⟨X, c⟩ₖ⟩ₖ⟩ₖ⟩ₖ θ d v ∧
          A = hierarchy (ordinalAdd θ ω) ∧
            M = indexedMarkerStructure B (8 : V) A (standardTuple ![α, ν, U, W, X, c, θ, d]) := by
  simp [piWitnessRankClassBodyFormula, eval_boundedSetExs, Semiformula.eval_substs,
    Matrix.comp_vecCons', Function.comp_def, eval_piWitnessMarkedParametersFormula,
    Semiformula.Evalb]

theorem eval_piWitnessRankClassFormula {n k : ℕ} (ψ : SetTheorySemisentence (n + 2))
    (M ρ : V) [IsOrdinal ρ] (v : Fin n → V) :
    (piWitnessRankClassFormula k ψ).Evalb (M :> ρ :> hierarchy ρ :> v) ↔
      IsPiWitnessRankStructure k ψ ρ M v := by
  rw [piWitnessRankClassFormula, eval_boundedPairBind]
  simp only [Semiterm.val_bvar, Matrix.cons_val_zero, eval_piWitnessRankClassBodyFormula]
  constructor
  · rintro ⟨A, C, _, α, _, ν, _, U, _, W, _, X, _, c, _, θ, _, d, _, _, hs, rfl, hM⟩
    exact ⟨α, ν, U, W, X, c, θ, d, hs, hM⟩
  · rintro ⟨α, ν, U, W, X, c, θ, d, hs, rfl⟩
    let := hs.rankCriterion.1
    have hv := hs.marker_values_mem
    have hρδ := IsOrdinal.toIsTransitive.mem_trans hs.bounds.1 (ordinalAdd_omega_gt θ)
    refine ⟨hierarchy (ordinalAdd θ ω), _, rfl,
      α, hv 0, ν, hv 1, U, hv 2, W, hv 3, X, hv 4, c, hv 5, θ, hv 6, d, hv 7,
      hierarchy_mono (IsOrdinal.toIsTransitive.transitive ρ hρδ), hs, rfl, rfl⟩

end ZFVP
