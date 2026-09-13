import ZFVP.SetTheory.PiWitnessRankStageFormula
import ZFVP.SetTheory.PiWitnessRankStructures
import ZFVP.SetTheory.BoundedWitnessFamilyTuple

/-! The marked parameters can be bound inside the structure universe without increasing complexity. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedPiWitnessMarkerDataFormula : SetTheorySemisentence 15 :=
  “N t e α ν U W X c θ d A M ρ B. !sequenceSupportFormula A ∧ !(boundedNumeralFormula 8) N ∧
    !boundedWitnessFamilyTupleFormula A e ν U W X c ∧ !(boundedStandardTupleFormula 8) A t α ν U W X c θ d”

def piWitnessMarkedDataFormula {n : ℕ} (k : ℕ) (ψ : SetTheorySemisentence (n + 2)) :
    SetTheorySemisentence (n + 15) :=
  (boundedPiWitnessMarkerDataFormula.subst
    ![.bvar 0, .bvar 1, .bvar 2, .bvar 3, .bvar 4, .bvar 5, .bvar 6, .bvar 7,
      .bvar 8, .bvar 9, .bvar 10, .bvar 11, .bvar 12, .bvar 13, .bvar 14]).and
    ((piOneIndexedMarkerStructureFormula.subst ![.bvar 12, .bvar 14, .bvar 0, .bvar 11, .bvar 1]).and
      ((piWitnessRankStageFormula k ψ).subst
        (.bvar 11 :> .bvar 13 :> .bvar 3 :> .bvar 2 :> .bvar 9 :> .bvar 10 :>
          fun i : Fin n ↦ .bvar ⟨i.val + 15, by omega⟩)))

def piWitnessMarkedParametersFormula {n : ℕ} (k : ℕ) (ψ : SetTheorySemisentence (n + 2)) :
    SetTheorySemisentence (n + 12) :=
  boundedSetExs (.bvar 8) (boundedSetExs (.bvar 9) (boundedSetExs (.bvar 10) (piWitnessMarkedDataFormula k ψ)))

theorem boundedPiWitnessMarkerDataFormula_bounded : IsBoundedSetFormula boundedPiWitnessMarkerDataFormula :=
  .and (sequenceSupportFormula_bounded.subst _) (.and ((boundedNumeralFormula_bounded 8).subst _)
    (.and (boundedWitnessFamilyTupleFormula_bounded.subst _) ((boundedStandardTupleFormula_bounded 8).subst _)))

theorem piWitnessMarkedDataFormula_pi {n k : ℕ} {ψ : SetTheorySemisentence (n + 2)}
    (hψ : IsPiFormula (k + 1) ψ) : IsPiFormula (k + 1) (piWitnessMarkedDataFormula k ψ) :=
  .and (.bounded (boundedPiWitnessMarkerDataFormula_bounded.subst _))
    (.and ((piOneIndexedMarkerStructureFormula_piOne.mono (by omega)).subst _)
      ((piWitnessRankStageFormula_pi hψ).subst _))

theorem piWitnessMarkedParametersFormula_pi {n k : ℕ} {ψ : SetTheorySemisentence (n + 2)}
    (hψ : IsPiFormula (k + 1) ψ) : IsPiFormula (k + 1) (piWitnessMarkedParametersFormula k ψ) :=
  .boundedExs (.bvar 8) (.boundedExs (.bvar 9) (.boundedExs (.bvar 10) (piWitnessMarkedDataFormula_pi hψ)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_marked_and {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.and ψ).Evalb v ↔ φ.Evalb v ∧ ψ.Evalb v := Iff.rfl

theorem boundedPiWitnessMarkerData_support {N t e α ν U W X c θ d A M ρ B : V}
    (h : boundedPiWitnessMarkerDataFormula.Evalb ![N, t, e, α, ν, U, W, X, c, θ, d, A, M, ρ, B]) :
    IsSequenceSupport A := by
  have hs : sequenceSupportFormula.Evalb ![A] := h.1
  exact (Defined.eval_iff ![A]).mp hs

theorem eval_boundedPiWitnessMarkerDataFormula (N t e α ν U W X c θ d A M ρ B : V)
    [IsSequenceSupport A] (he : e ∈ A) :
    boundedPiWitnessMarkerDataFormula.Evalb ![N, t, e, α, ν, U, W, X, c, θ, d, A, M, ρ, B] ↔
      N = (8 : V) ∧ e = ⟨ν, ⟨U, ⟨W, ⟨X, c⟩ₖ⟩ₖ⟩ₖ⟩ₖ ∧
        t = standardTuple ![α, ν, U, W, X, c, θ, d] ∧
          ∀ i : Fin 8, (![α, ν, U, W, X, c, θ, d] i) ∈ A := by
  simp [boundedPiWitnessMarkerDataFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, eval_boundedWitnessFamilyTupleFormula he,
    eval_boundedStandardTupleFormula, show IsSequenceSupport A from inferInstance]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_piWitnessMarkedDataFormula {n k : ℕ} (ψ : SetTheorySemisentence (n + 2))
    (N t e α ν U W X c θ d A M ρ B : V) (v : Fin n → V) :
    (piWitnessMarkedDataFormula k ψ).Evalb
      (N :> t :> e :> α :> ν :> U :> W :> X :> c :> θ :> d :> A :> M :> ρ :> B :> v) ↔
      boundedPiWitnessMarkerDataFormula.Evalb ![N, t, e, α, ν, U, W, X, c, θ, d, A, M, ρ, B] ∧
        piOneIndexedMarkerStructureFormula.Evalb ![M, B, N, A, t] ∧
          (piWitnessRankStageFormula k ψ).Evalb (A :> ρ :> α :> e :> θ :> d :> v) := by
  simp [piWitnessMarkedDataFormula, eval_marked_and, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]

theorem eval_piWitnessMarkedParametersFormula {n k : ℕ} (ψ : SetTheorySemisentence (n + 2))
    (α ν U W X c θ d A M ρ B : V) [IsOrdinal ρ] (v : Fin n → V) :
    (piWitnessMarkedParametersFormula k ψ).Evalb (α :> ν :> U :> W :> X :> c :> θ :> d :> A :> M :> ρ :> B :> v) ↔
      B ⊆ A ∧ IsPiWitnessRankStage k ψ ρ α ⟨ν, ⟨U, ⟨W, ⟨X, c⟩ₖ⟩ₖ⟩ₖ⟩ₖ θ d v ∧
        A = hierarchy (ordinalAdd θ ω) ∧
          M = indexedMarkerStructure B (8 : V) A (standardTuple ![α, ν, U, W, X, c, θ, d]) := by
  simp [piWitnessMarkedParametersFormula, eval_boundedSetExs, eval_piWitnessMarkedDataFormula]
  constructor
  · rintro ⟨e, he, t, _, N, _, hd, hM, hs⟩
    let := boundedPiWitnessMarkerData_support hd
    obtain ⟨rfl, rfl, rfl, _⟩ := (eval_boundedPiWitnessMarkerDataFormula _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he).mp hd
    obtain ⟨hBA, _, hM⟩ := (eval_piOneIndexedMarkerStructureFormula _ _ _ _ _).mp hM
    obtain ⟨hA, hs⟩ := (eval_piWitnessRankStageFormula ψ _ _ _ _ _ _ v).mp hs
    exact ⟨hBA, hs, hA, hM⟩
  · rintro ⟨hBA, hs, rfl, rfl⟩
    let := hs.rankCriterion.1
    let := hierarchy_isSequenceSupport
      (IsOrdinal.toIsTransitive.mem_trans hs.rankCriterion.2.1 (ordinalAdd_omega_gt θ))
      (fun _ ↦ ordinalAdd_omega_succ_closed θ)
    have hv := hs.marker_values_mem
    have he : ⟨ν, ⟨U, ⟨W, ⟨X, c⟩ₖ⟩ₖ⟩ₖ⟩ₖ ∈ hierarchy (ordinalAdd θ ω) :=
      hierarchy_mono (IsOrdinal.toIsTransitive.transitive θ (ordinalAdd_omega_gt θ)) _ hs.bounds.2.2.1
    refine ⟨_, he, _, standardTuple_mem_support _ hv, (8 : V), IsCodingSupport.numeral_mem 8, ?_, ?_, ?_⟩
    · exact (eval_boundedPiWitnessMarkerDataFormula _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he).mpr ⟨rfl, rfl, rfl, hv⟩
    · exact (eval_piOneIndexedMarkerStructureFormula _ _ _ _ _).mpr ⟨hBA, standardTuple_mem_function _ hv, rfl⟩
    · exact (eval_piWitnessRankStageFormula ψ _ _ _ _ _ _ v).mpr ⟨rfl, hs⟩

end ZFVP
