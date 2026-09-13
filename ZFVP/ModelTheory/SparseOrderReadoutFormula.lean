import ZFVP.ModelTheory.BoundedSparseOrderCertificate

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedSparseOrderReadoutFormula : SetTheorySemisentence 9 :=
  “R W T S a b C O E. !boundedSparseOrderCertificateFormula W T S a C O E ∧
    !boundedValueFormula R O b”

def sigmaOneSparseOrderReadoutFormula : SetTheorySemisentence 6 :=
  “R W T S a b. ∃ C, ∃ O, ∃ E, !boundedSparseOrderReadoutFormula R W T S a b C O E”

theorem boundedSparseOrderReadoutFormula_bounded : IsBoundedSetFormula boundedSparseOrderReadoutFormula :=
  .and (boundedSparseOrderCertificateFormula_bounded.subst _) (boundedValueFormula_bounded.subst _)

theorem sigmaOneSparseOrderReadoutFormula_sigmaOne : IsSigmaFormula 1 sigmaOneSparseOrderReadoutFormula :=
  .exs (.exs (.exs (.bounded (boundedSparseOrderReadoutFormula_bounded.subst _))))

variable {M : Type*} [SetStructure M]

theorem eval_sigmaOneSparseOrderReadoutFormula (R W T S a b : M) :
    sigmaOneSparseOrderReadoutFormula.Evalb ![R, W, T, S, a, b] ↔
      ∃ C O E : M, boundedSparseOrderReadoutFormula.Evalb ![R, W, T, S, a, b, C, O, E] := by
  simp [sigmaOneSparseOrderReadoutFormula, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedSparseOrderReadoutFormula (R W T S a b C O E : V) :
    boundedSparseOrderReadoutFormula.Evalb ![R, W, T, S, a, b, C, O, E] ↔
      boundedSparseOrderCertificateFormula.Evalb ![W, T, S, a, C, O, E] ∧ R = O ‘ b := by
  simp [boundedSparseOrderReadoutFormula, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]

theorem sparseOrderReadout_in_transitive {X : V} [IsTransitive X]
    (R W T S a b : SetDomain X) :
    sigmaOneSparseOrderReadoutFormula.Evalb ![R, W, T, S, a, b] ↔
      ∃ C ∈ X, ∃ O ∈ X, ∃ E ∈ X,
        boundedSparseOrderCertificateFormula.Evalb ![W.val, T.val, S.val, a.val, C, O, E] ∧
          R.val = O ‘ b.val := by
  rw [eval_sigmaOneSparseOrderReadoutFormula]
  have hb (C O E : SetDomain X) := bounded_formula_absolute X
    boundedSparseOrderReadoutFormula_bounded ![R, W, T, S, a, b, C, O, E]
  have hv (C O E : SetDomain X) :
      (fun i ↦ (![R, W, T, S, a, b, C, O, E] i).val) =
        ![R.val, W.val, T.val, S.val, a.val, b.val, C.val, O.val, E.val] := by
    funext i
    fin_cases i <;> rfl
  simp only [hv] at hb
  constructor
  · rintro ⟨C, O, E, he⟩
    refine ⟨C.val, C.property, O.val, O.property, E.val, E.property, ?_⟩
    apply (eval_boundedSparseOrderReadoutFormula _ _ _ _ _ _ _ _ _).mp
    exact (hb C O E).mp he
  · rintro ⟨C, hC, O, hO, E, hE, he⟩
    refine ⟨⟨C, hC⟩, ⟨O, hO⟩, ⟨E, hE⟩, ?_⟩
    apply (hb ⟨C, hC⟩ ⟨O, hO⟩ ⟨E, hE⟩).mpr
    exact (eval_boundedSparseOrderReadoutFormula _ _ _ _ _ _ _ _ _).mpr he

end ZFVP
