import ZFVP.ModelTheory.InternalArithmeticGraphs
import ZFVP.ModelTheory.InternalPrimitiveProgramEquations

/-! Arithmetic and set-theoretic program evaluation agree on all internal natural inputs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem evalArithmetic_prec_agreement (a b : PrimitiveProgram)
    (ha : ∀ x : InternalArithmetic V, internalArithmeticVal (a.evalArithmetic x) = a.evalSet (internalArithmeticVal x))
    (hb : ∀ x : InternalArithmetic V, internalArithmeticVal (b.evalArithmetic x) = b.evalSet (internalArithmeticVal x))
    (z n : InternalArithmetic V) :
    internalArithmeticVal ((PrimitiveProgram.prec a b).evalArithmetic (Arithmetic.pair z n)) =
      naturalPrimitive a.evalSet b.evalSet (evalSet_definable a) (evalSet_definable b)
        (internalArithmeticVal z) (internalArithmeticVal n) := by
  let R := naturalPrimitive a.evalSet b.evalSet (evalSet_definable a) (evalSet_definable b) (internalArithmeticVal z)
  let φ := arithmeticInZF.translate (PrimitiveProgram.prec a b).arithmeticFormula.val
  let P : V → Prop := fun t ↦ φ.Evalb ![R t, naturalSquarePair (internalArithmeticVal z) t]
  have hR : ℒₛₑₜ-function₁ R := naturalPrimitive_definable _ _ _ _ _
  have hE : Language.Definable ℒₛₑₜ (fun v : Fin 2 → V ↦ φ.Evalb v) :=
    (show Defined (fun v : Fin 2 → V ↦ φ.Evalb v) φ from ⟨fun _ ↦ Iff.rfl⟩).to_definable
  have hP : ℒₛₑₜ-predicate P := by
    apply Language.Definable.substitution hE
      (f := fun i (v : Fin 1 → V) ↦ (![R (v 0), naturalSquarePair (internalArithmeticVal z) (v 0)] i))
    intro i
    fin_cases i
    · exact hR
    · change ℒₛₑₜ-function₁ (fun t ↦ naturalSquarePair (internalArithmeticVal z) t)
      definability
  have hSem (m : InternalArithmetic V) : P (internalArithmeticVal m) ↔
      R (internalArithmeticVal m) =
        internalArithmeticVal ((PrimitiveProgram.prec a b).evalArithmetic (Arithmetic.pair z m)) := by
    have hy : R (internalArithmeticVal m) ∈ (ω : V) :=
      naturalPrimitive_natural _ _ _ _ a.realization.natural b.realization.natural
        (internalArithmeticVal_mem z) (internalArithmeticVal_mem m)
    have h := internalArithmetic_graph_translation (PrimitiveProgram.prec a b).arithmeticFormula
      (PrimitiveProgram.prec a b).evalArithmetic (evalArithmetic_defined _) (Arithmetic.pair z m) hy
    simpa only [internalArithmeticVal_pair, P, φ] using h
  have h0 : P 0 := by
    have h := (hSem 0).mpr (by
      change R (internalArithmeticVal 0) = _
      rw [internalArithmeticVal_zero, evalArithmetic_prec_zero]
      change naturalPrimitive _ _ _ _ _ 0 = _
      rw [naturalPrimitive_zero]
      exact (ha z).symm)
    simpa only [internalArithmeticVal_zero] using h
  have hs : ∀ t ∈ (ω : V), P t → P (SetTheory.succ t) := by
    intro t ht ih
    obtain ⟨m, rfl⟩ := internalArithmeticVal_surjective ht
    have hm1 : internalArithmeticVal (m + 1) = SetTheory.succ (internalArithmeticVal m) := by
      rw [internalArithmeticVal_add, internalArithmeticVal_one, ordinalAdd_one_natural (internalArithmeticVal_mem m)]
    have h := (hSem (m + 1)).mpr (by
      change naturalPrimitive _ _ _ _ _ (internalArithmeticVal (m + 1)) = _
      rw [hm1, naturalPrimitive_succ _ _ _ _ _ (internalArithmeticVal_mem m),
        evalArithmetic_prec_succ, hb, internalArithmeticVal_pair, internalArithmeticVal_pair,
        ← (hSem m).mp ih])
    simpa only [hm1] using h
  exact ((hSem n).mp (naturalNumber_induction P hP h0 hs _ (internalArithmeticVal_mem n))).symm

theorem evalArithmetic_agreement (c : PrimitiveProgram) (x : InternalArithmetic V) :
    internalArithmeticVal (c.evalArithmetic x) = c.evalSet (internalArithmeticVal x) := by
  induction c generalizing x with
  | zero => simp only [evalArithmetic_zero, internalArithmeticVal_zero, evalSet_zero]
  | succ =>
    simp only [evalArithmetic_succ, internalArithmeticVal_add, internalArithmeticVal_one, evalSet_succ]
    exact ordinalAdd_one_natural (internalArithmeticVal_mem x)
  | left =>
    exact (congrArg Prod.fst (naturalSquareUnpair_internalArithmeticVal x)).symm
  | right =>
    exact (congrArg Prod.snd (naturalSquareUnpair_internalArithmeticVal x)).symm
  | pair a b ha hb =>
    rw [evalArithmetic_pair, internalArithmeticVal_pair, ha, hb, evalSet_pair]
  | comp a b ha hb =>
    rw [evalArithmetic_comp, ha, hb, evalSet_comp]
  | prec a b ha hb =>
    calc
      internalArithmeticVal ((PrimitiveProgram.prec a b).evalArithmetic x) =
          internalArithmeticVal ((PrimitiveProgram.prec a b).evalArithmetic
            (Arithmetic.pair (Arithmetic.pi₁ x) (Arithmetic.pi₂ x))) := by rw [Arithmetic.pair_unpair]
      _ = naturalPrimitive a.evalSet b.evalSet (evalSet_definable a) (evalSet_definable b)
          (internalArithmeticVal (Arithmetic.pi₁ x)) (internalArithmeticVal (Arithmetic.pi₂ x)) :=
        evalArithmetic_prec_agreement a b ha hb _ _
      _ = (PrimitiveProgram.prec a b).evalSet
          (naturalSquarePair (internalArithmeticVal (Arithmetic.pi₁ x)) (internalArithmeticVal (Arithmetic.pi₂ x))) :=
        (evalSet_prec_pair a b (internalArithmeticVal_mem _) (internalArithmeticVal_mem _)).symm
      _ = (PrimitiveProgram.prec a b).evalSet (internalArithmeticVal x) := by
        rw [← internalArithmeticVal_pair, Arithmetic.pair_unpair]

theorem arithmeticFormula_translation_agreement (c : PrimitiveProgram) {x y : V}
    (hx : x ∈ (ω : V)) (hy : y ∈ (ω : V)) :
    (arithmeticInZF.translate c.arithmeticFormula.val).Evalb ![y, x] ↔ c.formula.Evalb ![y, x] := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hx
  rw [internalArithmetic_graph_translation c.arithmeticFormula c.evalArithmetic (evalArithmetic_defined c) u hy,
    evalArithmetic_agreement, eval_formula_iff]

end PrimitiveProgram
end ZFVP
