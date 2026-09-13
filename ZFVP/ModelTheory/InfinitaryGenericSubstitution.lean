import ZFVP.ModelTheory.InfinitaryCoordinateFormulaEvaluation
import ZFVP.ModelTheory.InfinitaryCoordinateTermFunctions

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension.CoordinateTerm
variable {L : Language}

def instantiate {n} (φ : Formula L n) (ts : Fin n → CoordinateTerm L) : Formula L (arity ts) :=
  φ.subst (fun i ↦ Formula.liftRightTerm (le_arity ts i) (ts i).2)

end HenkinConstruction.FragmentExtension.CoordinateTerm
namespace HenkinConstruction.FragmentExtension.GenericConditionChain
open HenkinLanguage FragmentClosure FiniteCondition
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}
  {p₀ : H.FiniteCondition} (C : GenericConditionChain H p₀)

theorem eval_iff_contains {n} (φ : Formula (limit L) n)
    (ts : Fin n → CoordinateTerm (limit L)) :
    CoordinateTerm.Eval C.point φ ts ↔ C.Contains (CoordinateTerm.instantiate φ ts) := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj⟩ := C.coordinate_cofinal (CoordinateTerm.arity ts)
    have hbound := (C.refines (Nat.le_max_right i j)).choose
    have h : CoordinateTerm.arity ts ≤ 1 + (C.point (max i j)).1 := by omega
    obtain ⟨hs, hh⟩ := CoordinateTerm.evalAt_persistent (C.refines (Nat.le_max_left i j)) hi
    refine ⟨max i j, h, ?_⟩
    intro b hb
    rw [CoordinateTerm.instantiate, Formula.weakEval_subst]
    simpa only [Formula.val_liftRightTerm, Function.comp_def, Formula.rightEmbed_trans] using hh b hb
  · rintro ⟨i, h, hh⟩
    refine ⟨i, fun j ↦ (CoordinateTerm.le_arity ts j).trans h, ?_⟩
    intro b hb
    have := hh b hb
    rw [CoordinateTerm.instantiate, Formula.weakEval_subst] at this
    simpa only [Formula.val_liftRightTerm, Function.comp_def, Formula.rightEmbed_trans] using this

theorem eval_neg_iff {n} {φ : Formula (limit L) n}
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (ts : Fin n → CoordinateTerm (limit L)) :
    CoordinateTerm.Eval C.point (.neg φ) ts ↔ ¬CoordinateTerm.Eval C.point φ ts := by
  rw [C.eval_iff_contains, C.eval_iff_contains]
  exact C.neg_iff (subst_closed hφ _)

theorem eval_conjunction_iff {n} {f : ℕ → Formula (limit L) n}
    (hf : ⟨n, .conj f⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (ts : Fin n → CoordinateTerm (limit L)) :
    CoordinateTerm.Eval C.point (.conj f) ts ↔ ∀ i, CoordinateTerm.Eval C.point (f i) ts := by
  rw [C.eval_iff_contains]
  change C.Contains (.conj (fun i ↦ CoordinateTerm.instantiate (f i) ts)) ↔ _
  exact (C.conjunction_iff (f := fun i ↦ CoordinateTerm.instantiate (f i) ts)
    (subst_closed hf (fun i ↦ Formula.liftRightTerm (CoordinateTerm.le_arity ts i) (ts i).2))).trans
      (forall_congr' (fun i ↦ (C.eval_iff_contains (f i) ts).symm))

end HenkinConstruction.FragmentExtension.GenericConditionChain
end ZFVP.Infinitary



