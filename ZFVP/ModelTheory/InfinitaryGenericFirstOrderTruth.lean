import ZFVP.ModelTheory.InfinitaryGenericTermEvaluation
import ZFVP.ModelTheory.InfinitaryGenericExistential

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace Formula

@[simp] theorem weakEval_expandFirstOrder {L : Language} {M : Type*} [Structure L M]
    (Q : Set M → Prop) {n} (φ : Semisentence L n) (b : Fin n → M) :
    WeakEval Q (expandFirstOrder φ) b ↔ φ.Evalb b := by
  induction φ with
  | verum => rfl
  | falsum => exact iff_of_eq (propext not_true)
  | rel r ts => rfl
  | nrel r ts => rfl
  | and φ ψ ihφ ihψ =>
    rw [expandFirstOrder, weakEval_and]
    exact and_congr (ihφ b) (ihψ b)
  | or φ ψ ihφ ihψ =>
    rw [expandFirstOrder, weakEval_or]
    exact or_congr (ihφ b) (ihψ b)
  | all φ ih =>
    rw [expandFirstOrder, weakEval_all]
    exact forall_congr' fun x ↦ ih (x :> b)
  | exs φ ih => exact exists_congr fun x ↦ ih (x :> b)

end Formula
namespace HenkinConstruction.FragmentExtension.GenericConditionChain
open HenkinLanguage FragmentClosure FiniteCondition
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}
  {p₀ : H.FiniteCondition} (C : GenericConditionChain H p₀)

theorem termClass_surjective : Function.Surjective C.termClass := Quotient.mk_surjective

theorem forall_termClass (P : C.ExtensionDomain → Prop) :
    (∀ x, P x) ↔ ∀ t, P (C.termClass t) := C.termClass_surjective.forall

theorem exists_termClass (P : C.ExtensionDomain → Prop) :
    (∃ x, P x) ↔ ∃ t, P (C.termClass t) := C.termClass_surjective.exists

theorem termClass_cons {n} (t : CoordinateTerm (limit L))
    (ts : Fin n → CoordinateTerm (limit L)) :
    (fun i ↦ C.termClass ((t :> ts) i)) = C.termClass t :> (fun i ↦ C.termClass (ts i)) := by
  funext i
  cases i using Fin.cases <;> rfl

theorem eval_verum {n} (ts : Fin n → CoordinateTerm (limit L)) :
    CoordinateTerm.Eval C.point (.fo .verum) ts := by
  obtain ⟨k, hk⟩ := C.coordinate_cofinal (CoordinateTerm.arity ts)
  exact ⟨k, fun i ↦ (CoordinateTerm.le_arity ts i).trans hk, fun _ _ ↦ trivial⟩

theorem eval_and_iff {n} (φ ψ : Formula (limit L) n)
    (ts : Fin n → CoordinateTerm (limit L)) :
    CoordinateTerm.Eval C.point (φ.and ψ) ts ↔
      CoordinateTerm.Eval C.point φ ts ∧ CoordinateTerm.Eval C.point ψ ts := by
  rw [C.eval_iff_contains, C.eval_iff_contains, C.eval_iff_contains]
  simp only [CoordinateTerm.instantiate, Formula.subst_and, C.and_iff]

theorem eval_or_iff {n} {φ ψ : Formula (limit L) n}
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (hψ : ⟨n, ψ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (ts : Fin n → CoordinateTerm (limit L)) :
    CoordinateTerm.Eval C.point (φ.or ψ) ts ↔
      CoordinateTerm.Eval C.point φ ts ∨ CoordinateTerm.Eval C.point ψ ts := by
  classical
  rw [Formula.or, C.eval_neg_iff (and_closed (neg_closed hφ) (neg_closed hψ)),
    C.eval_and_iff, C.eval_neg_iff hφ, C.eval_neg_iff hψ]
  tauto

theorem eval_all_iff {n} {φ : Formula (limit L) (n + 1)}
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (ts : Fin n → CoordinateTerm (limit L)) :
    CoordinateTerm.Eval C.point (Formula.all φ) ts ↔
      ∀ t : CoordinateTerm (limit L), CoordinateTerm.Eval C.point φ (t :> ts) := by
  classical
  rw [Formula.all, C.eval_neg_iff (exs_closed (neg_closed hφ)),
    C.eval_existential_iff (exs_closed (neg_closed hφ))]
  simp only [not_exists, C.eval_neg_iff hφ, not_not]

theorem eval_expanded_iff {n} (φ : Semisentence (limit L) n)
    (ts : Fin n → CoordinateTerm (limit L)) :
    CoordinateTerm.Eval C.point (Formula.expandFirstOrder φ) ts ↔
      CoordinateTerm.Eval C.point (.fo φ) ts := by
  simp only [CoordinateTerm.Eval, CoordinateTerm.EvalAt, Formula.weakEval_expandFirstOrder,
    Formula.weakEval_fo]

/-- Expanded first-order truth in the coordinate-term quotient structure. -/
theorem expanded_firstOrder_truth {n} (φ : Semisentence (limit L) n)
    (ts : Fin n → CoordinateTerm (limit L)) :
    φ.Evalb (s := C.extensionStructure) (fun i ↦ C.termClass (ts i)) ↔
      CoordinateTerm.Eval C.point (Formula.expandFirstOrder φ) ts := by
  induction φ with
  | verum => exact iff_of_true trivial (C.eval_verum ts)
  | falsum =>
    change False ↔ CoordinateTerm.Eval C.point (.neg (.fo .verum)) ts
    rw [C.eval_neg_iff (fo_in_fragment _)]
    exact iff_of_false id (fun h ↦ h (C.eval_verum ts))
  | rel r us =>
    change Structure.rel (self := C.extensionStructure) r
      (fun i ↦ (us i).val (fun j ↦ C.termClass (ts j)) Empty.elim) ↔
        CoordinateTerm.Eval C.point (.fo (.rel r us)) ts
    rw [funext (fun i ↦ C.term_val (us i) ts), C.rel_termClass]
    exact (C.eval_subst_iff (atom r) us ts).symm
  | nrel r us =>
    change (¬Structure.rel (self := C.extensionStructure) r
      (fun i ↦ (us i).val (fun j ↦ C.termClass (ts j)) Empty.elim)) ↔
        CoordinateTerm.Eval C.point (.neg (.fo (.rel r us))) ts
    rw [C.eval_neg_iff (fo_in_fragment _), funext (fun i ↦ C.term_val (us i) ts), C.rel_termClass]
    exact not_congr (C.eval_subst_iff (atom r) us ts).symm
  | and φ ψ ihφ ihψ =>
    change (_ ∧ _) ↔ CoordinateTerm.Eval C.point
      ((Formula.expandFirstOrder φ).and (Formula.expandFirstOrder ψ)) ts
    rw [C.eval_and_iff]
    exact and_congr (ihφ ts) (ihψ ts)
  | or φ ψ ihφ ihψ =>
    change (_ ∨ _) ↔ CoordinateTerm.Eval C.point
      ((Formula.expandFirstOrder φ).or (Formula.expandFirstOrder ψ)) ts
    rw [C.eval_or_iff (expanded_in_fragment _) (expanded_in_fragment _)]
    exact or_congr (ihφ ts) (ihψ ts)
  | all φ ih =>
    change (∀ x : C.ExtensionDomain,
      φ.Evalb (x :> (fun i ↦ C.termClass (ts i)))) ↔
        CoordinateTerm.Eval C.point (Formula.all (Formula.expandFirstOrder φ)) ts
    rw [C.forall_termClass, C.eval_all_iff (expanded_in_fragment _)]
    apply forall_congr'
    intro t
    simpa only [C.termClass_cons] using ih (t :> ts)
  | exs φ ih =>
    change (∃ x : C.ExtensionDomain,
      φ.Evalb (x :> (fun i ↦ C.termClass (ts i)))) ↔
        CoordinateTerm.Eval C.point (.exs (Formula.expandFirstOrder φ)) ts
    rw [C.exists_termClass, C.eval_existential_iff (exs_closed (expanded_in_fragment _))]
    apply exists_congr
    intro t
    simpa only [C.termClass_cons] using ih (t :> ts)

/-- First-order evaluation agrees with the generic finite-condition semantics. -/
theorem firstOrder_truth {n} (φ : Semisentence (limit L) n)
    (ts : Fin n → CoordinateTerm (limit L)) :
    φ.Evalb (s := C.extensionStructure) (fun i ↦ C.termClass (ts i)) ↔
      CoordinateTerm.Eval C.point (.fo φ) ts :=
  (C.expanded_firstOrder_truth φ ts).trans (C.eval_expanded_iff φ ts)

end HenkinConstruction.FragmentExtension.GenericConditionChain
end ZFVP.Infinitary
