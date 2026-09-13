import ZFVP.ModelTheory.InfinitaryClosedFragmentTruth

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension
open HenkinLanguage KeislerDerivation FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))} (H : FragmentExtension Γ (FragmentClosure.carrier S))

theorem classOf_surjective : Function.Surjective H.classOf := Quotient.mk_surjective

theorem forall_classOf (P : H.Domain → Prop) : (∀ x, P x) ↔ ∀ t, P (H.classOf t) :=
  H.classOf_surjective.forall

theorem exists_classOf (P : H.Domain → Prop) : (∃ x, P x) ↔ ∃ t, P (H.classOf t) :=
  H.classOf_surjective.exists

theorem classOf_cons {n} (t : Semiterm (limit L) Empty 0)
    (v : Fin n → Semiterm (limit L) Empty 0) :
    (fun i ↦ H.classOf (Fin.cases t v i)) = H.classOf t :> (fun i ↦ H.classOf (v i)) := by
  funext i
  cases i using Fin.cases <;> rfl

/-- Expanded first-order truth in the actual quotient structure. -/
theorem expanded_firstOrder_truth {n} (φ : Semisentence (limit L) n)
    (v : Fin n → Semiterm (limit L) Empty 0) :
    Semiformula.Eval (s := H.termStructure) (fun i ↦ H.classOf (v i)) Empty.elim φ ↔
      (Formula.expandFirstOrder φ).subst v ∈ H.carrier := by
  induction φ with
  | verum =>
    change True ↔ Formula.fo (.verum : Semisentence (limit L) 0) ∈ H.carrier
    exact iff_of_true trivial (H.of_theorem (fo_in_fragment _) .truth)
  | falsum =>
    change False ↔ Formula.neg (.fo (.verum : Semisentence (limit L) 0)) ∈ H.carrier
    rw [H.neg_mem_iff (fo_in_fragment _)]
    exact iff_of_false id (not_not.mpr (H.of_theorem (fo_in_fragment _) .truth))
  | rel r ts =>
    change Structure.rel r (fun i ↦ Semiterm.val (s := H.termStructure) (fun j ↦ H.classOf (v j)) Empty.elim (ts i)) ↔
      Formula.fo (.rel r (fun i ↦ (Rew.subst v) (ts i))) ∈ H.carrier
    rw [funext (fun i ↦ H.term_val (ts i) v)]
    exact H.rel_classOf r _
  | nrel r ts =>
    change (¬Structure.rel r (fun i ↦ Semiterm.val (s := H.termStructure) (fun j ↦ H.classOf (v j)) Empty.elim (ts i))) ↔
      Formula.neg (.fo (.rel r (fun i ↦ (Rew.subst v) (ts i)))) ∈ H.carrier
    rw [H.neg_mem_iff (fo_in_fragment _), funext (fun i ↦ H.term_val (ts i) v)]
    exact not_congr (H.rel_classOf r _)
  | and φ ψ ihφ ihψ =>
    change (_ ∧ _) ↔ ((Formula.expandFirstOrder φ).and (Formula.expandFirstOrder ψ)).subst v ∈ H.carrier
    rw [Formula.subst_and, H.and_mem_iff (subst_closed (expanded_in_fragment _) _)
      (subst_closed (expanded_in_fragment _) _)]
    exact and_congr (ihφ v) (ihψ v)
  | or φ ψ ihφ ihψ =>
    change (_ ∨ _) ↔ ((Formula.expandFirstOrder φ).or (Formula.expandFirstOrder ψ)).subst v ∈ H.carrier
    rw [Formula.subst_or, H.or_mem_iff (subst_closed (expanded_in_fragment _) _)
      (subst_closed (expanded_in_fragment _) _)]
    exact or_congr (ihφ v) (ihψ v)
  | all φ ih =>
    change (∀ x : H.Domain, Semiformula.Eval (x :> (fun i ↦ H.classOf (v i))) Empty.elim φ) ↔
      (Formula.all (Formula.expandFirstOrder φ)).subst v ∈ H.carrier
    rw [H.forall_classOf, Formula.subst_all,
      H.all_mem_iff (subst_closed (expanded_in_fragment _) _)]
    apply forall_congr'
    intro t
    rw [Formula.substFirst_lift]
    simpa only [H.classOf_cons] using ih (Fin.cases t v)
  | exs φ ih =>
    change (∃ x : H.Domain, Semiformula.Eval (x :> (fun i ↦ H.classOf (v i))) Empty.elim φ) ↔
      Formula.exs ((Formula.expandFirstOrder φ).subst (liftSubstitution v)) ∈ H.carrier
    rw [H.exists_classOf, H.exs_mem_iff _ (exs_closed (subst_closed (expanded_in_fragment _) _))]
    apply exists_congr
    intro t
    rw [Formula.substFirst_lift]
    simpa only [H.classOf_cons] using ih (Fin.cases t v)

theorem firstOrder_truth {n} (φ : Semisentence (limit L) n)
    (v : Fin n → Semiterm (limit L) Empty 0) :
    Semiformula.Eval (s := H.termStructure) (fun i ↦ H.classOf (v i)) Empty.elim φ ↔
      (Formula.fo φ).subst v ∈ H.carrier := by
  rw [H.expanded_firstOrder_truth, Formula.expandFirstOrder_subst]
  exact (H.expansion_mem_iff (φ ⇜ v)).symm

end HenkinConstruction.FragmentExtension
end ZFVP.Infinitary

