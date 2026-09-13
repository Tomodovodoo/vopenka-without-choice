import ZFVP.ModelTheory.InfinitaryHenkinQuantifier

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension
open HenkinLanguage KeislerDerivation FragmentClosure
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))} (H : FragmentExtension Γ (FragmentClosure.carrier S))

/-- The full fragment truth lemma for the countable quotient and its extensional
weak quantifier. It does not identify the weak quantifier with uncountability. -/
theorem weak_truth {n} (φ : Formula (limit L) n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier S) (v : Fin n → Semiterm (limit L) Empty 0) :
    Formula.WeakEval H.weakQuantifier φ (fun i ↦ H.classOf (v i)) ↔
      φ.subst v ∈ H.carrier := by
  induction φ with
  | fo φ => exact H.firstOrder_truth φ v
  | neg φ ih =>
    have hc := subformulas_closed hφ (Or.inr (Formula.self_mem_subformulas φ))
    change (¬Formula.WeakEval H.weakQuantifier φ _) ↔ Formula.neg (φ.subst v) ∈ H.carrier
    rw [H.neg_mem_iff (subst_closed hc v)]
    exact not_congr (ih hc v)
  | conj f ih =>
    have hc (i : ℕ) : ⟨_, f i⟩ ∈ FragmentClosure.carrier S :=
      subformulas_closed hφ (Or.inr (Set.mem_iUnion.mpr ⟨i, Formula.self_mem_subformulas (f i)⟩))
    change (∀ i, Formula.WeakEval H.weakQuantifier (f i) _) ↔
      Formula.conj (fun i ↦ (f i).subst v) ∈ H.carrier
    rw [H.conj_mem_iff _ (subst_closed hφ v) (fun i ↦ subst_closed (hc i) v)]
    exact forall_congr' fun i ↦ ih i (hc i) v
  | exs φ ih =>
    have hc := subformulas_closed hφ (Or.inr (Formula.self_mem_subformulas φ))
    change (∃ x : H.Domain, Formula.WeakEval H.weakQuantifier φ
        (x :> (fun i ↦ H.classOf (v i)))) ↔
      Formula.exs (φ.subst (liftSubstitution v)) ∈ H.carrier
    rw [H.exists_classOf, H.exs_mem_iff _ (subst_closed hφ v)]
    apply exists_congr
    intro t
    rw [Formula.substFirst_lift]
    simpa only [H.classOf_cons] using ih hc (Fin.cases t v)
  | q φ ih =>
    have hc := subformulas_closed hφ (Or.inr (Formula.self_mem_subformulas φ))
    have hθ := subst_closed hc (liftSubstitution v)
    have he : {x : H.Domain | Formula.WeakEval H.weakQuantifier φ
        (x :> (fun i ↦ H.classOf (v i)))} = H.fiber (φ.subst (liftSubstitution v)) := by
      ext x
      change Formula.WeakEval H.weakQuantifier φ (x :> (fun i ↦ H.classOf (v i))) ↔
        (φ.subst (liftSubstitution v)).substFirst x.out ∈ H.carrier
      rw [Formula.substFirst_lift]
      have hx : H.classOf x.out = x := Quotient.out_eq x
      simpa only [H.classOf_cons, hx] using ih hc (Fin.cases x.out v)
    change H.weakQuantifier _ ↔ Formula.q (φ.subst (liftSubstitution v)) ∈ H.carrier
    rw [he, H.weakQuantifier_fiber hθ]

theorem weak_sentence_truth (φ : Sentence (limit L))
    (hφ : ⟨0, φ⟩ ∈ FragmentClosure.carrier S) :
    Formula.WeakEval H.weakQuantifier φ Fin.elim0 ↔ φ ∈ H.carrier := by
  have he := H.weak_truth φ hφ (Fin.elim0 : Fin 0 → Semiterm (limit L) Empty 0)
  have hs : φ.subst (Fin.elim0 : Fin 0 → Semiterm (limit L) Empty 0) = φ := by
    rw [← Formula.rewrite_subst]
    have hr : Rew.subst (Fin.elim0 : Fin 0 → Semiterm (limit L) Empty 0) = Rew.id := by
      apply Rew.ext
      · intro i; exact i.elim0
      · intro i; exact i.elim
    rw [hr, Formula.rewrite_id]
  have hb : (fun i : Fin 0 ↦ H.classOf i.elim0) = (Fin.elim0 : Fin 0 → H.Domain) :=
    Subsingleton.elim _ _
  simpa only [hs, hb] using he

end HenkinConstruction.FragmentExtension
end ZFVP.Infinitary


