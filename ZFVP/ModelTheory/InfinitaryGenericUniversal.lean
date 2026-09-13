import ZFVP.ModelTheory.InfinitaryGenericFirstOrderTruth

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension.GenericConditionChain
open HenkinLanguage FragmentClosure FiniteCondition
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}
  {p₀ : H.FiniteCondition} (C : GenericConditionChain H p₀)

theorem eval_all_terms_iff {n} {φ : Formula (limit L) (n + 1)}
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (ts : Fin n → CoordinateTerm (limit L)) :
    CoordinateTerm.Eval C.point φ.all ts ↔
      ∀ t, CoordinateTerm.Eval C.point φ (t :> ts) := by
  classical
  change CoordinateTerm.Eval C.point (.neg (.exs (.neg φ))) ts ↔ _
  rw [C.eval_neg_iff (exs_closed (neg_closed hφ)),
    C.eval_existential_iff (exs_closed (neg_closed hφ))]
  simp only [not_exists, C.eval_neg_iff hφ, not_not]

theorem eval_and_terms_iff {n} (φ ψ : Formula (limit L) n)
    (ts : Fin n → CoordinateTerm (limit L)) :
    CoordinateTerm.Eval C.point (φ.and ψ) ts ↔
      CoordinateTerm.Eval C.point φ ts ∧ CoordinateTerm.Eval C.point ψ ts := by
  rw [C.eval_iff_contains, C.eval_iff_contains, C.eval_iff_contains]
  simpa only [CoordinateTerm.instantiate, Formula.subst_and] using
    (C.and_iff (φ := CoordinateTerm.instantiate φ ts) (ψ := CoordinateTerm.instantiate ψ ts))

theorem eval_imp_iff {n} {φ ψ : Formula (limit L) n}
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (hψ : ⟨n, ψ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (ts : Fin n → CoordinateTerm (limit L)) :
    CoordinateTerm.Eval C.point (φ.imp ψ) ts ↔
      (CoordinateTerm.Eval C.point φ ts → CoordinateTerm.Eval C.point ψ ts) := by
  classical
  change CoordinateTerm.Eval C.point (.neg ((Formula.neg (.neg φ)).and (.neg ψ))) ts ↔ _
  rw [C.eval_neg_iff (and_closed (neg_closed (neg_closed hφ)) (neg_closed hψ)),
    C.eval_and_terms_iff, C.eval_neg_iff (neg_closed hφ), C.eval_neg_iff hφ, C.eval_neg_iff hψ]
  tauto

theorem eval_q_monotone {n} {φ ψ : Formula (limit L) (n + 1)}
    {ts : Fin n → CoordinateTerm (limit L)}
    (himp : CoordinateTerm.Eval C.point (φ.imp ψ).all ts)
    (hq : CoordinateTerm.Eval C.point (.q φ) ts) : CoordinateTerm.Eval C.point (.q ψ) ts := by
  obtain ⟨i, hi⟩ := himp
  obtain ⟨j, hj⟩ := hq
  obtain ⟨hs, hh⟩ := CoordinateTerm.evalAt_persistent (C.refines (Nat.le_max_left i j)) hi
  obtain ⟨ht, hq⟩ := CoordinateTerm.evalAt_persistent (C.refines (Nat.le_max_right i j)) hj
  refine ⟨max i j, hs, ?_⟩
  intro b hb
  apply H.weakQuantifier_mono ?_ (hq b hb)
  intro x hx
  exact ((Formula.weakEval_imp _ _ _ _).mp
    ((Formula.weakEval_all _ _ _).mp (hh b hb) x)) hx

end HenkinConstruction.FragmentExtension.GenericConditionChain
end ZFVP.Infinitary


