import ZFVP.ModelTheory.InfinitaryGenericFiberInclusion

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension.GenericConditionChain
open HenkinLanguage FragmentClosure FiniteCondition
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}
  {p₀ : H.FiniteCondition} (C : GenericConditionChain H p₀)

/-- The upward closure of positively labelled definable fibers, on actual subsets
of the quotient. This definition precedes the quotient truth theorem. -/
def extensionQuantifier (A : Set C.ExtensionDomain) : Prop :=
  ∃ n, ∃ φ : Formula (limit L) (n + 1),
    ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S) ∧
    ∃ ts : Fin n → CoordinateTerm (limit L),
      CoordinateTerm.Eval C.point (.q φ) ts ∧ C.genericFiber φ ts ⊆ A

theorem extensionQuantifier_mono : Monotone C.extensionQuantifier := by
  intro A B hAB
  rintro ⟨n, φ, hφ, ts, hq, hs⟩
  exact ⟨n, φ, hφ, ts, hq, hs.trans hAB⟩

theorem extensionQuantifier_fiber {n} {φ : Formula (limit L) (n + 1)}
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (ts : Fin n → CoordinateTerm (limit L)) :
    C.extensionQuantifier (C.genericFiber φ ts) ↔ CoordinateTerm.Eval C.point (.q φ) ts := by
  constructor
  · rintro ⟨m, ψ, hψ, us, hq, hsub⟩
    exact C.q_label_of_fiber_subset hψ hφ hsub hq
  · intro hq
    exact ⟨n, φ, hφ, ts, hq, Set.Subset.refl _⟩

/-- Full fragment truth in the actual quotient, including every finite tuple of
new parameters and every Q occurrence. -/
theorem extension_truth {n} (φ : Formula (limit L) n)
    (hφ : ⟨n, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (ts : Fin n → CoordinateTerm (limit L)) :
    Formula.WeakEval C.extensionQuantifier φ (fun i ↦ C.termClass (ts i)) ↔
      CoordinateTerm.Eval C.point φ ts := by
  induction φ with
  | fo φ => exact C.firstOrder_truth φ ts
  | neg φ ih =>
    rw [Formula.weakEval_neg, C.eval_neg_iff
      (subformulas_closed hφ (Or.inr (Formula.self_mem_subformulas φ)))]
    exact not_congr (ih (subformulas_closed hφ (Or.inr (Formula.self_mem_subformulas φ))) ts)
  | conj f ih =>
    rw [Formula.weakEval_conj, C.eval_conjunction_iff hφ]
    exact forall_congr' (fun i ↦ ih i (sequence_member_closed hφ i) ts)
  | exs φ ih =>
    have hf := subformulas_closed hφ (Or.inr (Formula.self_mem_subformulas φ))
    rw [Formula.weakEval_exs, C.exists_termClass, C.eval_existential_iff hφ]
    apply exists_congr
    intro t
    simpa only [C.termClass_cons, Set.mem_setOf_eq] using ih hf (t :> ts)
  | q φ ih =>
    have hf := subformulas_closed hφ (Or.inr (Formula.self_mem_subformulas φ))
    change C.extensionQuantifier {x | Formula.WeakEval C.extensionQuantifier φ
      (x :> (fun i ↦ C.termClass (ts i)))} ↔ _
    have he : {x | Formula.WeakEval C.extensionQuantifier φ
        (x :> (fun i ↦ C.termClass (ts i)))} = C.genericFiber φ ts := by
      ext x
      obtain ⟨t, rfl⟩ := C.termClass_surjective x
      rw [C.termClass_mem_genericFiber]
      simpa only [C.termClass_cons, Set.mem_setOf_eq] using ih hf (t :> ts)
    rw [he, C.extensionQuantifier_fiber hf]

end HenkinConstruction.FragmentExtension.GenericConditionChain
end ZFVP.Infinitary

