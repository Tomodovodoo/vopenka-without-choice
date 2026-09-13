import ZFVP.SetTheory.ClassFormulaForcing
import ZFVP.SetTheory.AtomicForcingAction
import ZFVP.SetTheory.ForcingConditionAction

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingTermValue_nameAction {n : ℕ} (t : Semiterm ℒₛₑₜ Empty n)
    (π : V) (v : Fin n → V) :
    forcingTermValue t (standardTuple (fun i ↦ nameAction π (v i))) =
      nameAction π (forcingTermValue t (standardTuple v)) := by
  cases t with
  | bvar i => simp only [forcingTermValue, value_standardTuple]
  | fvar x => exact Empty.elim x
  | func f _ => exact Empty.elim f

theorem forcingTermValue_isName {P : V} {n : ℕ} (t : Semiterm ℒₛₑₜ Empty n)
    (v : Fin n → V) (hv : ∀ i, IsForcingName P (v i)) :
    IsForcingName P (forcingTermValue t (standardTuple v)) := by
  cases t with
  | bvar i => simpa only [forcingTermValue, value_standardTuple] using hv i
  | fvar x => exact Empty.elim x
  | func f _ => exact Empty.elim f

theorem forcingAtomic_nameAction_iff {P R π p : V} (hπ : IsForcingAutomorphism P R π)
    {n k : ℕ} (r : Language.Set.Rel k) (ts : Fin k → Semiterm ℒₛₑₜ Empty n)
    (v : Fin n → V) (hv : ∀ i, IsForcingName P (v i)) (hp : p ∈ P) :
    π ‘ p ∈ forcingAtomic P R r ts (standardTuple (fun i ↦ nameAction π (v i))) ↔
      p ∈ forcingAtomic P R r ts (standardTuple v) := by
  cases r <;> simp only [forcingAtomic, forcingTermValue_nameAction]
  · exact atomicEquality_nameAction_iff hπ (forcingTermValue_isName _ v hv) (forcingTermValue_isName _ v hv) hp
  · exact atomicMembership_nameAction_iff hπ (forcingTermValue_isName _ v hv) (forcingTermValue_isName _ v hv) hp

theorem classForcingFormula_nameAction_iff {P R π : V} (hR : IsForcingPreorder P R)
    (hπ : IsForcingAutomorphism P R π) (N : V → Prop) (hN : ℒₛₑₜ-predicate N)
    (hnames : ∀ x, N x → IsForcingName P x)
    (hclosed : ∀ x, N x → N (nameAction π x))
    (hsurj : ∀ y, N y → ∃ x, N x ∧ nameAction π x = y)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → V) (hv : ∀ i, N (v i))
    {p : V} (hp : p ∈ P) :
    π ‘ p ∈ classForcingFormula P R N hN φ (standardTuple (fun i ↦ nameAction π (v i))) ↔
      p ∈ classForcingFormula P R N hN φ (standardTuple v) := by
  induction φ generalizing p with
  | verum => exact iff_of_true (function_value_mem hπ.1 hp) hp
  | falsum => simp only [classForcingFormula_falsum, not_mem_empty]
  | rel r ts => exact forcingAtomic_nameAction_iff hπ r ts v (fun i ↦ hnames _ (hv i)) hp
  | nrel r ts =>
    rw [classForcingFormula_nrel, classForcingFormula_nrel]
    exact forcingNegation_action_iff hπ
      (fun q hq ↦ forcingAtomic_nameAction_iff hπ r ts v (fun i ↦ hnames _ (hv i)) hq) hp
  | and φ ψ ihφ ihψ =>
    rw [classForcingFormula_and, classForcingFormula_and, mem_inter_iff, mem_inter_iff]
    exact and_congr (ihφ v hv hp) (ihψ v hv hp)
  | or φ ψ ihφ ihψ =>
    rw [classForcingFormula_or, classForcingFormula_or]
    apply forcingClosure_action_iff hπ
    · intro q hq
      rcases mem_union_iff.mp hq with hh | hh
      · exact (classForcingFormula_regular N hN hR φ _).1 q hh
      · exact (classForcingFormula_regular N hN hR ψ _).1 q hh
    · intro q hq
      rcases mem_union_iff.mp hq with hh | hh
      · exact (classForcingFormula_regular N hN hR φ _).1 q hh
      · exact (classForcingFormula_regular N hN hR ψ _).1 q hh
    · intro q hq
      rw [mem_union_iff, mem_union_iff]
      exact or_congr (ihφ v hv hq) (ihψ v hv hq)
    · exact hp
  | @all n φ ih =>
    rw [classForcingFormula_all, classForcingFormula_all]
    apply forcingClassIntersection_action_iff hπ N hN (nameAction π) hclosed hsurj
    · intro x hx q hq
      exact ih (x :> v) (fun i ↦ Fin.cases hx (fun j ↦ hv j) i) hq
    · exact hp
  | @exs n φ ih =>
    rw [classForcingFormula_exs, classForcingFormula_exs]
    unfold forcingExistential
    apply forcingClosure_action_iff hπ (forcingClassUnion_subset _ _ _ _ _) (forcingClassUnion_subset _ _ _ _ _)
    · intro q hq
      apply forcingClassUnion_action_iff hπ N hN (nameAction π) hclosed hsurj
      · intro x hx r hr
        exact ih (x :> v) (fun i ↦ Fin.cases hx (fun j ↦ hv j) i) hr
      · exact hq
    · exact hp

end ZFVP
