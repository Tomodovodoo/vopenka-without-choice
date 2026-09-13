import ZFVP.SetTheory.EquivalentRetractionAtoms
import ZFVP.SetTheory.RetractionForcingOperations
import ZFVP.SetTheory.ClassFormulaForcingAction
import ZFVP.SetTheory.FormulaForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingRetraction.forcingAtomic_nameAction_iff {P R N T m p : V}
    (hr : IsForcingRetraction N T P R m) (hR : IsForcingPreorder P R)
    (he : ∀ q ∈ P, ⟨m ‘ q, q⟩ₖ ∈ R ∧ ⟨q, m ‘ q⟩ₖ ∈ R)
    {n k : ℕ} (r : Language.Set.Rel k) (ts : Fin k → Semiterm ℒₛₑₜ Empty n)
    (v : Fin n → V) (hv : ∀ i, IsForcingName P (v i)) (hp : p ∈ P) :
    p ∈ forcingAtomic P R r ts (standardTuple v) ↔
      m ‘ p ∈ forcingAtomic N T r ts (standardTuple (fun i ↦ nameAction m (v i))) := by
  cases r <;> simp only [forcingAtomic, forcingTermValue_nameAction]
  · exact hr.atomicEquality_nameAction_iff hR he (forcingTermValue_isName _ v hv) (forcingTermValue_isName _ v hv) hp
  · exact hr.atomicMembership_nameAction_iff hR he (forcingTermValue_isName _ v hv) (forcingTermValue_isName _ v hv) hp

/-- Full formula forcing commutes with the specified name action of an
equivalent retraction. This proof applies to arbitrary internal ZF grounds. -/
theorem IsForcingRetraction.forcingFormula_nameAction_iff {P R N T m : V}
    (hr : IsForcingRetraction N T P R m) (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ q ∈ P, ⟨m ‘ q, q⟩ₖ ∈ R ∧ ⟨q, m ‘ q⟩ₖ ∈ R)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → V) (hv : ∀ i, IsForcingName P (v i))
    {p : V} (hp : p ∈ P) :
    p ∈ forcingFormula P R φ (standardTuple v) ↔
      m ‘ p ∈ forcingFormula N T φ (standardTuple (fun i ↦ nameAction m (v i))) := by
  have hclosed (x : V) (hx : IsForcingName P x) := nameAction_isName hr.maps hx
  have hsurj (y : V) (hy : IsForcingName N y) : ∃ x, IsForcingName P x ∧ nameAction m x = y :=
    ⟨y, hy.mono hr.inclusion, nameAction_eq_self_of_fixes_conditions hr.fixes hy⟩
  induction φ generalizing p with
  | verum => exact iff_of_true hp (function_value_mem hr.maps hp)
  | falsum => simp only [forcingFormula_falsum, not_mem_empty]
  | rel r ts => exact hr.forcingAtomic_nameAction_iff hR he r ts v hv hp
  | nrel r ts =>
    rw [forcingFormula_nrel, forcingFormula_nrel]
    exact hr.forcingNegation_iff (fun q hq ↦ hr.forcingAtomic_nameAction_iff hR he r ts v hv hq) hp
  | and φ ψ ihφ ihψ =>
    rw [forcingFormula_and, forcingFormula_and, mem_inter_iff, mem_inter_iff]
    exact and_congr (ihφ v hv hp) (ihψ v hv hp)
  | or φ ψ ihφ ihψ =>
    rw [forcingFormula_or, forcingFormula_or]
    apply hr.forcingClosure_iff
    · intro q hq
      rcases mem_union_iff.mp hq with hq | hq
      · exact (forcingFormula_regular hR φ _).1 q hq
      · exact (forcingFormula_regular hR ψ _).1 q hq
    · intro q hq
      rcases mem_union_iff.mp hq with hq | hq
      · exact (forcingFormula_regular hT φ _).1 q hq
      · exact (forcingFormula_regular hT ψ _).1 q hq
    · intro q hq
      rw [mem_union_iff, mem_union_iff]
      exact or_congr (ihφ v hv hq) (ihψ v hv hq)
    · exact hp
  | @all n φ ih =>
    rw [forcingFormula_all, forcingFormula_all]
    apply hr.forcingClassIntersection_iff (IsForcingName P) (IsForcingName N)
      (by definability) (by definability) (nameAction m) hclosed hsurj
    · intro x hx q hq
      exact ih (x :> v) (fun i ↦ Fin.cases hx (fun j ↦ hv j) i) hq
    · exact hp
  | @exs n φ ih =>
    rw [forcingFormula_exs, forcingFormula_exs]
    unfold forcingExistential
    apply hr.forcingClosure_iff (forcingClassUnion_subset _ _ _ _ _) (forcingClassUnion_subset _ _ _ _ _)
    · intro q hq
      apply hr.forcingClassUnion_iff (IsForcingName P) (IsForcingName N)
        (by definability) (by definability) (nameAction m) hclosed hsurj
      · intro x hx r hrP
        exact ih (x :> v) (fun i ↦ Fin.cases hx (fun j ↦ hv j) i) hrP
      · exact hq
    · exact hp

theorem IsForcingRetraction.forcingFormula_check_iff {P R N T m one : V}
    (hr : IsForcingRetraction N T P R m) (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (he : ∀ q ∈ P, ⟨m ‘ q, q⟩ₖ ∈ R ∧ ⟨q, m ‘ q⟩ₖ ∈ R) (hone : one ∈ N)
    {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → V) {p : V} (hp : p ∈ P) :
    p ∈ forcingFormula P R φ (standardTuple (fun i ↦ checkName one (v i))) ↔
      m ‘ p ∈ forcingFormula N T φ (standardTuple (fun i ↦ checkName one (v i))) := by
  have hh := hr.forcingFormula_nameAction_iff hR hT he φ (fun i ↦ checkName one (v i))
    (fun i ↦ checkName_isName (hr.inclusion one hone) (v i)) hp
  simpa only [nameAction_checkName (hr.inclusion one hone) (hr.fixes one hone)] using hh

end ZFVP
