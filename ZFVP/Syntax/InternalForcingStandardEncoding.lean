import ZFVP.Syntax.InternalForcingRegular
import ZFVP.Syntax.StandardCodeExpressions
import ZFVP.SetTheory.ClassFormulaForcing

/-! Internal formula-code forcing agrees with the externally finite formula
recursion on standard tuple assignments. No forcing-order hypothesis is needed. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingTermValue_index {n : ℕ} (t : SetTheorySemiterm Empty n) (b : V) :
    forcingTermValue t b = b ‘ ((membershipTermIndex t).val : V) := by
  cases t with
  | bvar i => rfl
  | fvar e => exact Empty.elim e
  | func f _ => exact Empty.elim f

theorem standardMembershipAtomicArguments {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → SetTheorySemiterm Empty n) :
    IsAtomicArguments (membershipLanguageCode : V) ∅ (n : V)
      (relationToken (membershipSymbol r))
      (standardTuple (fun i ↦ encodeSemiterm
        (fun {k} ↦ membershipFunctionSymbol (V := V) (k := k)) Empty.elim (ts i))) := by
  rw [← eval_membershipArgumentExpression r ts]
  apply (membershipAtomicArguments_iff (by simp)).mpr
  cases r <;>
    simp only [membershipArgumentExpression, CodeExpression.eval_boundArgs, CodeExpression.eval]
  · exact ⟨Or.inr (Or.inl rfl), _, natCast_mem_of_lt (membershipTermIndex (ts 0)).isLt,
      _, natCast_mem_of_lt (membershipTermIndex (ts 1)).isLt, rfl⟩
  · exact ⟨Or.inr (Or.inr rfl), _, natCast_mem_of_lt (membershipTermIndex (ts 0)).isLt,
      _, natCast_mem_of_lt (membershipTermIndex (ts 1)).isLt, rfl⟩

theorem internalAtomicForcingSet_standard {n k : ℕ} (P R b : V)
    (r : Language.Set.Rel k) (ts : Fin k → SetTheorySemiterm Empty n) :
    internalAtomicForcingSet P R (n : V) b (relationToken (membershipSymbol r))
      (standardTuple (fun i ↦ encodeSemiterm
        (fun {k} ↦ membershipFunctionSymbol (V := V) (k := k)) Empty.elim (ts i))) =
      forcingAtomic P R r ts b := by
  rw [← eval_membershipArgumentExpression r ts]
  cases r <;>
    simp only [membershipArgumentExpression, CodeExpression.eval_boundArgs, CodeExpression.eval,
      forcingAtomic, forcingTermValue_index]
  all_goals
    have hi : ((membershipTermIndex (ts 0)).val : V) ∈ (n : V) := by
      exact natCast_mem_of_lt (membershipTermIndex (ts 0)).isLt
    have hj : ((membershipTermIndex (ts 1)).val : V) ∈ (n : V) := by
      exact natCast_mem_of_lt (membershipTermIndex (ts 1)).isLt
    apply mem_ext
    intro p
    simp only [mem_internalAtomicForcingSet, internalForcingAtomic_boundPair hi hj]
  · simp [membershipSymbol, equalityToken, relationToken]
    exact atomicEquality_subset P R _ _ p
  · have hz : (⟨(1 : V), (1 : V)⟩ₖ : V) ≠ ∅ := by
      intro h
      have hm : ({(1 : V)} : V) ∈ ⟨(1 : V), (1 : V)⟩ₖ := by simp [kpair]
      rw [h] at hm
      exact not_mem_empty hm
    simp [membershipSymbol, equalityToken, relationToken, hz]
    exact atomicMembership_subset P R _ _ p

theorem internalForcingSet_standardEncoding (P R D : V) {n : ℕ}
    (φ : SetTheorySemisentence n) (v : Fin n → V) (hv : ∀ i, v i ∈ D) :
    internalForcingSet P R D (n : V) (encodeMembershipFormula φ) (standardTuple v) =
      classForcingFormula P R (fun x ↦ x ∈ D) (by definability) φ (standardTuple v) := by
  have hc : ∀ {m : ℕ} (ψ : SetTheorySemisentence m),
      IsMembershipFormulaCode (m : V) (encodeMembershipFormula ψ) :=
    fun ψ ↦ (mem_formulaSet_iff _ _ _ _).mp (encodeMembershipFormula_mem ψ)
  induction φ with
  | verum => exact internalForcingSet_truth (by simp) (standardTuple_mem_function v hv)
  | falsum => exact internalForcingSet_falsity (by simp)
  | rel r ts =>
    change internalForcingSet P R D _ (atomCode _ _) _ = _
    rw [internalForcingSet_atom (by simp) (standardMembershipAtomicArguments r ts)
      (standardTuple_mem_function v hv), internalAtomicForcingSet_standard]
    rfl
  | nrel r ts =>
    change internalForcingSet P R D _ (negAtomCode _ _) _ = _
    rw [internalForcingSet_negAtom (by simp) (standardMembershipAtomicArguments r ts)
      (standardTuple_mem_function v hv), internalAtomicForcingSet_standard]
    rfl
  | and φ ψ ihφ ihψ =>
    change internalForcingSet P R D _ (andCode (encodeMembershipFormula φ) (encodeMembershipFormula ψ)) _ = _
    rw [internalForcingSet_and (hc φ) (hc ψ) (standardTuple_mem_function v hv),
      ihφ v hv, ihψ v hv]
    rfl
  | or φ ψ ihφ ihψ =>
    change internalForcingSet P R D _ (orCode (encodeMembershipFormula φ) (encodeMembershipFormula ψ)) _ = _
    rw [internalForcingSet_or (hc φ) (hc ψ) (standardTuple_mem_function v hv),
      ihφ v hv, ihψ v hv]
    rfl
  | @all m φ ih =>
    change internalForcingSet P R D _ (allCode (encodeMembershipFormula φ)) _ = _
    rw [internalForcingSet_all (by simp) (by simpa only [num_succ_def] using hc φ)
      (standardTuple_mem_function v hv), classForcingFormula_all]
    apply mem_ext
    intro p
    simp only [mem_forcingClassIntersection_iff]
    apply and_congr_right
    intro _
    apply forall_congr'
    intro x
    apply imp_congr_right
    intro hx
    change p ∈ internalForcingSet P R D (succ (m : V)) (encodeMembershipFormula φ)
      (standardTuple (x :> v)) ↔ _
    rw [← num_succ_def, ih (x :> v) (fun i ↦ Fin.cases hx hv i)]
    rfl
  | @exs m φ ih =>
    change internalForcingSet P R D _ (existsCode (encodeMembershipFormula φ)) _ = _
    rw [internalForcingSet_exists (by simp) (by simpa only [num_succ_def] using hc φ)
      (standardTuple_mem_function v hv), classForcingFormula_exs]
    unfold forcingExistential
    congr 1
    apply mem_ext
    intro p
    simp only [mem_forcingClassUnion_iff]
    apply and_congr_right
    intro _
    apply exists_congr
    intro x
    apply and_congr_right
    intro hx
    change p ∈ internalForcingSet P R D (succ (m : V)) (encodeMembershipFormula φ)
      (standardTuple (x :> v)) ↔ _
    rw [← num_succ_def, ih (x :> v) (fun i ↦ Fin.cases hx hv i)]
    rfl

end ZFVP
