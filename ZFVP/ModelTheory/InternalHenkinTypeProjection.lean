import ZFVP.ModelTheory.InternalHenkinUnaryInstances

/-! Existentially project a consistent finite condition to one distinguished
name. If the condition implies all instances of a unary type, its projection
is an ordinary consistent unary formula implying that type. -/

set_option autoImplicit false

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem CodedFormulaImplies.exists_left (hω : Schmerl.HasStandardOmega V) {T n φ ψ : V}
    (hn : n ∈ (ω : V)) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n))
    (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n)
    (h : CodedFormulaImplies T (succ n) φ (henkinShiftFormula n ψ)) :
    CodedFormulaImplies T n (existsCode φ) ψ := by
  have hnf := negateFormula_mem membershipLanguageCode_valid hφ
  have hne := (formulaSet_quantifiers membershipLanguageCode_valid hn hφ).2
  have hp := ((codedFormulaImplies_iff_standard hω _ _ _ _).mp h).2.2
  have he : ({henkinShiftFormula n ψ, negateFormula membershipLanguageCode ∅ (succ n) φ} : V) =
      insert (negateFormula membershipLanguageCode ∅ (succ n) φ) (shiftCodedSequent n ({ψ} : V)) := by
    rw [shiftCodedSequent_singleton]
    ext x
    simp
    tauto
  rw [he] at hp
  have hv := (isCodedSequent_singleton hn hψ).insert (formulaSet_quantifiers membershipLanguageCode_valid hn hnf).1
  have ha := hp.all hv (fun x hx ↦ (mem_singleton_iff.mp hx).symm ▸ hψ) hnf
  have he' : insert (allCode (negateFormula membershipLanguageCode ∅ (succ n) φ)) ({ψ} : V) =
      ({ψ, negateFormula membershipLanguageCode ∅ n (existsCode φ)} : V) := by
    rw [negateFormula_exists membershipLanguageCode_valid hn hφ]
    ext x
    simp
    tauto
  rw [he'] at ha
  exact ⟨hne, hψ, ha.to_internal⟩

theorem IsConsistentCodedFormula.exists_projection (hω : Schmerl.HasStandardOmega V) {T n φ : V}
    (hn : n ∈ (ω : V)) (h : IsConsistentCodedFormula T (succ n) φ) :
    IsConsistentCodedFormula T n (existsCode φ) := by
  have hcon := (CodedFormulaImplies.witness_exists T hn h.1).consistent hω h
  exact hcon.of_renamed hω (formulaSet_quantifiers membershipLanguageCode_valid hn h.1).2
    (ω_succ_closed hn) (successorIndices_function hn)

theorem exists_unary_principal_of_last (hω : Schmerl.HasStandardOmega V) {T P : V}
    (hP : P ⊆ formulaSet (membershipLanguageCode : V) ∅ 1) (k : ℕ) {χ : V}
    (hχ : IsConsistentCodedFormula T ((k + 1 : ℕ) : V) χ)
    (hall : ∀ ψ ∈ P, CodedFormulaImplies T ((k + 1 : ℕ) : V) χ
      (unaryCodedInstance ((k + 1 : ℕ) : V) (k : V) ψ)) :
    ∃ θ : V, IsConsistentCodedFormula T 1 θ ∧ ∀ ψ ∈ P, CodedFormulaImplies T 1 θ ψ := by
  induction k generalizing χ with
  | zero =>
    refine ⟨χ, hχ, ?_⟩
    intro ψ hψ
    have h := hall ψ hψ
    change CodedFormulaImplies T 1 χ (unaryCodedInstance 1 0 ψ) at h
    rwa [unaryCodedInstance_zero (hP ψ hψ)] at h
  | succ k ih =>
    have hn : ((k + 1 : ℕ) : V) ∈ (ω : V) := by simp
    have hk : (k : V) ∈ ((k + 1 : ℕ) : V) := natCast_mem_of_lt (Nat.lt_succ_self k)
    have hc : IsConsistentCodedFormula T (succ ((k + 1 : ℕ) : V)) χ := by
      simpa only [num_succ_def] using hχ
    apply ih (χ := existsCode χ) (hc.exists_projection hω hn)
    intro ψ hψ
    apply CodedFormulaImplies.exists_left hω hn hc.1 (unaryCodedInstance_valid hn hk (hP ψ hψ))
    have hh := hall ψ hψ
    have he := unaryCodedInstance_shift hn hk (hP ψ hψ)
    rw [he]
    simpa only [num_succ_def] using hh

theorem exists_unary_principal_of_context (hω : Schmerl.HasStandardOmega V) {T P n i χ : V}
    (hP : P ⊆ formulaSet (membershipLanguageCode : V) ∅ 1) (hχ : IsConsistentCodedFormula T n χ) (hi : i ∈ n)
    (hall : ∀ ψ ∈ P, CodedFormulaImplies T n χ (unaryCodedInstance n i ψ)) :
    ∃ θ : V, IsConsistentCodedFormula T 1 θ ∧ ∀ ψ ∈ P, CodedFormulaImplies T 1 θ ψ := by
  obtain ⟨k, rfl⟩ := hω n hχ.context
  cases k with
  | zero => exact (not_mem_empty hi).elim
  | succ k =>
    have hn := hχ.context
    have hk : (k : V) ∈ ((k + 1 : ℕ) : V) := natCast_mem_of_lt (Nat.lt_succ_self k)
    let r := swapCodedIndices ((k + 1 : ℕ) : V) i (k : V)
    have hr : r ∈ ((k + 1 : ℕ) : V) ^ ((k + 1 : ℕ) : V) := swapCodedIndices_function hi hk
    have hri : r ‘ i = (k : V) := by
      rw [swapCodedIndices_value hi]
      simp only [swapCodedIndex, ite_true]
    have hcon := hχ.permute hω hr (swapCodedIndices_compose hi hk)
    apply exists_unary_principal_of_last hω hP k hcon
    intro ψ hψ
    have h := (hall ψ hψ).rename hω hn hr
    rw [unaryCodedInstance_rename hn hn hi hr (hP ψ hψ), hri] at h
    exact h

end ZFVP
