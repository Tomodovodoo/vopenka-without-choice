import ZFVP.ModelTheory.InternalHenkinImplication

/-! Iterated context extension respects the formula operations and syntactic
implications. All iteration indices range over the internal omega. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem naturalIteration_add (F : V → V) (hF : ℒₛₑₜ-function₁ F) (a : V)
    {i j : V} (hi : i ∈ (ω : V)) (hj : j ∈ (ω : V)) :
    naturalIteration F hF (naturalIteration F hF a i) j = naturalIteration F hF a (ordinalAdd i j) := by
  apply naturalNumber_induction (fun j ↦
    naturalIteration F hF (naturalIteration F hF a i) j = naturalIteration F hF a (ordinalAdd i j))
    (by definability) ?_ ?_ j hj
  · rw [naturalIteration_zero]
    rw [zero_def, ordinalAdd_zero]
  · intro j hj ih
    have : IsOrdinal i := IsOrdinal.of_mem hi
    have : IsOrdinal j := IsOrdinal.of_mem hj
    rw [naturalIteration_succ F hF _ hj, ih, ordinalAdd_succ,
      naturalIteration_succ F hF a (ordinalAdd_natural hi hj)]

theorem henkinLiftCode_add (p : V) {i j : V} (hi : i ∈ (ω : V)) (hj : j ∈ (ω : V)) :
    henkinLiftCode (henkinLiftCode p i) j = henkinLiftCode p (ordinalAdd i j) :=
  naturalIteration_add _ _ _ hi hj

theorem henkinLiftCode_negate {n φ k : V} (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n)
    (hk : k ∈ (ω : V)) :
    henkinLiftCode ⟨n, negateFormula membershipLanguageCode ∅ n φ⟩ₖ k =
      ⟨kpair.π₁ (henkinLiftCode ⟨n, φ⟩ₖ k),
        negateFormula membershipLanguageCode ∅ (kpair.π₁ (henkinLiftCode ⟨n, φ⟩ₖ k))
          (kpair.π₂ (henkinLiftCode ⟨n, φ⟩ₖ k))⟩ₖ := by
  apply naturalNumber_induction (fun k ↦
    henkinLiftCode ⟨n, negateFormula membershipLanguageCode ∅ n φ⟩ₖ k =
      ⟨kpair.π₁ (henkinLiftCode ⟨n, φ⟩ₖ k),
        negateFormula membershipLanguageCode ∅ (kpair.π₁ (henkinLiftCode ⟨n, φ⟩ₖ k))
          (kpair.π₂ (henkinLiftCode ⟨n, φ⟩ₖ k))⟩ₖ) (by definability) ?_ ?_ k hk
  · simp only [henkinLiftCode_zero, kpair.π₁_kpair, kpair.π₂_kpair]
  · intro k hk ih
    rw [henkinLiftCode_succ _ hk, henkinLiftCode_succ _ hk, ih]
    have hv := henkinLiftCode_valid hφ hk
    simp only [henkinShiftCode, kpair.π₁_kpair, kpair.π₂_kpair,
      henkinShiftFormula_negate (formulaSet_context membershipLanguageCode_valid hv) hv]

theorem henkinLiftCode_and {n φ ψ k : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n)
    (hk : k ∈ (ω : V)) :
    henkinLiftCode ⟨n, andCode φ ψ⟩ₖ k =
      ⟨ordinalAdd n k, andCode (kpair.π₂ (henkinLiftCode ⟨n, φ⟩ₖ k))
        (kpair.π₂ (henkinLiftCode ⟨n, ψ⟩ₖ k))⟩ₖ := by
  have hn := formulaSet_context membershipLanguageCode_valid hφ
  apply naturalNumber_induction (fun k ↦
    henkinLiftCode ⟨n, andCode φ ψ⟩ₖ k =
      ⟨ordinalAdd n k, andCode (kpair.π₂ (henkinLiftCode ⟨n, φ⟩ₖ k))
        (kpair.π₂ (henkinLiftCode ⟨n, ψ⟩ₖ k))⟩ₖ) (by definability) ?_ ?_ k hk
  · simp only [henkinLiftCode_zero, kpair.π₂_kpair]
    rw [zero_def, ordinalAdd_zero]
  · intro k hk ih
    have : IsOrdinal n := IsOrdinal.of_mem hn
    have : IsOrdinal k := IsOrdinal.of_mem hk
    have hf := henkinLiftCode_valid hφ hk
    have hg := henkinLiftCode_valid hψ hk
    rw [henkinLiftCode_context hn hk] at hf hg
    simp only [henkinLiftCode_succ _ hk, ih, henkinShiftCode, kpair.π₁_kpair, kpair.π₂_kpair,
      henkinLiftCode_context hn hk, henkinShiftFormula, renameMembershipFormula_and hf hg, ordinalAdd_succ]

theorem CodedFormulaImplies.lift (hω : Schmerl.HasStandardOmega V) {T n φ ψ k : V}
    (h : CodedFormulaImplies T n φ ψ) (hk : k ∈ (ω : V)) :
    CodedFormulaImplies T (ordinalAdd n k) (kpair.π₂ (henkinLiftCode ⟨n, φ⟩ₖ k))
      (kpair.π₂ (henkinLiftCode ⟨n, ψ⟩ₖ k)) := by
  have hn := formulaSet_context membershipLanguageCode_valid h.1
  apply naturalNumber_induction (fun k ↦
    CodedFormulaImplies T (ordinalAdd n k) (kpair.π₂ (henkinLiftCode ⟨n, φ⟩ₖ k))
      (kpair.π₂ (henkinLiftCode ⟨n, ψ⟩ₖ k))) (by definability) ?_ ?_ k hk
  · simp only [henkinLiftCode_zero, kpair.π₂_kpair]
    simpa only [zero_def, ordinalAdd_zero] using h
  · intro k hk ih
    have : IsOrdinal n := IsOrdinal.of_mem hn
    have : IsOrdinal k := IsOrdinal.of_mem hk
    simp only [henkinLiftCode_succ _ hk, henkinShiftCode, kpair.π₂_kpair,
      henkinLiftCode_context hn hk, ordinalAdd_succ, henkinShiftFormula]
    exact ih.rename hω (ω_succ_closed (ordinalAdd_natural hn hk))
      (successorIndices_function (ordinalAdd_natural hn hk))

end ZFVP
