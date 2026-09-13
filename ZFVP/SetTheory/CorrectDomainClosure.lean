import ZFVP.SetTheory.HigherPartialTruth

/-! Nesting and cofinal closure of the recursively correct rank stages. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem CorrectDomain.of_le {k l : ℕ} {A : V} (hA : CorrectDomain l A) (hkl : k ≤ l) : CorrectDomain k A := by
  induction hkl with
  | refl => exact hA
  | step _ ih => exact ih hA.lower

theorem correctDomain_of_cofinal (k : ℕ) {δ : V} [IsOrdinal δ]
    (hω : (ω : V) ∈ δ) (hlim : ∀ ξ ∈ δ, succ ξ ∈ δ)
    (h : ∀ ξ ∈ δ, ∃ α ∈ δ, ξ ∈ α ∧ CorrectDomain k (hierarchy α)) :
    CorrectDomain k (hierarchy δ) := by
  let := hierarchy_isSequenceSupport hω hlim
  induction k with
  | zero => exact hierarchy_isSequenceSupport hω hlim
  | succ k ih =>
    have hδ : CorrectDomain k (hierarchy δ) := ih (fun ξ hξ ↦ by
      obtain ⟨α, hα, hξα, hD⟩ := h ξ hξ
      exact ⟨α, hα, hξα, hD.lower⟩)
    refine ⟨hδ, ?_⟩
    intro n _ φ _ b hb hcode htyped htruth
    obtain ⟨α, hα, hrank, hD⟩ := h (rank b) ((mem_hierarchy_iff_rank_mem b δ).mp hb)
    let := IsOrdinal.of_mem hα
    let := hD.support
    have hbα : b ∈ hierarchy α := (mem_hierarchy_iff_rank_mem b α).mpr hrank
    have htypedα : b ∈ hierarchy α ^ n := (function_on_support_iff hbα n).mpr
      ⟨IsFunction.of_mem htyped, domain_eq_of_mem_function htyped⟩
    have hs := (hD.sigmaTruth_iff hcode htypedα).mp htruth
    exact correctDomainCode_upward k hcode (hierarchy α) (hierarchy δ) hD.lower hδ
      (hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ hα)) b htypedα hs

theorem domainSigmaTruth_stable {k l : ℕ} (hkl : k ≤ l) {n φ b : V}
    (hφ : IsLevyFormulaCode .sigma (k + 1) n φ) :
    DomainSigmaTruth k n φ b ↔ DomainSigmaTruth l n φ b := by
  constructor
  · rintro ⟨A, hA, hb, hs⟩
    obtain ⟨B, hB, hAB⟩ := correctDomain_containing l A
    have hsub := hB.support.transitive A hAB
    exact ⟨B, hB, mem_function_of_mem_function_of_subset hb hsub,
      correctDomainCode_upward k hφ A B hA (hB.of_le hkl) hsub b hb hs⟩
  · rintro ⟨A, hA, hb, hs⟩
    exact ⟨A, hA.of_le hkl, hb, hs⟩

theorem domainPiTruth_stable {k l : ℕ} (hkl : k ≤ l) {n φ b : V}
    (hφ : IsLevyFormulaCode .pi (k + 1) n φ) :
    DomainPiTruth k n φ b ↔ DomainPiTruth l n φ b := by
  have hvalid : IsMembershipFormulaCode n φ := (mem_formulaSet_iff _ _ _ _).mp hφ.valid
  rw [domainPiTruth_iff_not_sigma_negate k hvalid, domainPiTruth_iff_not_sigma_negate l hvalid]
  exact not_congr (domainSigmaTruth_stable hkl hφ.neg)

theorem CorrectDomain.standard_sigma_correct {k n : ℕ} {A : V} (hA : CorrectDomain (k + 1) A)
    {φ : SetTheorySemisentence n} (hφ : IsSigmaFormula (k + 1) φ) (b : Fin n → V)
    (hb : standardTuple b ∈ A ^ (n : V)) :
    MembershipSatisfies A (n : V) (encodeMembershipFormula φ) (standardTuple b) ↔ φ.Evalb b :=
  (hA.sigmaTruth_iff hφ.encode hb).symm.trans (domainSigmaTruth_correct k hφ b)

theorem CorrectDomain.standard_pi_correct {k n : ℕ} {A : V} (hA : CorrectDomain (k + 1) A)
    {φ : SetTheorySemisentence n} (hφ : IsPiFormula (k + 1) φ) (b : Fin n → V)
    (hb : standardTuple b ∈ A ^ (n : V)) :
    MembershipSatisfies A (n : V) (encodeMembershipFormula φ) (standardTuple b) ↔ φ.Evalb b := by
  obtain ⟨B, hB, _, hbB, href⟩ := correctDomain_reflectingMembership (k + 1) φ b A
  exact (correctDomain_code_absolute hA hB hφ.encode hb hbB).trans href

end ZFVP
