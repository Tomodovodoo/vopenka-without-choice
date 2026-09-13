import ZFVP.Syntax.VopenkaAxiomSet
import ZFVP.SetTheory.FiniteDictionary

/-! Uniform semantics for internally finite membership sequents and their Boolean rules. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsCodedSequent (n Γ : V) : Prop :=
  n ∈ (ω : V) ∧ IsInternallyFinite Γ ∧ Γ ⊆ formulaSet membershipLanguageCode ∅ n

def CodedSequentHolds (U n Γ b : V) : Prop := ∃ φ ∈ Γ, MembershipSatisfies U n φ b

def CodedSequentTrue (U n Γ : V) : Prop := ∀ b ∈ U ^ n, CodedSequentHolds U n Γ b

instance isCodedSequent_definable : ℒₛₑₜ-relation[V] IsCodedSequent := by
  unfold IsCodedSequent
  definability

instance codedSequentHolds_definable : ℒₛₑₜ-relation₄[V] CodedSequentHolds := by
  unfold CodedSequentHolds
  definability

instance codedSequentTrue_definable : ℒₛₑₜ-relation₃[V] CodedSequentTrue := by
  unfold CodedSequentTrue
  definability

theorem codedSequentHolds_insert (U n Γ φ b : V) :
    CodedSequentHolds U n (insert φ Γ) b ↔ MembershipSatisfies U n φ b ∨ CodedSequentHolds U n Γ b := by
  simp [CodedSequentHolds, or_and_right, exists_or]

theorem codedSequentHolds_union (U n Γ Δ b : V) :
    CodedSequentHolds U n (Γ ∪ Δ) b ↔ CodedSequentHolds U n Γ b ∨ CodedSequentHolds U n Δ b := by
  simp [CodedSequentHolds, or_and_right, exists_or]

theorem membershipSatisfies_and {U n φ ψ b : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n)
    (hb : b ∈ U ^ n) :
    MembershipSatisfies U n (andCode φ ψ) b ↔ MembershipSatisfies U n φ b ∧ MembershipSatisfies U n ψ b :=
  satisfies_and membershipLanguageCode_valid hn hφ hψ (by simpa using hb)

theorem membershipSatisfies_or {U n φ ψ b : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n)
    (hb : b ∈ U ^ n) :
    MembershipSatisfies U n (orCode φ ψ) b ↔ MembershipSatisfies U n φ b ∨ MembershipSatisfies U n ψ b :=
  satisfies_or membershipLanguageCode_valid hn hφ hψ (by simpa using hb)

theorem membershipSatisfies_negate {U n φ b : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hb : b ∈ U ^ n) :
    MembershipSatisfies U n (negateFormula membershipLanguageCode ∅ n φ) b ↔ ¬MembershipSatisfies U n φ b :=
  satisfies_negateFormula membershipLanguageCode_valid hφ (by simpa using hb)

theorem codedSequentTrue_identity {U n φ : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    CodedSequentTrue U n {φ, negateFormula membershipLanguageCode ∅ n φ} := by
  classical
  intro b hb
  by_cases ht : MembershipSatisfies U n φ b
  · exact ⟨φ, by simp, ht⟩
  · exact ⟨negateFormula membershipLanguageCode ∅ n φ, by simp, (membershipSatisfies_negate hφ hb).mpr ht⟩

theorem codedSequentTrue_verum {U n : V} (hn : n ∈ (ω : V)) :
    CodedSequentTrue U n ({truthCode} : V) := by
  intro b hb
  exact ⟨truthCode, by simp, (satisfies_truth membershipLanguageCode_valid hn).mpr (by simpa using hb)⟩

theorem codedSequentTrue_weaken {U n Γ Δ : V} (hΓ : CodedSequentTrue U n Γ) (hsub : Γ ⊆ Δ) :
    CodedSequentTrue U n Δ := by
  intro b hb
  obtain ⟨φ, hφ, ht⟩ := hΓ b hb
  exact ⟨φ, hsub _ hφ, ht⟩

theorem codedSequentTrue_or {U n Γ φ ψ : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n)
    (hΓ : CodedSequentTrue U n (insert φ (insert ψ Γ))) :
    CodedSequentTrue U n (insert (orCode φ ψ) Γ) := by
  intro b hb
  have ht := hΓ b hb
  rw [codedSequentHolds_insert, codedSequentHolds_insert] at ht
  rw [codedSequentHolds_insert, membershipSatisfies_or hn hφ hψ hb]
  exact or_assoc.mpr ht

theorem codedSequentTrue_and {U n Γ φ ψ : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n)
    (hΓφ : CodedSequentTrue U n (insert φ Γ)) (hΓψ : CodedSequentTrue U n (insert ψ Γ)) :
    CodedSequentTrue U n (insert (andCode φ ψ) Γ) := by
  intro b hb
  have hs := (codedSequentHolds_insert _ _ _ _ _).mp (hΓφ b hb)
  have ht := (codedSequentHolds_insert _ _ _ _ _).mp (hΓψ b hb)
  rw [codedSequentHolds_insert, membershipSatisfies_and hn hφ hψ hb]
  rcases hs with hs | hs
  · exact ht.elim (fun ht ↦ Or.inl ⟨hs, ht⟩) Or.inr
  · exact Or.inr hs

theorem codedSequentTrue_cut {U n Γ Δ φ : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n)
    (hΓ : CodedSequentTrue U n (insert φ Γ))
    (hΔ : CodedSequentTrue U n (insert (negateFormula membershipLanguageCode ∅ n φ) Δ)) :
    CodedSequentTrue U n (Γ ∪ Δ) := by
  intro b hb
  have hs := (codedSequentHolds_insert _ _ _ _ _).mp (hΓ b hb)
  have ht := (codedSequentHolds_insert _ _ _ _ _).mp (hΔ b hb)
  rw [membershipSatisfies_negate hφ hb] at ht
  rw [codedSequentHolds_union]
  rcases hs with hs | hs
  · exact Or.inr (ht.resolve_left (not_not.mpr hs))
  · exact Or.inl hs

theorem not_codedSequentTrue_empty (U : V) : ¬CodedSequentTrue U 0 ∅ := by
  intro h
  obtain ⟨φ, hφ, _⟩ := h ∅ (by simp [mem_function_iff, zero_def])
  exact not_mem_empty hφ

end ZFVP
