import ZFVP.ModelTheory.CodedSequentQuantifiers

/-! Set-coded rules for classical membership sequents, with theory axioms and cut. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

def IsCodedSequentRule (T P n Γ : V) : Prop :=
  (n = 0 ∧ ∃ φ ∈ T, Γ = {φ}) ∨
  (∃ φ ∈ formulaSet membershipLanguageCode ∅ n, Γ = {φ, negateFormula membershipLanguageCode ∅ n φ}) ∨
  Γ = {truthCode} ∨
  (∃ Δ φ ψ, φ ∈ formulaSet membershipLanguageCode ∅ n ∧ ψ ∈ formulaSet membershipLanguageCode ∅ n ∧
    Γ = insert (orCode φ ψ) Δ ∧ ⟨n, insert φ (insert ψ Δ)⟩ₖ ∈ P) ∨
  (∃ Δ φ ψ, φ ∈ formulaSet membershipLanguageCode ∅ n ∧ ψ ∈ formulaSet membershipLanguageCode ∅ n ∧
    Γ = insert (andCode φ ψ) Δ ∧ ⟨n, insert φ Δ⟩ₖ ∈ P ∧ ⟨n, insert ψ Δ⟩ₖ ∈ P) ∨
  (∃ Δ Ξ φ, φ ∈ formulaSet membershipLanguageCode ∅ n ∧ Γ = Δ ∪ Ξ ∧
    ⟨n, insert φ Δ⟩ₖ ∈ P ∧ ⟨n, insert (negateFormula membershipLanguageCode ∅ n φ) Ξ⟩ₖ ∈ P) ∨
  (∃ Δ φ, Δ ⊆ formulaSet membershipLanguageCode ∅ n ∧ φ ∈ formulaSet membershipLanguageCode ∅ (succ n) ∧
    Γ = insert (allCode φ) Δ ∧ ⟨succ n, insert φ (shiftCodedSequent n Δ)⟩ₖ ∈ P) ∨
  (∃ Δ φ i, i ∈ n ∧ φ ∈ formulaSet membershipLanguageCode ∅ (succ n) ∧
    Γ = insert (existsCode φ) Δ ∧ ⟨n, insert (instantiateMembershipFormula n i φ) Δ⟩ₖ ∈ P) ∨
  (∃ Δ, Δ ⊆ Γ ∧ ⟨n, Δ⟩ₖ ∈ P) ∨
  ∃ m r Δ, m ∈ (ω : V) ∧ r ∈ n ^ m ∧ Δ ⊆ formulaSet membershipLanguageCode ∅ m ∧
    Γ = renameCodedSequent m n r Δ ∧ ⟨m, Δ⟩ₖ ∈ P

instance isCodedSequentRule_definable : ℒₛₑₜ-relation₄[V] IsCodedSequentRule := by
  unfold IsCodedSequentRule truthCode
  repeat' apply Language.Definable.or
  all_goals definability

theorem codedSequentTrue_theory {U T φ : V} (hT : SatisfiesSentenceCodes U T) (hφ : φ ∈ T) :
    CodedSequentTrue U 0 ({φ} : V) := by
  intro b hb
  have he : b = (∅ : V) := by
    apply function_eq_of_values hb (show (∅ : V) ∈ U ^ (0 : V) from by simp [mem_function_iff, zero_def])
    intro i hi
    exact False.elim (not_mem_empty hi)
  rw [he]
  exact ⟨φ, by simp, (hT.2 φ hφ).2⟩

theorem IsCodedSequentRule.sound {U T P n Γ : V} (hT : SatisfiesSentenceCodes U T)
    (hn : n ∈ (ω : V)) (hP : ∀ m Δ, ⟨m, Δ⟩ₖ ∈ P → CodedSequentTrue U m Δ)
    (hr : IsCodedSequentRule T P n Γ) : CodedSequentTrue U n Γ := by
  rcases hr with ⟨rfl, φ, hφ, rfl⟩ | ⟨φ, hφ, rfl⟩ | rfl |
    ⟨Δ, φ, ψ, hφ, hψ, rfl, hp⟩ | ⟨Δ, φ, ψ, hφ, hψ, rfl, hp, hq⟩ |
    ⟨Δ, Ξ, φ, hφ, rfl, hp, hq⟩ | ⟨Δ, φ, hΔ, hφ, rfl, hp⟩ |
    ⟨Δ, φ, i, hi, hφ, rfl, hp⟩ | ⟨Δ, hΔ, hp⟩ | ⟨m, r, Δ, hm, hmr, hΔ, rfl, hp⟩
  · exact codedSequentTrue_theory hT hφ
  · exact codedSequentTrue_identity hφ
  · exact codedSequentTrue_verum hn
  · exact codedSequentTrue_or hn hφ hψ (hP _ _ hp)
  · exact codedSequentTrue_and hn hφ hψ (hP _ _ hp) (hP _ _ hq)
  · exact codedSequentTrue_cut hφ (hP _ _ hp) (hP _ _ hq)
  · exact codedSequentTrue_all hT.1 hn hΔ hφ (hP _ _ hp)
  · exact codedSequentTrue_exists hT.1 hn hi hφ (hP _ _ hp)
  · exact codedSequentTrue_weaken (hP _ _ hp) hΔ
  · exact codedSequentTrue_rename hT.1 hm hn hmr hΔ (hP _ _ hp)

end ZFVP
