import ZFVP.Syntax.LevyNegation

/-! Internal Sigma-one upward and Pi-one downward preservation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def MembershipSatisfactionUpward (n φ : V) : Prop :=
  ∀ A B : V, IsTransitive A → IsTransitive B → IsNonempty A → IsNonempty B → A ⊆ B →
    ∀ b ∈ A ^ n, MembershipSatisfies A n φ b → MembershipSatisfies B n φ b

instance membershipSatisfactionUpward_definable : ℒₛₑₜ-relation[V] MembershipSatisfactionUpward := by
  unfold MembershipSatisfactionUpward
  definability

theorem sigmaOneCode_upward {n φ : V} (hφ : IsLevyFormulaCode .sigma 1 n φ) :
    MembershipSatisfactionUpward n φ := by
  refine levyFormulaCode_successor_induction 0 .sigma MembershipSatisfactionUpward
    (by definability) ?_ ?_ ?_ ?_ n φ hφ
  · intro p n φ hφ A B hAt hBt hA hB hAB b hb hs
    exact (boundedFormulaCode_absolute hφ A B hAt hBt hA hB b hb
      (mem_function_of_mem_function_of_subset hb hAB)).mp hs
  · intro n hn φ ψ hφ hψ ihφ ihψ
    constructor
    · intro A B hAt hBt hA hB hAB b hb hs
      have hbA : b ∈ structureDomain (membershipStructureCode A) ^ n := by simpa using hb
      have hbB : b ∈ structureDomain (membershipStructureCode B) ^ n := by
        simpa using mem_function_of_mem_function_of_subset hb hAB
      obtain ⟨hsφ, hsψ⟩ := (satisfies_and membershipLanguageCode_valid hn hφ.valid hψ.valid hbA).mp hs
      exact (satisfies_and membershipLanguageCode_valid hn hφ.valid hψ.valid hbB).mpr
        ⟨ihφ A B hAt hBt hA hB hAB b hb hsφ, ihψ A B hAt hBt hA hB hAB b hb hsψ⟩
    · intro A B hAt hBt hA hB hAB b hb hs
      have hbA : b ∈ structureDomain (membershipStructureCode A) ^ n := by simpa using hb
      have hbB : b ∈ structureDomain (membershipStructureCode B) ^ n := by
        simpa using mem_function_of_mem_function_of_subset hb hAB
      apply (satisfies_or membershipLanguageCode_valid hn hφ.valid hψ.valid hbB).mpr
      exact ((satisfies_or membershipLanguageCode_valid hn hφ.valid hψ.valid hbA).mp hs).elim
        (fun h ↦ Or.inl (ihφ A B hAt hBt hA hB hAB b hb h))
        (fun h ↦ Or.inr (ihψ A B hAt hBt hA hB hAB b hb h))
  · intro n hn i hi φ hφ ih
    constructor
    · intro A B hAt hBt hA hB hAB b hb hs
      let := hAt
      let := hBt
      have hbB := mem_function_of_mem_function_of_subset hb hAB
      apply (membershipSatisfies_boundedAll hn hi hφ.valid hbB).mpr
      intro x hx
      have hxA := hAt.transitive _ (function_value_mem hb hi) x hx
      exact ih A B hAt hBt hA hB hAB _ (assignmentPrepend_mem_function hn hb hxA)
        ((membershipSatisfies_boundedAll hn hi hφ.valid hb).mp hs x hx)
    · intro A B hAt hBt hA hB hAB b hb hs
      let := hAt
      let := hBt
      have hbB := mem_function_of_mem_function_of_subset hb hAB
      obtain ⟨x, hx, hsx⟩ := (membershipSatisfies_boundedExists hn hi hφ.valid hb).mp hs
      have hxA := hAt.transitive _ (function_value_mem hb hi) x hx
      exact (membershipSatisfies_boundedExists hn hi hφ.valid hbB).mpr
        ⟨x, hx, ih A B hAt hBt hA hB hAB _ (assignmentPrepend_mem_function hn hb hxA) hsx⟩
  · intro n hn φ hφ ih A B hAt hBt hA hB hAB b hb hs
    have hbA : b ∈ structureDomain (membershipStructureCode A) ^ n := by simpa using hb
    have hbB : b ∈ structureDomain (membershipStructureCode B) ^ n := by
      simpa using mem_function_of_mem_function_of_subset hb hAB
    obtain ⟨x, hx, hsx⟩ := (satisfies_exists membershipLanguageCode_valid hn hφ.valid hbA).mp hs
    have hxA : x ∈ A := by simpa using hx
    exact (satisfies_exists membershipLanguageCode_valid hn hφ.valid hbB).mpr
      ⟨x, by simpa using hAB x hxA,
        ih A B hAt hBt hA hB hAB _ (assignmentPrepend_mem_function hn hb hxA) hsx⟩

theorem membershipSatisfies_sigmaOne_upward {A B n φ b : V} [hAt : IsTransitive A] [hBt : IsTransitive B]
    (hφ : IsLevyFormulaCode .sigma 1 n φ) (hA : IsNonempty A) (hB : IsNonempty B)
    (hAB : A ⊆ B) (hb : b ∈ A ^ n) :
    MembershipSatisfies A n φ b → MembershipSatisfies B n φ b :=
  sigmaOneCode_upward hφ A B hAt hBt hA hB hAB b hb

theorem membershipSatisfies_piOne_downward {A B n φ b : V} [IsTransitive A] [IsTransitive B]
    (hφ : IsLevyFormulaCode .pi 1 n φ) (hA : IsNonempty A) (hB : IsNonempty B)
    (hAB : A ⊆ B) (hb : b ∈ A ^ n) :
    MembershipSatisfies B n φ b → MembershipSatisfies A n φ b := by
  classical
  intro hs
  by_contra hn
  have hbA : b ∈ structureDomain (membershipStructureCode A) ^ n := by simpa using hb
  have hbB : b ∈ structureDomain (membershipStructureCode B) ^ n := by
    simpa using mem_function_of_mem_function_of_subset hb hAB
  have hnegA := (satisfies_negateFormula membershipLanguageCode_valid hφ.valid hbA).mpr hn
  have hnegB := membershipSatisfies_sigmaOne_upward hφ.neg hA hB hAB hb hnegA
  exact (satisfies_negateFormula membershipLanguageCode_valid hφ.valid hbB).mp hnegB hs

end ZFVP
