import ZFVP.ModelTheory.ElementaryInclusion

/-! Elementary inclusions preserve satisfaction on the original assignment graph. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsElementaryInclusion

variable {A B C : V}

theorem refl (hA : IsNonempty A) : IsElementaryInclusion A A := IsCodedMembershipEmbedding.identity hA

theorem trans (hAB : IsElementaryInclusion A B) (hBC : IsElementaryInclusion B C) :
    IsElementaryInclusion A C := by
  have h := IsCodedMembershipEmbedding.comp hAB hBC
  rw [graph_compose_identity hAB.function] at h
  exact h

theorem satisfaction_iff (h : IsElementaryInclusion A B) {n φ b : V}
    (hn : n ∈ (ω : V)) (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ A ^ n) :
    MembershipSatisfies A n φ b ↔ MembershipSatisfies B n φ b := by
  have he := h.satisfies_iff hn ((mem_formulaSet_iff _ _ _ _).mpr hφ) (by simpa using hb)
  rw [graph_compose_identity hb] at he
  exact he

theorem of_satisfaction (hA : IsNonempty A) (hB : IsNonempty B) (hsub : A ⊆ B)
    (he : ∀ n ∈ (ω : V), ∀ φ, IsMembershipFormulaCode n φ → ∀ b ∈ A ^ n,
      MembershipSatisfies A n φ b ↔ MembershipSatisfies B n φ b) : IsElementaryInclusion A B := by
  refine ⟨membershipStructureCode_valid hA, membershipStructureCode_valid hB,
    by simpa using mem_function_of_mem_function_of_subset (identity_mem_function A) hsub, ?_⟩
  intro n hn φ hφ b hb
  have hb' : b ∈ A ^ n := by simpa using hb
  rw [graph_compose_identity hb']
  exact he n hn φ ((mem_formulaSet_iff _ _ _ _).mp hφ) b hb'

end IsElementaryInclusion

end ZFVP
