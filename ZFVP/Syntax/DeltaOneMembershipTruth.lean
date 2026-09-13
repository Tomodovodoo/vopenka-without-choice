import ZFVP.Syntax.SigmaOneMembershipModelTruth

/-! Sigma-one and Pi-one definitions of satisfaction over arbitrary set domains. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneNotMembershipTruthFormula : SetTheorySemisentence 4 :=
  “A n φ b. ∃ F, !sigmaOneMembershipFamilyFormula F ∧
    (¬!boundedPairMemberFormula F n φ ∨ ¬!boundedFunctionFormula b n A ∨
      !(sigmaOneMembershipModelTruthFormula false) A n φ b)”

def piOneMembershipTruthFormula : SetTheorySemisentence 4 := ∼sigmaOneNotMembershipTruthFormula

theorem sigmaOneNotMembershipTruthFormula_sigmaOne : IsLevyFormula .sigma 1 sigmaOneNotMembershipTruthFormula :=
  .exs (.and (sigmaOneMembershipFamilyFormula_sigmaOne.subst _)
    (.or (.bounded (boundedPairMemberFormula_bounded.subst _).neg)
      (.or (.bounded (boundedFunctionFormula_bounded.subst _).neg)
        ((sigmaOneMembershipModelTruthFormula_sigmaOne false).subst _))))

theorem piOneMembershipTruthFormula_piOne : IsLevyFormula .pi 1 piOneMembershipTruthFormula :=
  sigmaOneNotMembershipTruthFormula_sigmaOne.neg

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem membershipSatisfies_valid {A n φ b : V} (h : MembershipSatisfies A n φ b) :
    IsMembershipFormulaCode n φ ∧ b ∈ A ^ n := by
  have hs : Satisfies membershipLanguageCode ∅ (membershipStructureCode A) ∅ n φ b := h
  have hφ := satisfies_formula_mem hs
  exact ⟨(mem_formulaSet_iff _ _ _ _).mp hφ, by simpa using satisfies_assignment_mem hφ hs⟩

theorem eval_sigmaOneMembershipTruthFormula (A n φ b : V) :
    (sigmaOneMembershipModelTruthFormula true).Evalb ![A, n, φ, b] ↔ MembershipSatisfies A n φ b := by
  rw [eval_sigmaOneMembershipModelTruthFormula]
  change (IsMembershipFormulaCode n φ ∧ b ∈ A ^ n ∧ MembershipSatisfies A n φ b) ↔ _
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨(membershipSatisfies_valid h).1, (membershipSatisfies_valid h).2, h⟩⟩

theorem eval_sigmaOneNotMembershipTruthFormula (A n φ b : V) :
    sigmaOneNotMembershipTruthFormula.Evalb ![A, n, φ, b] ↔ ¬MembershipSatisfies A n φ b := by
  simp [sigmaOneNotMembershipTruthFormula, eval_sigmaOneMembershipModelTruthFormula, TruthAnswer]
  constructor
  · intro h hs
    obtain ⟨hφ, hb⟩ := membershipSatisfies_valid hs
    exact h.elim (fun h ↦ h hφ) (fun h ↦ h.elim (fun h ↦ h hb) (fun h ↦ h.2.2 hs))
  · intro h
    by_cases hφ : IsMembershipFormulaCode n φ
    · by_cases hb : b ∈ A ^ n
      · exact Or.inr (Or.inr ⟨hφ, hb, h⟩)
      · exact Or.inr (Or.inl hb)
    · exact Or.inl hφ

theorem eval_piOneMembershipTruthFormula (A n φ b : V) :
    piOneMembershipTruthFormula.Evalb ![A, n, φ, b] ↔ MembershipSatisfies A n φ b := by
  simp [piOneMembershipTruthFormula, eval_sigmaOneNotMembershipTruthFormula]

instance sigmaOneMembershipTruthFormula_defined :
    ℒₛₑₜ-relation₄[V] MembershipSatisfies via sigmaOneMembershipModelTruthFormula true :=
  ⟨fun (v : Fin 4 → V) ↦ by
    have hv : ![v 0, v 1, v 2, v 3] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun t ↦ Fin.cases rfl (fun u ↦ Fin.elim0 u) t) k) j) i
    change (sigmaOneMembershipModelTruthFormula true).Evalb v ↔ MembershipSatisfies (v 0) (v 1) (v 2) (v 3)
    rw [← hv]
    exact eval_sigmaOneMembershipTruthFormula (v 0) (v 1) (v 2) (v 3)⟩

instance piOneMembershipTruthFormula_defined :
    ℒₛₑₜ-relation₄[V] MembershipSatisfies via piOneMembershipTruthFormula :=
  ⟨fun (v : Fin 4 → V) ↦ by
    have hv : ![v 0, v 1, v 2, v 3] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun t ↦ Fin.cases rfl (fun u ↦ Fin.elim0 u) t) k) j) i
    change piOneMembershipTruthFormula.Evalb v ↔ MembershipSatisfies (v 0) (v 1) (v 2) (v 3)
    rw [← hv]
    exact eval_piOneMembershipTruthFormula (v 0) (v 1) (v 2) (v 3)⟩

end ZFVP
