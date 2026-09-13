import ZFVP.ModelTheory.CodedEmbeddingTransport
import ZFVP.SetTheory.BoundedComposition
import ZFVP.Syntax.DeltaOneMembershipTruth
import ZFVP.SetTheory.DeltaOneBoundedTruth

/-! Coded elementary embeddings of membership structures have a Pi-one definition in ZF. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def piOneMembershipEmbeddingFormula : SetTheorySemisentence 3 :=
  “A B f. !boundedNonemptyFormula A ∧ !boundedNonemptyFormula B ∧
    !boundedFunctionFormula f A B ∧ ∀ n φ b c,
      !boundedFunctionFormula b n A → !boundedComposedAssignmentFormula n A B b f c →
        ((!(sigmaOneMembershipModelTruthFormula true) A n φ b → !piOneMembershipTruthFormula B n φ c) ∧
         (!(sigmaOneMembershipModelTruthFormula true) B n φ c → !piOneMembershipTruthFormula A n φ b))”

theorem piOneMembershipEmbeddingFormula_piOne : IsLevyFormula .pi 1 piOneMembershipEmbeddingFormula :=
  .and (.bounded (boundedNonemptyFormula_bounded.subst _))
    (.and (.bounded (boundedNonemptyFormula_bounded.subst _))
      (.and (.bounded (boundedFunctionFormula_bounded.subst _))
        (.all (.all (.all (.all (.or (.bounded (boundedFunctionFormula_bounded.subst _).neg)
          (.or (.bounded (boundedComposedAssignmentFormula_bounded.subst _).neg)
            (.and
              (.or ((sigmaOneMembershipModelTruthFormula_sigmaOne true).subst _).neg
                (piOneMembershipTruthFormula_piOne.subst _))
              (.or ((sigmaOneMembershipModelTruthFormula_sigmaOne true).subst _).neg
                (piOneMembershipTruthFormula_piOne.subst _)))))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem codedMembershipEmbedding_iff_all_satisfaction {A B f : V} :
    IsCodedMembershipEmbedding A B f ↔ IsNonempty A ∧ IsNonempty B ∧ f ∈ B ^ A ∧
      ∀ n φ b, b ∈ A ^ n →
        (MembershipSatisfies A n φ b ↔ MembershipSatisfies B n φ (compose b f)) := by
  constructor
  · intro h
    refine ⟨h.source_nonempty, h.target_nonempty, h.function, ?_⟩
    intro n φ b hb
    by_cases hφ : IsMembershipFormulaCode n φ
    · exact h.satisfies_iff hφ.context hφ.valid (by simpa using hb)
    · have ha : ¬MembershipSatisfies A n φ b := fun hs ↦ hφ (membershipSatisfies_valid hs).1
      have hc : ¬MembershipSatisfies B n φ (compose b f) := fun hs ↦ hφ (membershipSatisfies_valid hs).1
      simp [ha, hc]
  · rintro ⟨hA, hB, hf, h⟩
    refine ⟨membershipStructureCode_valid hA, membershipStructureCode_valid hB, by simpa using hf, ?_⟩
    intro n hn φ hφ b hb
    exact h n φ b (by simpa using hb)

theorem eval_piOneMembershipEmbeddingFormula (A B f : V) :
    piOneMembershipEmbeddingFormula.Evalb ![A, B, f] ↔ IsCodedMembershipEmbedding A B f := by
  rw [codedMembershipEmbedding_iff_all_satisfaction]
  simp [piOneMembershipEmbeddingFormula]
  intro hA hB hf
  constructor
  · intro h n φ b hb
    have hc := (isComposedAssignment_iff hb hf).mpr rfl
    exact ⟨(h n φ b (compose b f) hb hc).1, (h n φ b (compose b f) hb hc).2⟩
  · intro h n φ b c hb hc
    rw [(isComposedAssignment_iff hb hf).mp hc]
    exact ⟨(h n φ b hb).mp, (h n φ b hb).mpr⟩

instance piOneMembershipEmbeddingFormula_defined :
    ℒₛₑₜ-relation₃[V] IsCodedMembershipEmbedding via piOneMembershipEmbeddingFormula :=
  ⟨fun (v : Fin 3 → V) ↦ by
    have hv : ![v 0, v 1, v 2] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) k) j) i
    change piOneMembershipEmbeddingFormula.Evalb v ↔ IsCodedMembershipEmbedding (v 0) (v 1) (v 2)
    rw [← hv]
    exact eval_piOneMembershipEmbeddingFormula _ _ _⟩

end ZFVP
