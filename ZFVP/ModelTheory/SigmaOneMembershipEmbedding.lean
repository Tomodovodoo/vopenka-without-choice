import ZFVP.ModelTheory.BoundedEmbeddingTables

/-! Complete truth tables give a Sigma-one certificate for coded elementarity. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneMembershipEmbeddingFormula : SetTheorySemisentence 3 :=
  “A B f. !boundedNonemptyFormula A ∧ !boundedNonemptyFormula B ∧
    !boundedFunctionFormula f A B ∧ ∃ F, !sigmaOneMembershipFamilyFormula F ∧
      ∃ U, !sequenceSupportFormula U ∧ A ∈ U ∧ B ∈ U ∧
        ∃ O ∈ U, !boundedOmegaFormula O ∧ ∃ T S,
          !membershipTruthTableFormula U O F A T ∧ !membershipTruthTableFormula U O F B S ∧
            !boundedEmbeddingTablesFormula U O F A B f T S”

theorem sigmaOneMembershipEmbeddingFormula_sigmaOne : IsLevyFormula .sigma 1 sigmaOneMembershipEmbeddingFormula := by
  refine .and (.bounded (boundedNonemptyFormula_bounded.subst _))
    (.and (.bounded (boundedNonemptyFormula_bounded.subst _))
      (.and (.bounded (boundedFunctionFormula_bounded.subst _)) (.exs ?_)))
  refine .and (sigmaOneMembershipFamilyFormula_sigmaOne.subst _) (.exs ?_)
  refine .and (.bounded (sequenceSupportFormula_bounded.subst _))
    (.and (.bounded (.rel _ _)) (.and (.bounded (.rel _ _)) (.boundedExs (.bvar 0) ?_)))
  exact .and (.bounded (boundedOmegaFormula_bounded.subst _)) (.exs (.exs
    (.and (.bounded (membershipTruthTableFormula_bounded.subst _))
      (.and (.bounded (membershipTruthTableFormula_bounded.subst _))
        (.bounded (boundedEmbeddingTablesFormula_bounded.subst _))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem codedMembershipEmbedding_iff_valid_satisfaction {A B f : V} :
    IsCodedMembershipEmbedding A B f ↔ IsNonempty A ∧ IsNonempty B ∧ f ∈ B ^ A ∧
      ∀ n φ b, IsMembershipFormulaCode n φ → b ∈ A ^ n →
        (MembershipSatisfies A n φ b ↔ MembershipSatisfies B n φ (compose b f)) := by
  constructor
  · intro h
    exact ⟨h.source_nonempty, h.target_nonempty, h.function, fun _ _ _ hφ hb ↦
      h.satisfies_iff hφ.context hφ.valid (by simpa using hb)⟩
  · rintro ⟨hA, hB, hf, h⟩
    refine ⟨membershipStructureCode_valid hA, membershipStructureCode_valid hB, by simpa using hf, ?_⟩
    intro n hn φ hφ b hb
    exact h n φ b ((mem_formulaSet_iff _ _ _ _).mp hφ) (by simpa using hb)

theorem eval_sigmaOneMembershipEmbeddingFormula (A B f : V) :
    sigmaOneMembershipEmbeddingFormula.Evalb ![A, B, f] ↔ IsCodedMembershipEmbedding A B f := by
  rw [codedMembershipEmbedding_iff_valid_satisfaction]
  simp [sigmaOneMembershipEmbeddingFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  intro hA hB hf
  constructor
  · rintro ⟨U, hU, hAU, hBU, _, T, hT, S, hS, he⟩
    let := hU
    have hAsub := hU.transitive A hAU
    have hBsub := hU.transitive B hBU
    exact (eval_boundedEmbeddingTablesFormula hAsub hBsub hf
      ((eval_membershipTruthTableFormula hAsub T).mp hT)
      ((eval_membershipTruthTableFormula hBsub S).mp hS)).mp he
  · intro h
    obtain ⟨U, hU, hp⟩ := sequenceSupport_containing ⟨A, B⟩ₖ
    let := hU
    obtain ⟨hAU, hBU⟩ := kpair_components_mem_transitive hp
    have hAsub := hU.transitive A hAU
    have hBsub := hU.transitive B hBU
    refine ⟨U, hU, hAU, hBU, hU.omega_mem, membershipModelTruthTable A,
      (eval_membershipTruthTableFormula hAsub _).mpr (membershipModelTruthTable_correct A),
      membershipModelTruthTable B,
      (eval_membershipTruthTableFormula hBsub _).mpr (membershipModelTruthTable_correct B), ?_⟩
    exact (eval_boundedEmbeddingTablesFormula hAsub hBsub hf
      (membershipModelTruthTable_correct A) (membershipModelTruthTable_correct B)).mpr h

instance sigmaOneMembershipEmbeddingFormula_defined :
    ℒₛₑₜ-relation₃[V] IsCodedMembershipEmbedding via sigmaOneMembershipEmbeddingFormula :=
  ⟨fun (v : Fin 3 → V) ↦ by
    have hv : ![v 0, v 1, v 2] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) k) j) i
    change sigmaOneMembershipEmbeddingFormula.Evalb v ↔ IsCodedMembershipEmbedding (v 0) (v 1) (v 2)
    rw [← hv]
    exact eval_sigmaOneMembershipEmbeddingFormula _ _ _⟩

end ZFVP
