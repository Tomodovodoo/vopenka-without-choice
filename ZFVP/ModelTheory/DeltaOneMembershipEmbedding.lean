import ZFVP.ModelTheory.SigmaOneMembershipEmbedding
import ZFVP.ModelTheory.EmbeddingAbsoluteness

/-! Delta-one recognition and transitive-model absoluteness of membership embedding graphs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem codedMembershipEmbedding_deltaOne :
    IsSigmaFormula 1 sigmaOneMembershipEmbeddingFormula ∧ IsPiFormula 1 piOneMembershipEmbeddingFormula ∧
      ∀ A B f : V, (sigmaOneMembershipEmbeddingFormula.Evalb ![A, B, f] ↔ IsCodedMembershipEmbedding A B f) ∧
        (piOneMembershipEmbeddingFormula.Evalb ![A, B, f] ↔ IsCodedMembershipEmbedding A B f) :=
  ⟨sigmaOneMembershipEmbeddingFormula_sigmaOne, piOneMembershipEmbeddingFormula_piOne,
    fun A B f ↦ ⟨eval_sigmaOneMembershipEmbeddingFormula A B f, eval_piOneMembershipEmbeddingFormula A B f⟩⟩

theorem Cn.membershipEmbedding_sigma_absolute {k : ℕ} {δ : V} (hδ : Cn (k + 1) δ)
    (A B f : SetDomain (hierarchy δ)) :
    sigmaOneMembershipEmbeddingFormula.Evalb ![A, B, f] ↔ IsCodedMembershipEmbedding A.val B.val f.val :=
  hδ.defined_correct (sigmaOneMembershipEmbeddingFormula_sigmaOne.mono (by omega))
    (fun v ↦ IsCodedMembershipEmbedding (v 0) (v 1) (v 2)) ![A, B, f]

theorem codedMembershipEmbedding_transitive_absolute (U : V) [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (A B f : SetDomain U) :
    IsCodedMembershipEmbedding A B f ↔ IsCodedMembershipEmbedding A.val B.val f.val := by
  constructor
  · intro h
    have hs := (eval_sigmaOneMembershipEmbeddingFormula A B f).mpr h
    have he := sigma_one_upward U sigmaOneMembershipEmbeddingFormula_sigmaOne ![A, B, f] hs
    exact (Defined.eval_iff _).mp he
  · intro h
    exact (eval_piOneMembershipEmbeddingFormula A B f).mp (codedMembershipEmbedding_downward U A B f h)

end ZFVP
