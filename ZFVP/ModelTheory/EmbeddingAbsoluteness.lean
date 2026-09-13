import ZFVP.ModelTheory.PiOneMembershipEmbedding
import ZFVP.SetTheory.CnAbsoluteness

/-! Downward truth and C(n)-rank absoluteness of the coded membership embedding dictionary. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem codedMembershipEmbedding_downward (U : V) [IsTransitive U]
    (A B f : SetDomain U) (h : IsCodedMembershipEmbedding A.val B.val f.val) :
    piOneMembershipEmbeddingFormula.Evalb ![A, B, f] := by
  apply pi_one_downward U piOneMembershipEmbeddingFormula_piOne ![A, B, f]
  exact (Defined.eval_iff _).mpr h

theorem Cn.membershipEmbedding_absolute {k : ℕ} {δ : V} (hδ : Cn (k + 1) δ)
    (A B f : SetDomain (hierarchy δ)) :
    piOneMembershipEmbeddingFormula.Evalb ![A, B, f] ↔ IsCodedMembershipEmbedding A.val B.val f.val :=
  hδ.defined_correct (piOneMembershipEmbeddingFormula_piOne.mono (by omega))
    (fun v ↦ IsCodedMembershipEmbedding (v 0) (v 1) (v 2)) ![A, B, f]

theorem rankElementaryMap_preserves_codedEmbedding {k l : ℕ} {δ ε : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε)
    (j : ElementaryMap (SetDomain (hierarchy δ)) (SetDomain (hierarchy ε)))
    (A B f : SetDomain (hierarchy δ)) :
    IsCodedMembershipEmbedding (j A).val (j B).val (j f).val ↔
      IsCodedMembershipEmbedding A.val B.val f.val := by
  rw [← hε.membershipEmbedding_absolute, ← hδ.membershipEmbedding_absolute]
  have he := j.elementary piOneMembershipEmbeddingFormula ![A, B, f] Empty.elim
  have hb : j ∘ ![A, B, f] = ![j A, j B, j f] := by
    funext i
    exact Fin.cases rfl (fun s ↦ Fin.cases rfl (fun t ↦ Fin.cases rfl (fun u ↦ Fin.elim0 u) t) s) i
  have hf : j ∘ (Empty.elim : Empty → SetDomain (hierarchy δ)) = Empty.elim := by
    funext i
    exact Empty.elim i
  rw [hb, hf] at he
  exact he.symm

end ZFVP
