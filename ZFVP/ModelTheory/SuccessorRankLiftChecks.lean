import ZFVP.ModelTheory.SuccessorRankLiftGraph
import ZFVP.SetTheory.CnSigmaClosure

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem successorRankEmbedding_value_checkName {δ ε e one x : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) e)
    (hone : one ∈ hierarchy δ) (hx : x ∈ hierarchy δ) :
    e ‘ (checkName one x) = checkName (e ‘ one) (e ‘ x) := by
  have he := successorRankEmbedding_pi_iff hδ hε h piOneCheckNameFormula_piOne ![one, x, checkName one x]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hone, hx, hδ.checkName_closed hone hx])
  have hs := (eval_piOneCheckNameFormula one x (checkName one x)).mpr rfl
  have ht := he.mp hs
  have hv : (fun i ↦ e ‘ (![one, x, checkName one x] i)) = ![e ‘ one, e ‘ x, e ‘ (checkName one x)] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) k) j) i
  rw [hv] at ht
  exact (eval_piOneCheckNameFormula _ _ _).mp ht

namespace SuccessorRankLiftData

variable {A B : ForcingContext V} {δ ε e π : V} (L : SuccessorRankLiftData A B δ ε e)
  (hπ : IsForcingRetraction A.P A.R B.P B.R π)
  (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P)

include L

theorem one_mem_source : A.one ∈ hierarchy δ := by
  let := L.source_correct.ordinal
  exact (hierarchy_transitive δ).mem_trans A.top.1 L.poset_mem

theorem checkName_mem_source {x : V} (hx : x ∈ hierarchy δ) : checkName A.one x ∈ hierarchy δ :=
  L.source_correct.checkName_closed L.one_mem_source hx

theorem check_mem_graph_domain (hone : A.one = B.one) {x : V} (hx : x ∈ hierarchy δ) :
    B.check x ∈ domain (L.graph hπ) := by
  apply (L.graph_domain hπ _).mpr
  refine ⟨⟨checkName A.one x, checkName_isName A.top.1 x⟩, L.checkName_mem_source hx, ?_⟩
  change B.ofName ⟨checkName B.one x, _⟩ = B.ofName ⟨checkName A.one x, _⟩
  congr 1
  exact Subtype.ext (congrArg (fun one ↦ checkName one x) hone.symm)

include hG in
theorem graph_check (hone : A.one = B.one) (heone : e ‘ A.one = B.one)
    {x : V} (hx : x ∈ hierarchy δ) : (L.graph hπ) ‘ (B.check x) = B.check (e ‘ x) := by
  let τ : ForcingName A.P := ⟨checkName A.one x, checkName_isName A.top.1 x⟩
  have ht : B.ofName ⟨τ.val, τ.property.mono hπ.inclusion⟩ = B.check x := by
    change B.ofName ⟨checkName A.one x, _⟩ = B.ofName ⟨checkName B.one x, _⟩
    congr 1
    exact Subtype.ext (congrArg (fun one ↦ checkName one x) hone)
  rw [← ht, L.graph_value hπ hG τ (L.checkName_mem_source hx)]
  change B.ofName ⟨e ‘ (checkName A.one x), _⟩ = B.ofName ⟨checkName B.one (e ‘ x), _⟩
  congr 1
  apply Subtype.ext
  change e ‘ (checkName A.one x) = checkName B.one (e ‘ x)
  rw [successorRankEmbedding_value_checkName L.source_correct L.target_correct L.embedding
    L.one_mem_source hx, heone]

end SuccessorRankLiftData
end ZFVP
