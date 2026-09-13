import ZFVP.ModelTheory.CodedEmbeddingSemantics
import ZFVP.Syntax.MembershipSatisfaction
import ZFVP.SetTheory.ElementaryMap

/-! From a coded membership embedding to the external elementary map used in the set-theoretic proofs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsCodedMembershipEmbedding (A B f : V) : Prop :=
  IsCodedElementaryEmbedding membershipLanguageCode (membershipStructureCode A) (membershipStructureCode B) f

instance codedMembershipEmbedding_definable : ℒₛₑₜ-relation₃[V] IsCodedMembershipEmbedding := by
  unfold IsCodedMembershipEmbedding
  definability

namespace IsCodedMembershipEmbedding

variable {A B C f g : V}

theorem source_nonempty (h : IsCodedMembershipEmbedding A B f) : IsNonempty A := by
  simpa using h.source.domain_nonempty

theorem target_nonempty (h : IsCodedMembershipEmbedding A B f) : IsNonempty B := by
  simpa using h.target.domain_nonempty

theorem function (h : IsCodedMembershipEmbedding A B f) : f ∈ B ^ A := by
  simpa using IsCodedElementaryEmbedding.function h

noncomputable def toFunction (h : IsCodedMembershipEmbedding A B f) : SetDomain A → SetDomain B :=
  fun x ↦ ⟨f ‘ x.val, function_value_mem h.function x.property⟩

theorem eval_semisentence (h : IsCodedMembershipEmbedding A B f)
    {n : ℕ} (φ : SetTheorySemisentence n) (b : Fin n → SetDomain A) :
    φ.Evalb b ↔ φ.Evalb (h.toFunction ∘ b) := by
  have : IsFunction f := IsFunction.of_mem h.function
  have hb : standardTuple (fun i ↦ (b i).val) ∈
      structureDomain (membershipStructureCode A) ^ (n : V) := by
    simpa using standardTuple_mem_function (fun i ↦ (b i).val) (fun i ↦ (b i).property)
  rw [← satisfies_encodeMembershipFormula h.source_nonempty φ b,
    h.satisfies_iff (by simp) (encodeMembershipFormula_mem φ) hb,
    compose_standardTuple _ f (fun i ↦ by
      simpa [domain_eq_of_mem_function h.function] using (b i).property)]
  exact satisfies_encodeMembershipFormula h.target_nonempty φ (h.toFunction ∘ b)

noncomputable def toElementaryMap (h : IsCodedMembershipEmbedding A B f) :
    ElementaryMap (SetDomain A) (SetDomain B) where
  toFun := h.toFunction
  elementary φ b a := by
    let : Nonempty (SetDomain A) := by
      obtain ⟨x, hx⟩ := h.source_nonempty.nonempty
      exact ⟨⟨x, hx⟩⟩
    exact elementary_of_semisentences h.toFunction (fun ψ c ↦ h.eval_semisentence ψ c) φ b a

theorem value_mem_iff (h : IsCodedMembershipEmbedding A B f) {x y : V}
    (hx : x ∈ A) (hy : y ∈ A) : f ‘ x ∈ f ‘ y ↔ x ∈ y :=
  h.toElementaryMap.map_mem_iff ⟨x, hx⟩ ⟨y, hy⟩

theorem identity (hA : IsNonempty A) : IsCodedMembershipEmbedding A A (SetTheory.identity A) := by
  simpa [IsCodedMembershipEmbedding] using
    IsCodedElementaryEmbedding.identity (membershipStructureCode_valid hA)

theorem comp (hf : IsCodedMembershipEmbedding A B f) (hg : IsCodedMembershipEmbedding B C g) :
    IsCodedMembershipEmbedding A C (compose f g) := IsCodedElementaryEmbedding.comp hf hg

end IsCodedMembershipEmbedding

end ZFVP
