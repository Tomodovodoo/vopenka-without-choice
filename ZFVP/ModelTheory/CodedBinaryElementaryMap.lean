import ZFVP.ModelTheory.CodedEmbeddingSemantics
import ZFVP.Syntax.BinaryRelationSatisfaction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {D E B R f : V}

noncomputable def IsCodedElementaryEmbedding.binaryElementaryMap
    (h : IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode D E)
      (binaryRelationStructureCode B R) f) :
    ElementaryMap (BinaryRelationDomain D E) (BinaryRelationDomain B R) where
  toFun := codedBinaryRelationEquiv B R ∘ h.toFunction ∘ (codedBinaryRelationEquiv D E).symm
  elementary {ξ n} φ b a := by
    have hD : IsNonempty D := by simpa using h.source.domain_nonempty
    have hB : IsNonempty B := by simpa using h.target.domain_nonempty
    let b' := (codedBinaryRelationEquiv D E).symm ∘ b
    let a' := (codedBinaryRelationEquiv D E).symm ∘ a
    have h₀ := binaryRelationStructure_eval hD φ a' b'
    have h₁ := h.eval_semiformula
      (fun {k} ↦ membershipFunctionSymbol (V := V) (k := k)) membershipSymbol
      (fun _ s ↦ membershipFunctionSymbol_valid s) (fun _ s ↦ membershipSymbol_valid s) φ b' a'
    have h₂ := binaryRelationStructure_eval hB φ (h.toFunction ∘ a') (h.toFunction ∘ b')
    have h₀' : φ.EvalAux (codedFoundationStructure h.source
        (fun {k} ↦ membershipFunctionSymbol (V := V) (k := k)) membershipSymbol
        (fun _ s ↦ membershipFunctionSymbol_valid s)) a' b' ↔ φ.Eval b a := by
      simpa only [a', b', Function.comp_def, Equiv.apply_symm_apply] using h₀
    exact h₀'.symm.trans (h₁.trans h₂)

@[simp] theorem IsCodedElementaryEmbedding.binaryElementaryMap_val
    (h : IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode D E)
      (binaryRelationStructureCode B R) f) (x : BinaryRelationDomain D E) :
    (h.binaryElementaryMap x).val = f ‘ x.val := rfl

end ZFVP
