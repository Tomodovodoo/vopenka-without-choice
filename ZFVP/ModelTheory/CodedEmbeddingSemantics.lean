import ZFVP.ModelTheory.CodedElementaryEmbedding
import ZFVP.ModelTheory.FiniteParameterElementarity

/-! Internal elementary graphs induce elementary maps on the represented external structures. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Λ : Language} {L M N f : V}

namespace IsCodedElementaryEmbedding

theorem eval_semisentence (h : IsCodedElementaryEmbedding L M N f)
    (F : ∀ {k}, Λ.Func k → V) (R : ∀ {k}, Λ.Rel k → V)
    (hF : ∀ k (s : Λ.Func k), F s ∈ functionSymbols L ∧
      (functionArities L) ‘ (F s) = (k : V))
    (hR : ∀ k (s : Λ.Rel k), R s ∈ relationSymbols L ∧
      (relationArities L) ‘ (R s) = (k : V))
    {n : ℕ} (φ : Semisentence Λ n) (b : Fin n → CodedDomain M) :
    φ.EvalAux (codedFoundationStructure h.source F R hF) Empty.elim b ↔
      φ.EvalAux (codedFoundationStructure h.target F R hF) Empty.elim (h.toFunction ∘ b) := by
  have : IsFunction f := IsFunction.of_mem h.function
  have hb := standardTuple_mem_function (fun i ↦ (b i).val) (fun i ↦ (b i).property)
  have hφ : encodeSemiformula F R Empty.elim φ ∈ formulaSet L ∅ (n : V) :=
    (mem_formulaSet_iff _ _ _ _).mpr
      (encodeSemiformula_mem_family h.source.language F R Empty.elim hF hR (by simp) φ)
  rw [← encodeSemiformula_satisfies h.source F R hF hR (Γ := (∅ : V)) (E := (∅ : V))
    Empty.elim (by simp) Empty.elim (by simp) b φ,
    h.satisfies_iff (by simp) hφ hb,
    compose_standardTuple _ f (fun i ↦ by
      simpa [domain_eq_of_mem_function h.function] using (b i).property)]
  exact encodeSemiformula_satisfies h.target F R hF hR (Γ := (∅ : V)) (E := (∅ : V))
    Empty.elim (by simp) Empty.elim (by simp) (h.toFunction ∘ b) φ

theorem eval_semiformula (h : IsCodedElementaryEmbedding L M N f)
    (F : ∀ {k}, Λ.Func k → V) (R : ∀ {k}, Λ.Rel k → V)
    (hF : ∀ k (s : Λ.Func k), F s ∈ functionSymbols L ∧
      (functionArities L) ‘ (F s) = (k : V))
    (hR : ∀ k (s : Λ.Rel k), R s ∈ relationSymbols L ∧
      (relationArities L) ‘ (R s) = (k : V))
    {ξ : Type*} {n : ℕ} (φ : Semiformula Λ ξ n)
    (b : Fin n → CodedDomain M) (a : ξ → CodedDomain M) :
    φ.EvalAux (codedFoundationStructure h.source F R hF) a b ↔
      φ.EvalAux (codedFoundationStructure h.target F R hF) (h.toFunction ∘ a) (h.toFunction ∘ b) := by
  let := codedFoundationStructure h.source F R hF
  let := codedFoundationStructure h.target F R hF
  let := codedDomain_nonempty h.source
  exact elementary_of_semisentences h.toFunction (fun ψ c ↦ h.eval_semisentence F R hF hR ψ c) φ b a

end IsCodedElementaryEmbedding

end ZFVP
