import ZFVP.Syntax.UniformSatisfaction
import ZFVP.Syntax.FoundationEquality
import ZFVP.SetTheory.CompositionLaws
import ZFVP.ModelTheory.FormulaNesting
import ZFVP.Syntax.StandardEquality

/-! Elementary embeddings as internal set graphs, with all internally finite formulas. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsCodedElementaryEmbedding (L M N f : V) : Prop :=
  IsStructureCode L M ∧ IsStructureCode L N ∧ f ∈ structureDomain N ^ structureDomain M ∧
    ∀ n ∈ (ω : V), ∀ φ ∈ formulaSet L ∅ n, ∀ b ∈ structureDomain M ^ n,
      (Satisfies L ∅ M ∅ n φ b ↔ Satisfies L ∅ N ∅ n φ (compose b f))

def codedElementaryEmbeddingFormula : SetTheorySemisentence 4 :=
  f“L M N f. !isStructureCodeFormula L M ∧ !isStructureCodeFormula L N ∧
    f ∈ !function.dfn (!structureDomainFormula N) (!structureDomainFormula M) ∧
    ∀ n ∈ !isω, ∀ φ ∈ !formulaSetFormula L (!isEmpty) n,
    ∀ b ∈ !function.dfn (!structureDomainFormula M) n,
      (!satisfiesFormula L (!isEmpty) M (!isEmpty) n φ b ↔
       !satisfiesFormula L (!isEmpty) N (!isEmpty) n φ (!composeFormula b f))”

instance codedElementaryEmbeddingFormula_defined :
    ℒₛₑₜ-relation₄[V] IsCodedElementaryEmbedding via codedElementaryEmbeddingFormula :=
  ⟨fun v ↦ by simp [codedElementaryEmbeddingFormula, IsCodedElementaryEmbedding]⟩

instance codedElementaryEmbedding_definable : ℒₛₑₜ-relation₄[V] IsCodedElementaryEmbedding :=
  codedElementaryEmbeddingFormula_defined.to_definable

namespace IsCodedElementaryEmbedding

variable {L M N P f g : V}

theorem source (h : IsCodedElementaryEmbedding L M N f) : IsStructureCode L M := h.1

theorem target (h : IsCodedElementaryEmbedding L M N f) : IsStructureCode L N := h.2.1

theorem function (h : IsCodedElementaryEmbedding L M N f) :
    f ∈ structureDomain N ^ structureDomain M := h.2.2.1

theorem satisfies_iff (h : IsCodedElementaryEmbedding L M N f)
    {n φ b : V} (hn : n ∈ (ω : V)) (hφ : φ ∈ formulaSet L ∅ n)
    (hb : b ∈ structureDomain M ^ n) :
    Satisfies L ∅ M ∅ n φ b ↔ Satisfies L ∅ N ∅ n φ (compose b f) :=
  h.2.2.2 n hn φ hφ b hb

theorem identity (hM : IsStructureCode L M) :
    IsCodedElementaryEmbedding L M M (SetTheory.identity (structureDomain M)) := by
  refine ⟨hM, hM, identity_mem_function _, ?_⟩
  intro n hn φ hφ b hb
  rw [graph_compose_identity hb]

theorem comp (hf : IsCodedElementaryEmbedding L M N f)
    (hg : IsCodedElementaryEmbedding L N P g) :
    IsCodedElementaryEmbedding L M P (compose f g) := by
  refine ⟨hf.source, hg.target, compose_function hf.function hg.function, ?_⟩
  intro n hn φ hφ b hb
  rw [hf.satisfies_iff hn hφ hb, hg.satisfies_iff hn hφ (compose_function hb hf.function),
    graph_compose_assoc]

noncomputable def toFunction (h : IsCodedElementaryEmbedding L M N f) : CodedDomain M → CodedDomain N :=
  fun x ↦ ⟨f ‘ x.val, function_value_mem h.function x.property⟩

theorem value_injective (h : IsCodedElementaryEmbedding L M N f)
    {x y : V} (hx : x ∈ structureDomain M) (hy : y ∈ structureDomain M)
    (heq : f ‘ x = f ‘ y) : x = y := by
  have : IsFunction f := IsFunction.of_mem h.function
  have hb : standardTuple ![x, y] ∈ structureDomain M ^ (2 : V) :=
    standardTuple_mem_function _ (by simp [hx, hy])
  have ht := h.satisfies_iff (by simp) (standardEqualityCode_mem h.source.language ∅) hb
  rw [satisfies_standardEqualityCode h.source hb,
    satisfies_standardEqualityCode h.target (compose_function hb h.function)] at ht
  rw [compose_standardTuple _ f (by simp [domain_eq_of_mem_function h.function, hx, hy])] at ht
  have he : (standardTuple (fun i ↦ f ‘ (![x, y] i))) ‘ (0 : V) = f ‘ x ∧
      (standardTuple (fun i ↦ f ‘ (![x, y] i))) ‘ (1 : V) = f ‘ y :=
    ⟨value_standardTuple _ 0, value_standardTuple _ 1⟩
  rw [(standardTuple_equality_values x y).1, (standardTuple_equality_values x y).2,
    he.1, he.2] at ht
  exact ht.mpr heq

theorem injective (h : IsCodedElementaryEmbedding L M N f) : Injective f := by
  have : IsFunction f := IsFunction.of_mem h.function
  intro x y z hxz hyz
  exact h.value_injective (mem_of_mem_functions h.function hxz).1
    (mem_of_mem_functions h.function hyz).1
    ((value_eq_of_kpair_mem hxz).trans (value_eq_of_kpair_mem hyz).symm)

theorem toFunction_injective (h : IsCodedElementaryEmbedding L M N f) :
    Function.Injective h.toFunction := by
  intro x y heq
  apply Subtype.ext
  exact h.value_injective x.property y.property (congrArg Subtype.val heq)

end IsCodedElementaryEmbedding

end ZFVP
