import ZFVP.ModelTheory.CodedMembershipEmbedding
import ZFVP.SetTheory.UniformLowTruth
import ZFVP.Syntax.UniformSyntaxTransport

/-! Fixed formulas and elementary transport for coded embedding predicates. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def codedMembershipEmbeddingFormula : SetTheorySemisentence 3 :=
  f“A B f. !codedElementaryEmbeddingFormula (!membershipLanguageCodeFormula)
    (!membershipStructureCodeFormula A) (!membershipStructureCodeFormula B) f”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance codedMembershipEmbeddingFormula_defined :
    ℒₛₑₜ-relation₃[V] IsCodedMembershipEmbedding via codedMembershipEmbeddingFormula :=
  ⟨fun v ↦ by simp [codedMembershipEmbeddingFormula, IsCodedMembershipEmbedding]⟩

namespace ElementaryMap

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_codedElementaryEmbedding_iff (j : ElementaryMap V W) (L M N f : V) :
    IsCodedElementaryEmbedding (j L) (j M) (j N) (j f) ↔ IsCodedElementaryEmbedding L M N f :=
  (j.map_defined codedElementaryEmbeddingFormula
    (fun v ↦ IsCodedElementaryEmbedding (v 0) (v 1) (v 2) (v 3))
    (fun v ↦ IsCodedElementaryEmbedding (v 0) (v 1) (v 2) (v 3)) ![L, M, N, f]).symm

theorem map_codedMembershipEmbedding_iff (j : ElementaryMap V W) (A B f : V) :
    IsCodedMembershipEmbedding (j A) (j B) (j f) ↔ IsCodedMembershipEmbedding A B f :=
  (j.map_defined codedMembershipEmbeddingFormula
    (fun v ↦ IsCodedMembershipEmbedding (v 0) (v 1) (v 2))
    (fun v ↦ IsCodedMembershipEmbedding (v 0) (v 1) (v 2)) ![A, B, f]).symm

end ElementaryMap

end ZFVP
