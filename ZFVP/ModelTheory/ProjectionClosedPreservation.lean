import ZFVP.ModelTheory.ProjectionFactorization
import ZFVP.ModelTheory.ForcingClosedSequences
import ZFVP.ModelTheory.ForcingDependentChoiceTransfer
import ZFVP.SetTheory.ElementaryDependentChoice
import ZFVP.ModelTheory.SeparativeModel

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext
variable (A B : ForcingContext V) {π E : V}
  (hπ : IsForcingSplitProjection A.P A.R B.P B.R π E)
  (he : forcingProjectionGeneric A.P A.R π B.G = A.G)

/-- Closed quotient forcing adds no ordinal-indexed functions into an intermediate set. -/
theorem projectionInclusion_function_of_closed {γ X : A.Model} [IsOrdinal γ]
    (hDC : InternalDependentChoiceAt γ)
    (hclosed : IsForcingClosedThrough (A.projectionQuotient B.P π)
      (A.projectionQuotientOrder B.P B.R π) γ)
    {f : B.Model}
    (hf : f ∈ A.projectionInclusion B hπ he X ^ A.projectionInclusion B hπ he γ) :
    ∃ g ∈ X ^ γ, A.projectionInclusion B hπ he g = f := by
  let C := A.projectionQuotientContext B hπ he
  let L := A.projectionQuotientRealization B hπ he
  obtain ⟨f', rfl⟩ := A.projectionQuotientRealization_surjective B hπ he f
  have hf' : f' ∈ C.check X ^ C.check γ := by
    apply (L.embedding.function_iff f' (C.check γ) (C.check X)).mp
    change L.value f' ∈ L.value (C.check X) ^ L.value (C.check γ)
    rw [L.value_check, L.value_check]
    exact hf
  obtain ⟨g, hg, heq⟩ := C.function_eq_check_of_closed hDC hclosed hf'
  refine ⟨g, hg, ?_⟩
  exact (L.value_check g).symm.trans (congrArg L.value heq)

theorem projectionInclusion_dependentChoiceAt_of_closed {γ : A.Model} [IsOrdinal γ]
    (hDC : InternalDependentChoiceAt γ)
    (hclosed : IsForcingClosedThrough (A.projectionQuotient B.P π)
      (A.projectionQuotientOrder B.P B.R π) γ) :
    InternalDependentChoiceAt (A.projectionInclusion B hπ he γ) := by
  let C := A.projectionQuotientContext B hπ he
  let j := A.projectionFactorizationElementaryMap B hπ he
  have hC := C.dependentChoiceAt_of_closed hDC hclosed
  have hB := j.dependentChoiceAt hC
  change InternalDependentChoiceAt (A.projectionFactorizationEquiv B hπ he (C.check γ)) at hB
  rwa [A.projectionFactorizationEquiv_check B hπ he] at hB

theorem projectionInclusion_function_of_separative_closed {γ X : A.Model} [IsOrdinal γ]
    (hDC : InternalDependentChoiceAt γ)
    (hclosed : IsForcingClosedThrough (A.projectionQuotient B.P π)
      (forcingSeparativeOrder (A.projectionQuotient B.P π) (A.projectionQuotientOrder B.P B.R π)) γ)
    {f : B.Model}
    (hf : f ∈ A.projectionInclusion B hπ he X ^ A.projectionInclusion B hπ he γ) :
    ∃ g ∈ X ^ γ, A.projectionInclusion B hπ he g = f := by
  let C := A.projectionQuotientContext B hπ he
  let L := A.projectionQuotientRealization B hπ he
  obtain ⟨f', rfl⟩ := A.projectionQuotientRealization_surjective B hπ he f
  have hf' : f' ∈ C.check X ^ C.check γ := by
    apply (L.embedding.function_iff f' (C.check γ) (C.check X)).mp
    change L.value f' ∈ L.value (C.check X) ^ L.value (C.check γ)
    rw [L.value_check, L.value_check]
    exact hf
  obtain ⟨g, hg, heq⟩ := C.function_eq_check_of_separative_closed hDC hclosed hf'
  exact ⟨g, hg, (L.value_check g).symm.trans (congrArg L.value heq)⟩

theorem projectionInclusion_dependentChoiceAt_of_separative_closed {γ : A.Model} [IsOrdinal γ]
    (hDC : InternalDependentChoiceAt γ)
    (hclosed : IsForcingClosedThrough (A.projectionQuotient B.P π)
      (forcingSeparativeOrder (A.projectionQuotient B.P π) (A.projectionQuotientOrder B.P B.R π)) γ) :
    InternalDependentChoiceAt (A.projectionInclusion B hπ he γ) := by
  let C := A.projectionQuotientContext B hπ he
  let j := A.projectionFactorizationElementaryMap B hπ he
  have hB := j.dependentChoiceAt (C.dependentChoiceAt_of_separative_closed hDC hclosed)
  change InternalDependentChoiceAt (A.projectionFactorizationEquiv B hπ he (C.check γ)) at hB
  exact A.projectionFactorizationEquiv_check B hπ he γ ▸ hB

end ForcingContext
end ZFVP
