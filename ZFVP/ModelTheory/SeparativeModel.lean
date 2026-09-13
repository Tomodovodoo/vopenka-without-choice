import ZFVP.ModelTheory.SeparativeGeneric
import ZFVP.ModelTheory.ForcingRealizationGeneration
import ZFVP.ModelTheory.ForcingClosedSequences
import ZFVP.ModelTheory.ForcingDependentChoiceTransfer
import ZFVP.SetTheory.ElementaryDependentChoice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

noncomputable def separativeContext (A : ForcingContext V) : ForcingContext V where
  P := A.P
  R := forcingSeparativeOrder A.P A.R
  one := A.one
  G := A.G
  order := forcingSeparativeOrder_preorder A.order
  top := forcingSeparativeOrder_top A.order A.top
  generic := externalForcingGeneric_separative A.order A.generic

noncomputable def separativeRealization (A : ForcingContext V) :
    ForcingRealization A.separativeContext A.Model where
  ground := A.checkEmbedding
  genericSet := A.genericSet
  generic_subset := A.genericSet_subset
  generic_mem := A.check_mem_genericSet_iff

theorem separativeRealization_surjective (A : ForcingContext V) :
    Function.Surjective A.separativeRealization.value := by
  apply ForcingRealization.value_surjective_of_generators A A.separativeRealization
  · intro x
    exact ⟨A.separativeContext.check x, A.separativeRealization.value_check x⟩
  · exact ⟨A.separativeContext.genericSet, A.separativeRealization.value_genericSet⟩

noncomputable def separativeEquiv (A : ForcingContext V) : A.separativeContext.Model ≃ A.Model :=
  Equiv.ofBijective A.separativeRealization.value
    ⟨A.separativeRealization.embedding.injective, A.separativeRealization_surjective⟩

theorem separativeEquiv_mem_iff (A : ForcingContext V) (x y : A.separativeContext.Model) :
    A.separativeEquiv x ∈ A.separativeEquiv y ↔ x ∈ y := A.separativeRealization.value_mem_iff x y

theorem separativeEquiv_check (A : ForcingContext V) (x : V) :
    A.separativeEquiv (A.separativeContext.check x) = A.check x := A.separativeRealization.value_check x

noncomputable def separativeElementaryMap (A : ForcingContext V) :
    ElementaryMap A.separativeContext.Model A.Model :=
  ElementaryMap.ofMembershipIso A.separativeEquiv A.separativeEquiv_mem_iff

theorem function_eq_check_of_separative_closed (A : ForcingContext V) {γ X : V} [IsOrdinal γ]
    (hDC : InternalDependentChoiceAt γ)
    (hclosed : IsForcingClosedThrough A.P (forcingSeparativeOrder A.P A.R) γ)
    {f : A.Model} (hf : f ∈ A.check X ^ A.check γ) : ∃ g ∈ X ^ γ, A.check g = f := by
  obtain ⟨f', rfl⟩ := A.separativeRealization_surjective f
  have hf' : f' ∈ A.separativeContext.check X ^ A.separativeContext.check γ := by
    apply (A.separativeRealization.embedding.function_iff f' (A.separativeContext.check γ)
      (A.separativeContext.check X)).mp
    change A.separativeRealization.value f' ∈
      A.separativeRealization.value (A.separativeContext.check X) ^
        A.separativeRealization.value (A.separativeContext.check γ)
    rw [A.separativeRealization.value_check, A.separativeRealization.value_check]
    exact hf
  obtain ⟨g, hg, he⟩ := A.separativeContext.function_eq_check_of_closed hDC hclosed hf'
  exact ⟨g, hg, (A.separativeRealization.value_check g).symm.trans (congrArg A.separativeRealization.value he)⟩

theorem dependentChoiceAt_of_separative_closed (A : ForcingContext V) {γ : V} [IsOrdinal γ]
    (hDC : InternalDependentChoiceAt γ)
    (hclosed : IsForcingClosedThrough A.P (forcingSeparativeOrder A.P A.R) γ) :
    InternalDependentChoiceAt (A.check γ) := by
  have h := A.separativeElementaryMap.dependentChoiceAt
    (A.separativeContext.dependentChoiceAt_of_closed hDC hclosed)
  change InternalDependentChoiceAt (A.separativeEquiv (A.separativeContext.check γ)) at h
  exact A.separativeEquiv_check γ ▸ h

end ForcingContext
end ZFVP
