import ZFVP.ModelTheory.TwoStepEquivalence
import ZFVP.ModelTheory.ForcingGenericInclusion
import ZFVP.ModelTheory.ForcingRetractionSequences

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def MembershipEndExtension.comp {U V W : Type*}
    [SetStructure U] [SetStructure V] [SetStructure W]
    (k : MembershipEndExtension V W) (j : MembershipEndExtension U V) :
    MembershipEndExtension U W where
  toFun := fun x ↦ k (j x)
  injective := k.injective.comp j.injective
  mem_iff := fun x y ↦ (k.mem_iff _ _).trans (j.mem_iff x y)
  endExtension := by
    intro x y hy
    obtain ⟨z, hz, rfl⟩ := k.endExtension (j x) y hy
    obtain ⟨a, ha, rfl⟩ := j.endExtension x z hz
    exact ⟨a, ha, rfl⟩

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TwoStepModel
variable (A : ForcingContext V) {Q S t Q' S' t' : V}
  (h : IsForcingIterand A.P A.R Q S t) (h' : IsForcingIterand A.P A.R Q' S' t')
  {H H' : Set A.Model}
  (hH : IsExternalForcingGeneric (A.ofName ⟨Q, h.posetName⟩) (A.ofName ⟨S, h.orderName⟩) H)
  (hH' : IsExternalForcingGeneric (A.ofName ⟨Q', h'.posetName⟩) (A.ofName ⟨S', h'.orderName⟩) H')
  (hG : ∀ p, p ∈ (combinedContext A h hH).G ↔
    p ∈ (combinedContext A h' hH').G ∧ p ∈ (combinedContext A h hH).P)

theorem inclusion_commutes
    (j : MembershipEndExtension (iterandContext A h hH).Model (iterandContext A h' hH').Model)
    (hj : ∀ x : A.Model, j ((iterandContext A h hH).check x) =
      (iterandContext A h' hH').check x)
    (x : (combinedContext A h hH).Model) :
    combinedEmbedding A h' hH' ((combinedContext A h hH).genericInclusion
      (combinedContext A h' hH') hG x) = j (combinedEmbedding A h hH x) := by
  apply (combinedContext A h hH).endExtension_ext
    ((combinedEmbedding A h' hH').comp ((combinedContext A h hH).genericInclusion
      (combinedContext A h' hH') hG)) (j.comp (combinedEmbedding A h hH))
  intro a
  change combinedEquiv A h' hH' ((combinedContext A h hH).genericInclusion
    (combinedContext A h' hH') hG ((combinedContext A h hH).check a)) =
      j (combinedEquiv A h hH ((combinedContext A h hH).check a))
  rw [ForcingContext.genericInclusion_check, combinedEquiv_check, combinedEquiv_check, hj]

theorem inclusion_function_of_tail_closed {π : A.Model}
    (hπ : IsForcingRetraction (iterandContext A h hH).P (iterandContext A h hH).R
      (iterandContext A h' hH').P (iterandContext A h' hH').R π)
    (hTail : ∀ p, p ∈ H ↔ p ∈ H' ∧ p ∈ (iterandContext A h hH).P)
    (hone : (iterandContext A h hH).one = (iterandContext A h' hH').one)
    {γ : V} (hγ : IsOrdinal (A.check γ)) (hDC : InternalDependentChoiceAt (A.check γ))
    (hclosed : ∀ α, IsOrdinal α → α ⊆ A.check γ →
      IsForcingClosedAt (iterandContext A h' hH').P (iterandContext A h' hH').R α)
    {X : (combinedContext A h hH).Model} {f : (combinedContext A h' hH').Model}
    (hf : f ∈ (combinedContext A h hH).genericInclusion (combinedContext A h' hH') hG X ^
      (combinedContext A h' hH').check γ) :
    ∃ g ∈ X ^ (combinedContext A h hH).check γ,
      (combinedContext A h hH).genericInclusion (combinedContext A h' hH') hG g = f := by
  let C := combinedContext A h hH
  let D := combinedContext A h' hH'
  let T := iterandContext A h hH
  let U := iterandContext A h' hH'
  let j := T.retractionEmbedding U hπ hTail
  have hj : ∀ x : A.Model, j (T.check x) = U.check x :=
    T.retractionInclusion_check U hπ hTail hone
  have hc := inclusion_commutes A h h' hH hH' hG j hj
  have hf' := ((combinedEmbedding A h' hH').function_iff f (D.check γ)
    (C.genericInclusion D hG X)).mpr hf
  change combinedEmbedding A h' hH' f ∈ _ ^ combinedEquiv A h' hH' (D.check γ) at hf'
  rw [hc X, combinedEquiv_check] at hf'
  let := hγ
  obtain ⟨g, hg, he⟩ := T.retractionInclusion_function_of_closed U hπ hTail hone hDC hclosed hf'
  obtain ⟨u, rfl⟩ := combinedEmbedding_surjective A h hH g
  refine ⟨u, ?_, (combinedEmbedding A h' hH').injective ((hc u).trans he)⟩
  apply ((combinedEmbedding A h hH).function_iff u (C.check γ) X).mp
  change combinedEmbedding A h hH u ∈ combinedEmbedding A h hH X ^
    combinedEquiv A h hH (C.check γ)
  rw [combinedEquiv_check]
  exact hg

end TwoStepModel
end ZFVP
