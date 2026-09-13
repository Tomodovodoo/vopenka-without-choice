import ZFVP.ModelTheory.LocalUnionNormalization
import ZFVP.ModelTheory.LocalUnionPairMembership

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem local_union_normalization_of_all_generics [Countable V] {P R one δ p q S t : V}
    (hR : IsForcingPreorder P R) (ho : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (hp : p ∈ P) (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R)
    (Q f : ForcingName P)
    (h : IsForcingIterand P R (forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val) S t)
    (hf : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G), q ∈ G →
      let A : ForcingContext V := ⟨P, R, one, G, hR, ho, hG⟩
      let Q' := forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val
      ∃ κ α : A.Model, IsOrdinal α ∧
        IsForcingDescending
          (A.projectionQuotient (twoStepConditions P R Q' t) (twoStepProjection P R Q' t))
          (forcingSeparativeOrder
            (A.projectionQuotient (twoStepConditions P R Q' t) (twoStepProjection P R Q' t))
            (A.projectionQuotientOrder (twoStepConditions P R Q' t)
              (twoStepOrder P R Q' S t) (twoStepProjection P R Q' t))) α (A.ofName f) ∧
        IsRegularCardinal κ ∧ κ ⊆ A.check δ ∧ α ∈ κ ∧ InternalDependentChoiceAt α ∧
        A.ofName ⟨Q', h.posetName⟩ = woodinCollapse κ (A.check δ) ∧
        A.ofName ⟨S, h.orderName⟩ = woodinCollapseOrder κ (A.check δ)) :
    let Q' := forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val
    let τ := forcingSelectedUnion P R one (twoStepNames Q' t) (twoStepTailSelector P R Q' t) f.val
    q ∈ atomicEquality P R (forcingLocalCanonicalName P R one δ p τ) τ := by
  dsimp only
  apply atomicEquality_of_all_generics hR ho hq
    ⟨_, forcingLocalCanonicalName_isName _ _ _ _ _ _⟩
    ⟨_, forcingSelectedUnion_isName _ _ _ _ _ _⟩
  intro G hG hqG
  let A : ForcingContext V := ⟨P, R, one, G, hR, ho, hG⟩
  obtain ⟨κ, α, hαord, hdesc, hκ, hκδ, hακ, hDC, hQ, hS⟩ := hf G hG hqG
  let := hαord
  have hpG : p ∈ A.G := A.generic.1.2.2.1 q hqG p hp hqp
  exact TwoStepModel.local_collapse_union_normalization A h hδ hP hpG f hdesc hκ hκδ hακ hDC hQ hS

end ZFVP
