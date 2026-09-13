import ZFVP.ModelTheory.LocalUnionNormalizationForcing
import ZFVP.ModelTheory.TransportedTwoStepSequence
import ZFVP.ModelTheory.QuotientClosureComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem transported_local_union_normalization [Countable V]
    {B R b T U o τ E π δ p q α S t : V} [IsOrdinal α]
    (hR : IsForcingPreorder B R) (hb : IsForcingTop B R b)
    (hU : IsForcingPreorder T U) (ho : IsForcingTop T U o)
    (hτ : IsForcingSplitProjection B R T U τ E)
    (hδ : IsChoicelessInaccessible δ) (hT : T ∈ hierarchy δ)
    (hp : p ∈ B) (hq : q ∈ T) (hqp : ⟨q, E ‘ p⟩ₖ ∈ U)
    (Q : ForcingName T) (f : ForcingName B)
    (h : IsForcingIterand T U (forcingSaturatedName T U (forcingNameHierarchy T δ) Q.val) S t)
    (hπ : π ∈ B ^ twoStepConditions T U (forcingSaturatedName T U (forcingNameHierarchy T δ) Q.val) t)
    (he : ∀ c ∈ twoStepConditions T U (forcingSaturatedName T U (forcingNameHierarchy T δ) Q.val) t,
      τ ‘ (kpair.π₁ c) = π ‘ c)
    (hf : ∀ (G : Set V) (hG : IsExternalForcingGeneric B R G), p ∈ G →
      let A : ForcingContext V := ⟨B, R, b, G, hR, hb, hG⟩
      let Q' := forcingSaturatedName T U (forcingNameHierarchy T δ) Q.val
      IsForcingDescending (A.projectionQuotient (twoStepConditions T U Q' t) π)
        (forcingSeparativeOrder (A.projectionQuotient (twoStepConditions T U Q' t) π)
          (A.projectionQuotientOrder (twoStepConditions T U Q' t) (twoStepOrder T U Q' S t) π))
        (A.check α) (A.ofName f) ∧
      (∀ a ∈ A.check α,
        ⟨A.check q, (compose (A.ofName f) (A.check (twoStepProjection T U Q' t))) ‘ a⟩ₖ ∈
          forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) ∧
      InternalDependentChoiceAt (A.check α) ∧
      IsForcingClosedThrough (A.projectionQuotient T τ)
        (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) (A.check α))
    (hcollapse : ∀ (H : Set V) (hH : IsExternalForcingGeneric T U H), q ∈ H →
      let C : ForcingContext V := ⟨T, U, o, H, hU, ho, hH⟩
      ∃ κ : C.Model, IsRegularCardinal κ ∧ κ ⊆ C.check δ ∧ C.check α ∈ κ ∧
        C.ofName ⟨forcingSaturatedName T U (forcingNameHierarchy T δ) Q.val, h.posetName⟩ =
          woodinCollapse κ (C.check δ) ∧
        C.ofName ⟨S, h.orderName⟩ = woodinCollapseOrder κ (C.check δ)) :
    let Q' := forcingSaturatedName T U (forcingNameHierarchy T δ) Q.val
    let σ := forcingSelectedUnion T U o (twoStepNames Q' t) (twoStepTailSelector T U Q' t) (nameAction E f.val)
    q ∈ atomicEquality T U (forcingLocalCanonicalName T U o δ (E ‘ p) σ) σ := by
  dsimp only
  apply local_union_normalization_of_all_generics hU ho hδ hT (function_value_mem hτ.maps hp)
    hq hqp Q ⟨nameAction E f.val, nameAction_isName hτ.maps f.property⟩ h
  intro H hH hqH
  let C : ForcingContext V := ⟨T, U, o, H, hU, ho, hH⟩
  let A : ForcingContext V := ⟨B, R, b, forcingProjectionGeneric B R τ H, hR, hb, hτ.projection.generic hR hH⟩
  have hpA : p ∈ A.G := by
    have hpH := C.generic.1.2.2.1 q hqH (E ‘ p) (function_value_mem hτ.maps hp) hqp
    have hx := hτ.projection.image_mem hR hH.1 hpH
    rwa [hτ.right_inverse p hp] at hx
  obtain ⟨hdesc, hbound, hDC, hclosed⟩ := hf A.G A.generic hpA
  obtain ⟨κ, hκ, hκδ, hακ, hQ, hS⟩ := hcollapse H hH hqH
  have hαmap : A.projectionInclusion C hτ rfl (A.check α) = C.check α :=
    A.projectionInclusion_check C hτ rfl α
  have hd := A.transported_twoStep_quotient_descending_of_bound C hτ rfl h hπ he f hdesc hqH hbound
  have hdc := A.projectionInclusion_dependentChoiceAt_of_separative_closed C hτ rfl hDC hclosed
  rw [hαmap] at hd hdc
  exact ⟨κ, C.check α, inferInstance, hd, hκ, hκδ, hακ, hdc, hQ, hS⟩

end ZFVP
