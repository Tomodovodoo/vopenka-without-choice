import ZFVP.ModelTheory.WoodinDirectedLocalUnionBound
import ZFVP.ModelTheory.TransportedLocalUnionNormalization
import ZFVP.ModelTheory.TransportedLocalUnionPair

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem local_directed_union_pair_mem_of_all_generics [Countable V] {P R one δ p q S t : V}
    (hR : IsForcingPreorder P R) (ho : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (hp : p ∈ P) (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R)
    (Q f : ForcingName P)
    (h : IsForcingIterand P R (forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val) S t)
    (hf : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G), q ∈ G →
      let A : ForcingContext V := ⟨P, R, one, G, hR, ho, hG⟩
      let Q' := forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val
      ∃ κ α : A.Model, IsOrdinal α ∧
        IsForcingDirectedFamily
          (A.projectionQuotient (twoStepConditions P R Q' t) (twoStepProjection P R Q' t))
          (forcingSeparativeOrder
            (A.projectionQuotient (twoStepConditions P R Q' t) (twoStepProjection P R Q' t))
            (A.projectionQuotientOrder (twoStepConditions P R Q' t)
              (twoStepOrder P R Q' S t) (twoStepProjection P R Q' t))) α (A.ofName f) ∧
        IsRegularCardinal κ ∧ κ ⊆ A.check δ ∧ α ∈ κ ∧ InternalDependentChoiceAt α ∧
        A.ofName ⟨Q', h.posetName⟩ = woodinCollapse κ (A.check δ) ∧
        A.ofName ⟨S, h.orderName⟩ = woodinCollapseOrder κ (A.check δ)) :
    let Q' := forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val
    ⟨q, forcingLocalCanonicalName P R one δ p
      (forcingSelectedUnion P R one (twoStepNames Q' t) (twoStepTailSelector P R Q' t) f.val)⟩ₖ ∈
        twoStepConditions P R Q' t := by
  dsimp only
  apply saturated_twoStep_mem_of_all_generics hR ho hq
    ⟨_, forcingLocalCanonicalName_isName _ _ _ _ _ _⟩ Q
    (forcingLocalCanonicalName_mem hR ho hδ hP _ _)
  intro G hG hqG
  let A : ForcingContext V := ⟨P, R, one, G, hR, ho, hG⟩
  obtain ⟨κ, α, hαord, hdesc, hκ, hκδ, hακ, hDC, hQ, hS⟩ := hf G hG hqG
  let := hαord
  have hpG : p ∈ A.G := A.generic.1.2.2.1 q hqG p hp hqp
  exact (TwoStepModel.local_collapse_directed_union_bound A h hδ hP hpG f hdesc hκ hκδ hακ hDC hQ hS).1

end ZFVP

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TwoStepModel

theorem local_collapse_directed_union_normalization (A : ForcingContext V)
    {Q S t δ p : V} (h : IsForcingIterand A.P A.R Q S t)
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (hp : p ∈ A.G)
    (f : ForcingName A.P) {κ α : A.Model} [IsOrdinal α]
    (hf : IsForcingDirectedFamily
      (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
      (forcingSeparativeOrder
        (A.projectionQuotient (twoStepConditions A.P A.R Q t) (twoStepProjection A.P A.R Q t))
        (A.projectionQuotientOrder (twoStepConditions A.P A.R Q t)
          (twoStepOrder A.P A.R Q S t) (twoStepProjection A.P A.R Q t))) α (A.ofName f))
    (hκ : IsRegularCardinal κ) (hκδ : κ ⊆ A.check δ) (hα : α ∈ κ)
    (hDC : InternalDependentChoiceAt α)
    (hQ : A.ofName ⟨Q, h.posetName⟩ = woodinCollapse κ (A.check δ))
    (hS : A.ofName ⟨S, h.orderName⟩ = woodinCollapseOrder κ (A.check δ)) :
    let τ := forcingSelectedUnion A.P A.R A.one (twoStepNames Q t) (twoStepTailSelector A.P A.R Q t) f.val
    A.ofName ⟨forcingLocalCanonicalName A.P A.R A.one δ p τ, forcingLocalCanonicalName_isName _ _ _ _ _ _⟩ =
      A.ofName ⟨τ, forcingSelectedUnion_isName _ _ _ _ _ _⟩ := by
  have hs := selected_tail_directed A h hf
  rw [hQ, hS] at hs
  have hu := A.forcingSelectedUnion_collapse_directed_bound (fun _ hν ↦ h.name hν)
    (twoStepTailSelector_maps A.P A.R Q t) f
    (mem_function_of_mem_function_of_subset hf.1 sep_subset) hκ hα hDC hs
  have hr := woodinCollapse_condition_mem_hierarchy
    (A.check_inaccessible_of_small hδ hP).regular hκδ hu.1
  exact A.localCanonicalName_value hδ hP hp
    ⟨_, forcingSelectedUnion_isName _ _ _ _ _ _⟩ hr

end TwoStepModel
end ZFVP

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem local_directed_union_normalization_of_all_generics [Countable V] {P R one δ p q S t : V}
    (hR : IsForcingPreorder P R) (ho : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (hp : p ∈ P) (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R)
    (Q f : ForcingName P)
    (h : IsForcingIterand P R (forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val) S t)
    (hf : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G), q ∈ G →
      let A : ForcingContext V := ⟨P, R, one, G, hR, ho, hG⟩
      let Q' := forcingSaturatedName P R (forcingNameHierarchy P δ) Q.val
      ∃ κ α : A.Model, IsOrdinal α ∧
        IsForcingDirectedFamily
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
  exact TwoStepModel.local_collapse_directed_union_normalization A h hδ hP hpG f hdesc hκ hκδ hακ hDC hQ hS

end ZFVP

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem transported_local_directed_union_pair_mem [Countable V]
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
      IsForcingDirectedFamily (A.projectionQuotient (twoStepConditions T U Q' t) π)
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
    ⟨q, forcingLocalCanonicalName T U o δ (E ‘ p)
      (forcingSelectedUnion T U o (twoStepNames Q' t) (twoStepTailSelector T U Q' t)
        (nameAction E f.val))⟩ₖ ∈ twoStepConditions T U Q' t := by
  dsimp only
  apply local_directed_union_pair_mem_of_all_generics hU ho hδ hT (function_value_mem hτ.maps hp)
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
  have hd := A.transported_twoStep_quotient_directed_of_bound C hτ rfl h hπ he f hdesc hqH hbound
  have hdc := A.projectionInclusion_dependentChoiceAt_of_separative_closed C hτ rfl hDC hclosed
  rw [hαmap] at hd hdc
  exact ⟨κ, C.check α, inferInstance, hd, hκ, hκδ, hακ, hdc, hQ, hS⟩

end ZFVP

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem transported_local_directed_union_normalization [Countable V]
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
      IsForcingDirectedFamily (A.projectionQuotient (twoStepConditions T U Q' t) π)
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
  apply local_directed_union_normalization_of_all_generics hU ho hδ hT (function_value_mem hτ.maps hp)
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
  have hd := A.transported_twoStep_quotient_directed_of_bound C hτ rfl h hπ he f hdesc hqH hbound
  have hdc := A.projectionInclusion_dependentChoiceAt_of_separative_closed C hτ rfl hDC hclosed
  rw [hαmap] at hd hdc
  exact ⟨κ, C.check α, inferInstance, hd, hκ, hκδ, hακ, hdc, hQ, hS⟩

end ZFVP

