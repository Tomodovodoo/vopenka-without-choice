import ZFVP.ModelTheory.ForcingAtomicSemanticConsequence
import ZFVP.ModelTheory.UsubaRestorationClosure
import ZFVP.ModelTheory.TransportedTwoStepSequence
import ZFVP.ModelTheory.QuotientClosureComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def usubaSelectedUnionName (T U o f : V) : V :=
  forcingSelectedUnion T U o (twoStepNames (usubaSaturatedPosetName T U) ∅)
    (twoStepTailSelector T U (usubaSaturatedPosetName T U) ∅) f

noncomputable def usubaLocalUnionName (T U o p f : V) : V :=
  forcingCarrierLocalNormalize T U (usubaRestorationPosetName T U) p
    (usubaSelectedUnionName T U o f)

theorem usubaSelectedUnionName_isName (T U o f : V) :
    IsForcingName T (usubaSelectedUnionName T U o f) := forcingSelectedUnion_isName _ _ _ _ _ _

theorem usubaLocalUnionName_isName (T U o p f : V) :
    IsForcingName T (usubaLocalUnionName T U o p f) := forcingCarrierLocalNormalize_isName _ _ _ _ _

theorem transported_usuba_selected_union_member [Countable V]
    {B R b T U o τ E π p q α : V} [IsOrdinal α]
    (hR : IsForcingPreorder B R) (hb : IsForcingTop B R b)
    (hU : IsForcingPreorder T U) (ho : IsForcingTop T U o)
    (hτ : IsForcingSplitProjection B R T U τ E)
    (hp : p ∈ B) (hq : q ∈ T) (hqp : ⟨q, E ‘ p⟩ₖ ∈ U)
    (f : ForcingName B)
    (hπ : π ∈ B ^ twoStepConditions T U (usubaSaturatedPosetName T U) ∅)
    (he : ∀ c ∈ twoStepConditions T U (usubaSaturatedPosetName T U) ∅,
      τ ‘ (kpair.π₁ c) = π ‘ c)
    (hf : ∀ (G : Set V) (hG : IsExternalForcingGeneric B R G), p ∈ G →
      let A : ForcingContext V := ⟨B, R, b, G, hR, hb, hG⟩
      let Q := usubaSaturatedPosetName T U
      let S := reverseInclusionOrderName T U Q
      IsForcingDescending (A.projectionQuotient (twoStepConditions T U Q ∅) π)
        (forcingSeparativeOrder (A.projectionQuotient (twoStepConditions T U Q ∅) π)
          (A.projectionQuotientOrder (twoStepConditions T U Q ∅) (twoStepOrder T U Q S ∅) π))
        (A.check α) (A.ofName f) ∧
      (∀ a ∈ A.check α,
        ⟨A.check q, (compose (A.ofName f) (A.check (twoStepProjection T U Q ∅))) ‘ a⟩ₖ ∈
          forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) ∧
      InternalDependentChoiceAt (A.check α) ∧
      IsForcingClosedThrough (A.projectionQuotient T τ)
        (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) (A.check α)) :
    q ∈ atomicMembership T U (usubaSelectedUnionName T U o (nameAction E f.val))
      (usubaRestorationPosetName T U) := by
  apply atomicMembership_of_all_generics hU ho hq
    ⟨_, usubaSelectedUnionName_isName _ _ _ _⟩
    ⟨_, usubaRestorationPosetName_isName _ _⟩
  intro H hH hqH
  let C : ForcingContext V := ⟨T, U, o, H, hU, ho, hH⟩
  let A : ForcingContext V := ⟨B, R, b, forcingProjectionGeneric B R τ H,
    hR, hb, hτ.projection.generic hR hH⟩
  have hpA : p ∈ A.G := by
    have hpH := C.generic.1.2.2.1 q hqH (E ‘ p) (function_value_mem hτ.maps hp) hqp
    have hx := hτ.projection.image_mem hR hH.1 hpH
    rwa [hτ.right_inverse p hp] at hx
  obtain ⟨hdesc, hbound, hDC, hclosed⟩ := hf A.G A.generic hpA
  let h := usubaSaturated_iterand hU ho
  have hd := A.transported_twoStep_quotient_descending_of_bound C hτ rfl h hπ he f hdesc hqH hbound
  have hdc := A.projectionInclusion_dependentChoiceAt_of_separative_closed C hτ rfl hDC hclosed
  have hαmap := A.projectionInclusion_check C hτ rfl α
  rw [hαmap] at hd hdc
  have hs := TwoStepModel.selected_tail_descending C h hd
  have hQ : C.ofName ⟨_, h.posetName⟩ = (usubaRestorationPoset : C.Model) := C.usubaSaturatedName_value
  have hS : C.ofName ⟨_, h.orderName⟩ = reverseInclusionOrder (usubaRestorationPoset : C.Model) := by
    have hv := (C.formula_truth piOneReverseInclusionOrderFormula
      ![⟨_, h.orderName⟩, ⟨_, h.posetName⟩]).mpr
      ⟨q, hqH, reverseInclusionOrderName_forces hU ho hq ⟨_, h.posetName⟩⟩
    have heq : C.ofName ⟨_, h.orderName⟩ = reverseInclusionOrder (C.ofName ⟨_, h.posetName⟩) :=
      (piOneReverseInclusionOrderFormula_defined.iff _).mp hv
    exact heq.trans (congrArg reverseInclusionOrder hQ)
  rw [hQ, hS] at hs
  have hu := C.forcingSelectedUnion_usuba_bound (fun _ hn ↦ h.name hn)
    (twoStepTailSelector_maps T U (usubaSaturatedPosetName T U) ∅)
    ⟨nameAction E f.val, nameAction_isName hτ.maps f.property⟩
    (mem_function_of_mem_function_of_subset hd.1 sep_subset) hdc hs
  change C.ofName ⟨_, usubaSelectedUnionName_isName _ _ _ _⟩ ∈ C.ofName C.usubaRestorationName
  rw [C.usubaRestorationName_value]
  exact hu.1

theorem transported_usuba_local_union_pair_mem [Countable V]
    {B R b T U o τ E π p q α : V} [IsOrdinal α]
    (hR : IsForcingPreorder B R) (hb : IsForcingTop B R b)
    (hU : IsForcingPreorder T U) (ho : IsForcingTop T U o)
    (hτ : IsForcingSplitProjection B R T U τ E)
    (hp : p ∈ B) (hq : q ∈ T) (hqp : ⟨q, E ‘ p⟩ₖ ∈ U)
    (f : ForcingName B)
    (hπ : π ∈ B ^ twoStepConditions T U (usubaSaturatedPosetName T U) ∅)
    (he : ∀ c ∈ twoStepConditions T U (usubaSaturatedPosetName T U) ∅,
      τ ‘ (kpair.π₁ c) = π ‘ c)
    (hf : ∀ (G : Set V) (hG : IsExternalForcingGeneric B R G), p ∈ G →
      let A : ForcingContext V := ⟨B, R, b, G, hR, hb, hG⟩
      let Q := usubaSaturatedPosetName T U
      let S := reverseInclusionOrderName T U Q
      IsForcingDescending (A.projectionQuotient (twoStepConditions T U Q ∅) π)
        (forcingSeparativeOrder (A.projectionQuotient (twoStepConditions T U Q ∅) π)
          (A.projectionQuotientOrder (twoStepConditions T U Q ∅) (twoStepOrder T U Q S ∅) π))
        (A.check α) (A.ofName f) ∧
      (∀ a ∈ A.check α,
        ⟨A.check q, (compose (A.ofName f) (A.check (twoStepProjection T U Q ∅))) ‘ a⟩ₖ ∈
          forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) ∧
      InternalDependentChoiceAt (A.check α) ∧
      IsForcingClosedThrough (A.projectionQuotient T τ)
        (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) (A.check α)) :
    ⟨q, usubaLocalUnionName T U o (E ‘ p) (nameAction E f.val)⟩ₖ ∈
      twoStepConditions T U (usubaSaturatedPosetName T U) ∅ := by
  exact carrierSaturated_twoStep_localNormalize hU ho (function_value_mem hτ.maps hp) hq hqp
    ⟨_, usubaRestorationPosetName_isName _ _⟩ ⟨_, usubaSelectedUnionName_isName _ _ _ _⟩
    (transported_usuba_selected_union_member hR hb hU ho hτ hp hq hqp f hπ he hf)

theorem transported_usuba_local_union_normalization [Countable V]
    {B R b T U o τ E π p q α : V} [IsOrdinal α]
    (hR : IsForcingPreorder B R) (hb : IsForcingTop B R b)
    (hU : IsForcingPreorder T U) (ho : IsForcingTop T U o)
    (hτ : IsForcingSplitProjection B R T U τ E)
    (hp : p ∈ B) (hq : q ∈ T) (hqp : ⟨q, E ‘ p⟩ₖ ∈ U)
    (f : ForcingName B)
    (hπ : π ∈ B ^ twoStepConditions T U (usubaSaturatedPosetName T U) ∅)
    (he : ∀ c ∈ twoStepConditions T U (usubaSaturatedPosetName T U) ∅,
      τ ‘ (kpair.π₁ c) = π ‘ c)
    (hf : ∀ (G : Set V) (hG : IsExternalForcingGeneric B R G), p ∈ G →
      let A : ForcingContext V := ⟨B, R, b, G, hR, hb, hG⟩
      let Q := usubaSaturatedPosetName T U
      let S := reverseInclusionOrderName T U Q
      IsForcingDescending (A.projectionQuotient (twoStepConditions T U Q ∅) π)
        (forcingSeparativeOrder (A.projectionQuotient (twoStepConditions T U Q ∅) π)
          (A.projectionQuotientOrder (twoStepConditions T U Q ∅) (twoStepOrder T U Q S ∅) π))
        (A.check α) (A.ofName f) ∧
      (∀ a ∈ A.check α,
        ⟨A.check q, (compose (A.ofName f) (A.check (twoStepProjection T U Q ∅))) ‘ a⟩ₖ ∈
          forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) ∧
      InternalDependentChoiceAt (A.check α) ∧
      IsForcingClosedThrough (A.projectionQuotient T τ)
        (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) (A.check α)) :
    q ∈ atomicEquality T U (usubaLocalUnionName T U o (E ‘ p) (nameAction E f.val))
      (usubaSelectedUnionName T U o (nameAction E f.val)) := by
  exact forcingCarrierLocalNormalize_forces_below hU ho (function_value_mem hτ.maps hp) hq hqp
    ⟨_, usubaRestorationPosetName_isName _ _⟩ ⟨_, usubaSelectedUnionName_isName _ _ _ _⟩
    (transported_usuba_selected_union_member hR hb hU ho hτ hp hq hqp f hπ he hf)

end ZFVP
