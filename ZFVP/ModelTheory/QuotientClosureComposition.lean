import ZFVP.ModelTheory.ProjectionClosureComposition
import ZFVP.ModelTheory.ProjectionQuotientReconstruction
import ZFVP.ModelTheory.ForcingContextCongruence
import ZFVP.ModelTheory.ForcingCheckedTruth
import ZFVP.ModelTheory.TwoStepCollapseQuotient
import ZFVP.ModelTheory.ProjectionClosedPreservation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem quotient_separative_closedAt_comp_countable [Countable V]
    (A : ForcingContext V) {Q S T U o π τ ρ E : V}
    (hτ : IsForcingSplitProjection A.P A.R T U τ E)
    (hU : IsForcingPreorder T U) (ho : IsForcingTop T U o) (hS : IsForcingPreorder Q S)
    (hπ : π ∈ A.P ^ Q) (hρ : IsForcingProjection T U Q S ρ)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q)
    (γ : A.Model) [IsOrdinal γ]
    (hbase : IsForcingClosedAt (A.projectionQuotient T τ)
      (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) γ)
    (htail : ∀ (H : Set V) (hH : IsExternalForcingGeneric T U H)
      (hA : forcingProjectionGeneric A.P A.R τ H = A.G),
      let C : ForcingContext V := ⟨T, U, o, H, hU, ho, hH⟩
      IsForcingClosedAt (C.projectionQuotient Q ρ)
        (forcingSeparativeOrder (C.projectionQuotient Q ρ) (C.projectionQuotientOrder Q S ρ))
        (A.projectionInclusion C hτ hA γ)) :
    IsForcingClosedAt (A.projectionQuotient Q π)
      (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) γ := by
  have ht : IsForcingTop T U (E ‘ A.one) :=
    ⟨function_value_mem hτ.maps A.top.1, fun q hq ↦
      (hτ.below q hq A.one A.top.1).mpr (A.top.2 _ (function_value_mem hτ.projection.maps hq))⟩
  have htop := A.projectionQuotient_top hτ.projection.maps ht (hτ.right_inverse A.one A.top.1)
  have hR := A.projectionQuotient_preorder hτ.projection.maps hU
  apply projection_separative_closedAt_countable hR htop
    (A.projectionQuotient_projection hπ hτ.projection.maps hρ he)
    (A.projectionQuotient_preorder hπ hS) hbase
  intro H hH
  let B : ForcingContext A.Model := ⟨_, _, _, H, hR, htop, hH⟩
  let C := A.projectionCombinedContext hτ.projection hU ho hH
  have hA : forcingProjectionGeneric A.P A.R τ C.G = A.G :=
    A.projectionCombined_projection hτ.projection hH
  have hB : B = A.projectionQuotientContext C hτ hA :=
    B.eq_of_data_eq _ rfl rfl rfl (A.projectionCombined_quotientFilter hτ.projection.maps hH.1).symm
  have hc := htail C.G C.generic hA
  have hb := (A.double_projectionQuotient_separative_closedAt_iff C hτ hA hπ hρ.maps he γ).mpr hc
  change IsForcingClosedAt (B.projectionQuotient _ _)
    (forcingSeparativeOrder (B.projectionQuotient _ _) (B.projectionQuotientOrder _ _ _)) (B.check γ)
  let transfer (D : ForcingContext A.Model) : Prop :=
    IsForcingClosedAt (D.projectionQuotient (A.projectionQuotient Q π) (A.projectionQuotientMap Q π ρ))
      (forcingSeparativeOrder
        (D.projectionQuotient (A.projectionQuotient Q π) (A.projectionQuotientMap Q π ρ))
        (D.projectionQuotientOrder (A.projectionQuotient Q π)
          (A.projectionQuotientOrder Q S π) (A.projectionQuotientMap Q π ρ))) (D.check γ)
  exact (congrArg transfer hB).mpr hb

theorem quotient_separative_closedBelow_comp_countable [Countable V]
    (A : ForcingContext V) {Q S T U o π τ ρ E : V}
    (hτ : IsForcingSplitProjection A.P A.R T U τ E)
    (hU : IsForcingPreorder T U) (ho : IsForcingTop T U o) (hS : IsForcingPreorder Q S)
    (hπ : π ∈ A.P ^ Q) (hρ : IsForcingProjection T U Q S ρ)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q)
    (κ : A.Model) [IsOrdinal κ]
    (hbase : IsForcingClosedBelow (A.projectionQuotient T τ)
      (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) κ)
    (htail : ∀ (H : Set V) (hH : IsExternalForcingGeneric T U H)
      (hA : forcingProjectionGeneric A.P A.R τ H = A.G),
      let C : ForcingContext V := ⟨T, U, o, H, hU, ho, hH⟩
      IsForcingClosedBelow (C.projectionQuotient Q ρ)
        (forcingSeparativeOrder (C.projectionQuotient Q ρ) (C.projectionQuotientOrder Q S ρ))
        (A.projectionInclusion C hτ hA κ)) :
    IsForcingClosedBelow (A.projectionQuotient Q π)
      (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) κ := by
  intro γ hγ
  let := IsOrdinal.of_mem hγ
  apply A.quotient_separative_closedAt_comp_countable hτ hU ho hS hπ hρ he γ (hbase γ hγ)
  intro H hH hA
  let C : ForcingContext V := ⟨T, U, o, H, hU, ho, hH⟩
  exact htail H hH hA _ ((A.projectionInclusion C hτ hA).mem_iff γ κ |>.mpr hγ)

theorem twoStep_collapse_quotient_comp_closedAt_countable [Countable V]
    (A : ForcingContext V) {T U o τ E Q S t π : V}
    (hτ : IsForcingSplitProjection A.P A.R T U τ E)
    (hU : IsForcingPreorder T U) (ho : IsForcingTop T U o) (h : IsForcingIterand T U Q S t)
    (hπ : π ∈ A.P ^ twoStepConditions T U Q t)
    (he : ∀ q ∈ twoStepConditions T U Q t,
      τ ‘ ((twoStepProjection T U Q t) ‘ q) = π ‘ q)
    (γ : A.Model) [IsOrdinal γ] (hDC : InternalDependentChoiceAt γ)
    (hbase : IsForcingClosedThrough (A.projectionQuotient T τ)
      (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) γ)
    (hcollapse : ∀ (H : Set V) (hH : IsExternalForcingGeneric T U H)
      (hA : forcingProjectionGeneric A.P A.R τ H = A.G),
      let C : ForcingContext V := ⟨T, U, o, H, hU, ho, hH⟩
      ∃ κ δ : C.Model, IsRegularCardinal κ ∧ A.projectionInclusion C hτ hA γ ∈ κ ∧
        C.ofName ⟨Q, h.posetName⟩ = woodinCollapse κ δ ∧
        C.ofName ⟨S, h.orderName⟩ = woodinCollapseOrder κ δ) :
    IsForcingClosedAt (A.projectionQuotient (twoStepConditions T U Q t) π)
      (forcingSeparativeOrder (A.projectionQuotient (twoStepConditions T U Q t) π)
        (A.projectionQuotientOrder (twoStepConditions T U Q t) (twoStepOrder T U Q S t) π)) γ := by
  apply A.quotient_separative_closedAt_comp_countable hτ hU ho (twoStep_preorder hU ho h)
    hπ (twoStep_projection hU ho h) he γ (hbase γ inferInstance (fun _ hx ↦ hx))
  intro H hH hA
  let C : ForcingContext V := ⟨T, U, o, H, hU, ho, hH⟩
  obtain ⟨κ, δ, hκ, hγκ, hQ, hS⟩ := hcollapse H hH hA
  exact C.twoStep_collapse_quotient_closedAt h hQ hS hκ hγκ
    (A.projectionInclusion_dependentChoiceAt_of_separative_closed C hτ hA hDC hbase)

end ForcingContext
end ZFVP

