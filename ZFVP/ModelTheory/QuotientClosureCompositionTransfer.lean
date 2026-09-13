import ZFVP.ModelTheory.QuotientClosureComposition
import ZFVP.ModelTheory.ProjectionQuotientClosureForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem projectionQuotient_closedBelow_comp_forced_countable [Countable V]
    {P R one T U o Q S π τ ρ E η : V} [IsOrdinal η]
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hτ : IsForcingSplitProjection P R T U τ E)
    (hU : IsForcingPreorder T U) (ho : IsForcingTop T U o) (hS : IsForcingPreorder Q S)
    (hπ : IsForcingProjection P R Q S π) (hρ : IsForcingProjection T U Q S ρ)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q)
    (hbase : ForcesProjectionQuotientClosedBelow P R one T U τ η)
    (htail : ForcesProjectionQuotientClosedBelow T U o Q S ρ η) :
    ForcesProjectionQuotientClosedBelow P R one Q S π η := by
  apply projectionQuotient_closedBelow_forced_of_generics hR ht hπ hS
  intro G hG
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  apply A.quotient_separative_closedBelow_comp_countable hτ hU ho hS hπ.maps hρ he
    (A.check η) (A.projectionQuotient_closedBelow_of_forced hτ.projection hU hbase)
  intro H hH hA
  let C : ForcingContext V := ⟨T, U, o, H, hU, ho, hH⟩
  change IsForcingClosedBelow (C.projectionQuotient Q ρ)
    (forcingSeparativeOrder (C.projectionQuotient Q ρ) (C.projectionQuotientOrder Q S ρ))
    (A.projectionInclusion C hτ hA (A.check η))
  rw [A.projectionInclusion_check C hτ hA]
  exact C.projectionQuotient_closedBelow_of_forced hρ hS htail

def quotientClosureCompositionTransferFormula : SetTheorySemisentence 13 :=
  f“P R b T U o Q S π τ ρ E η.
    !forcingPreorderFormula P R ∧ !forcingTopFormula P R b ∧
    !forcingSplitProjectionFormula P R T U τ E ∧
    !forcingPreorderFormula T U ∧ !forcingTopFormula T U o ∧ !forcingPreorderFormula Q S ∧
    !forcingProjectionFormula P R Q S π ∧ !forcingProjectionFormula T U Q S ρ ∧
    (∀ q ∈ Q, !value.dfn τ (!value.dfn ρ q) = !value.dfn π q) ∧ !IsOrdinal.dfn η ∧
    !allProjectionQuotientClosedBelowFormula P R b T U τ η ∧
    !allProjectionQuotientClosedBelowFormula T U o Q S ρ η →
    !allProjectionQuotientClosedBelowFormula P R b Q S π η”

private theorem forall_six_eq {β : Type*} (a b c d e f : β) (F : β → β → β → β → β → β → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔
      F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

theorem eval_quotientClosureCompositionTransferFormula (v : Fin 13 → V) :
    quotientClosureCompositionTransferFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
      IsForcingSplitProjection (v 0) (v 1) (v 3) (v 4) (v 9) (v 11) →
      IsForcingPreorder (v 3) (v 4) → IsForcingTop (v 3) (v 4) (v 5) →
      IsForcingPreorder (v 6) (v 7) → IsForcingProjection (v 0) (v 1) (v 6) (v 7) (v 8) →
      IsForcingProjection (v 3) (v 4) (v 6) (v 7) (v 10) →
      (∀ q ∈ v 6, (v 9) ‘ ((v 10) ‘ q) = (v 8) ‘ q) → IsOrdinal (v 12) →
      ForcesProjectionQuotientClosedBelow (v 0) (v 1) (v 2) (v 3) (v 4) (v 9) (v 12) →
      ForcesProjectionQuotientClosedBelow (v 3) (v 4) (v 5) (v 6) (v 7) (v 10) (v 12) →
      ForcesProjectionQuotientClosedBelow (v 0) (v 1) (v 2) (v 6) (v 7) (v 8) (v 12)) := by
  simp [quotientClosureCompositionTransferFormula]
  simp [Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Fin.forall_fin_succ, forall_six_eq]

theorem projectionQuotient_closedBelow_comp_forced
    {P R one T U o Q S π τ ρ E η : V} [IsOrdinal η]
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hτ : IsForcingSplitProjection P R T U τ E)
    (hU : IsForcingPreorder T U) (ho : IsForcingTop T U o) (hS : IsForcingPreorder Q S)
    (hπ : IsForcingProjection P R Q S π) (hρ : IsForcingProjection T U Q S ρ)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q)
    (hbase : ForcesProjectionQuotientClosedBelow P R one T U τ η)
    (htail : ForcesProjectionQuotientClosedBelow T U o Q S ρ η) :
    ForcesProjectionQuotientClosedBelow P R one Q S π η := by
  have hv : quotientClosureCompositionTransferFormula.Evalb ![P, R, one, T, U, o, Q, S, π, τ, ρ, E, η] := by
    apply eval_of_countable_zf quotientClosureCompositionTransferFormula
    intro W _ _ _ _ w
    apply (eval_quotientClosureCompositionTransferFormula w).mpr
    intro hR ht hτ hU ho hS hπ hρ he hη hbase htail
    let := hη
    exact projectionQuotient_closedBelow_comp_forced_countable hR ht hτ hU ho hS hπ hρ he hbase htail
  exact (eval_quotientClosureCompositionTransferFormula _).mp hv hR ht hτ hU ho hS hπ hρ he
    (show IsOrdinal η from inferInstance) hbase htail

theorem projectionQuotient_closedBelow_mono_forced_countable [Countable V]
    {P R one Q S π η κ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hS : IsForcingPreorder Q S) (hπ : IsForcingProjection P R Q S π)
    (hηκ : η ⊆ κ) (hc : ForcesProjectionQuotientClosedBelow P R one Q S π κ) :
    ForcesProjectionQuotientClosedBelow P R one Q S π η := by
  apply projectionQuotient_closedBelow_forced_of_generics hR ht hπ hS
  intro G hG
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  have hh := A.projectionQuotient_closedBelow_of_forced hπ hS hc
  change IsForcingClosedBelow (A.projectionQuotient Q π)
    (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) (A.check η)
  intro α hα
  exact hh α (((A.checkEmbedding.subset_iff η κ).mpr hηκ) α hα)

def quotientClosureMonotoneTransferFormula : SetTheorySemisentence 8 :=
  f“P R o Q S π η κ. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !forcingPreorderFormula Q S ∧ !forcingProjectionFormula P R Q S π ∧ η ⊆ κ ∧
    !allProjectionQuotientClosedBelowFormula P R o Q S π κ →
    !allProjectionQuotientClosedBelowFormula P R o Q S π η”

theorem eval_quotientClosureMonotoneTransferFormula (v : Fin 8 → V) :
    quotientClosureMonotoneTransferFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
      IsForcingPreorder (v 3) (v 4) → IsForcingProjection (v 0) (v 1) (v 3) (v 4) (v 5) →
      v 6 ⊆ v 7 → ForcesProjectionQuotientClosedBelow (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 7) →
      ForcesProjectionQuotientClosedBelow (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) := by
  simp [quotientClosureMonotoneTransferFormula]

theorem projectionQuotient_closedBelow_mono_forced {P R one Q S π η κ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hS : IsForcingPreorder Q S) (hπ : IsForcingProjection P R Q S π)
    (hηκ : η ⊆ κ) (hc : ForcesProjectionQuotientClosedBelow P R one Q S π κ) :
    ForcesProjectionQuotientClosedBelow P R one Q S π η := by
  have hv : quotientClosureMonotoneTransferFormula.Evalb ![P, R, one, Q, S, π, η, κ] := by
    apply eval_of_countable_zf quotientClosureMonotoneTransferFormula
    intro W _ _ _ _ w
    exact (eval_quotientClosureMonotoneTransferFormula w).mpr
      (fun hR ht hS hπ hηκ hc ↦ projectionQuotient_closedBelow_mono_forced_countable hR ht hS hπ hηκ hc)
  exact (eval_quotientClosureMonotoneTransferFormula _).mp hv hR ht hS hπ hηκ hc

end ZFVP
