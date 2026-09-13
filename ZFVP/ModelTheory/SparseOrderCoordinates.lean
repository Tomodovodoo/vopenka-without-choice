import ZFVP.ModelTheory.SparseCarrierOrderRecursion
import ZFVP.ModelTheory.SparseCutOrder
import ZFVP.ModelTheory.SparseCoordinatePoolRecovery
import ZFVP.ModelTheory.SparseReverseOrderComparison

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def SparseCoordinateComparison (S R a p q : V) : Prop :=
  SparseSubsetComparison (sparseCarrierCut S a) (sparseCutOrder S R a) (p ↾ a) (q ‘ a) (p ‘ a)

attribute [local aesop safe (rule_sets := [Definability])] Language.DefinableRel₅.comp

instance sparseCoordinateComparison_definable : ℒₛₑₜ-relation₅[V] SparseCoordinateComparison := by
  unfold SparseCoordinateComparison
  definability

def SparseOrderCoordinates (S R a p q : V) : Prop :=
  ∀ b ∈ a, SparseCoordinateComparison S R b p q

instance sparseOrderCoordinates_definable : ℒₛₑₜ-relation₅[V] SparseOrderCoordinates := by
  unfold SparseOrderCoordinates
  definability

theorem sparseOrderCoordinates_successor {S R a p q : V} :
    SparseOrderCoordinates S R (succ a) p q ↔
      SparseOrderCoordinates S R a p q ∧ SparseCoordinateComparison S R a p q := by
  constructor
  · intro h
    exact ⟨fun b hb ↦ h b (mem_succ_iff.mpr (Or.inr hb)), h a (mem_succ_self a)⟩
  · rintro ⟨h, ha⟩ b hb
    rcases mem_succ_iff.mp hb with he | hb
    · exact he ▸ ha
    · exact h b hb

theorem sparseCoordinateComparison_restrict {S R a c p q : V} [IsOrdinal c]
    [IsFunction p] [IsFunction q] (ha : a ∈ c) :
    SparseCoordinateComparison (sparseCarrierCut S c) (sparseCutOrder S R c) a (p ↾ c) (q ↾ c) ↔
      SparseCoordinateComparison S R a p q := by
  have hac := IsOrdinal.toIsTransitive.transitive _ ha
  unfold SparseCoordinateComparison
  rw [sparseCarrierCut_idem hac, sparseCutOrder_idem hac, restrict_restrict_of_subset hac,
    function_restrict_value_at ha, function_restrict_value_at ha]

theorem sparseOrderCoordinates_restrict {S R a c p q : V} [IsOrdinal c]
    [IsFunction p] [IsFunction q] (ha : a ⊆ c) :
    SparseOrderCoordinates (sparseCarrierCut S c) (sparseCutOrder S R c) a (p ↾ c) (q ↾ c) ↔
      SparseOrderCoordinates S R a p q := by
  apply forall_congr'
  intro b
  apply forall_congr'
  intro hb
  exact sparseCoordinateComparison_restrict (ha b hb)

theorem sparseSubsetComparison_empty {P R p one : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hp : p ∈ P) :
    SparseSubsetComparison P R p ∅ ∅ := by
  rw [sparseSubsetComparison_iff hR (empty_forcingName P) (empty_forcingName P)]
  let t : ForcingName P := ⟨∅, empty_forcingName P⟩
  let φ : SetTheorySemisentence 2 := .rel Language.Set.Rel.eq ![.bvar 0, .bvar 1]
  apply forcingFormula_entailment φ isSubsetOf (by
    intro W _ _ _ v hv
    have he : v 0 = v 1 := by simpa [φ, Structure.rel] using hv
    simp [he]) hR ht hp ![t, t]
  simpa only [φ, forcingFormula_rel, forcingAtomic, forcingTermValue, value_standardTuple,
    Matrix.cons_val_zero, Matrix.cons_val_one, atomicEquality_refl hR] using hp

theorem sparseCoordinateComparison_empty {S R a p q : V}
    (hR : IsForcingPreorder S R) (ht : IsForcingTop S R ∅)
    (hp : p ↾ a ∈ sparseCarrierCut S a) (hp0 : p ‘ a = ∅) (hq0 : q ‘ a = ∅) :
    SparseCoordinateComparison S R a p q := by
  unfold SparseCoordinateComparison
  rw [hp0, hq0]
  exact sparseSubsetComparison_empty (sparseCutOrder_preorder hR) (sparseCutOrder_top ht) hp

end ZFVP
