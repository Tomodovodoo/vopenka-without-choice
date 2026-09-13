import ZFVP.ModelTheory.ClassForcingTowerStageBoundedEquiv
import ZFVP.ModelTheory.ClassForcingTowerZF
import ZFVP.ModelTheory.ProjectionSubsetPreservation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace DefinableForcingTower
variable (T : DefinableForcingTower V) {G : Set V}
  (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)

def StageSetsHaveDCEnumerations : Prop :=
  ∀ (i : V) [IsOrdinal i] (x : (T.stageContext hG i).Model),
    ∃ j : V, ∃ hj : IsOrdinal j, ∃ hij : i ⊆ j, ∃ α : V, ∃ hα : IsOrdinal α,
      InternalDependentChoiceAt ((T.stageContext hG j).check α) ∧
      ∃ e : (T.stageContext hG j).Model,
        e ∈ (T.stageInclusion hG hij x) ^ ((T.stageContext hG j).check α) ∧
        range e = T.stageInclusion hG hij x

theorem stageSubset_stabilization_of_enumeration
    {i j k α : V} [IsOrdinal i] [IsOrdinal j] [IsOrdinal k] [IsOrdinal α]
    (hij : i ⊆ j) (hjk : j ⊆ k) (x : (T.stageContext hG i).Model)
    (hDC : InternalDependentChoiceAt ((T.stageContext hG j).check α))
    (hclosed : IsForcingClosedThrough
      ((T.stageContext hG j).projectionQuotient (T.P k) (T.projection j k))
      (forcingSeparativeOrder ((T.stageContext hG j).projectionQuotient (T.P k) (T.projection j k))
        ((T.stageContext hG j).projectionQuotientOrder (T.P k) (T.R k) (T.projection j k)))
      ((T.stageContext hG j).check α))
    {e : (T.stageContext hG j).Model}
    (he : e ∈ (T.stageInclusion hG hij x) ^ ((T.stageContext hG j).check α))
    (hr : range e = T.stageInclusion hG hij x)
    {z : (T.stageContext hG k).Model} (hz : z ⊆ T.stageInclusion hG (subset_trans hij hjk) x) :
    ∃ w : (T.stageContext hG j).Model, T.stageInclusion hG hjk w = z := by
  have hz' : z ⊆ T.stageInclusion hG hjk (T.stageInclusion hG hij x) := by
    rwa [T.stageInclusion_comp hG hij hjk]
  obtain ⟨w, _, hw⟩ := (T.stageContext hG j).projectionInclusion_subset_of_separative_closed
    (T.stageContext hG k) (T.splitProjection hjk) (T.stageFilter_projection hG.1 hjk)
    hDC hclosed he hr hz'
  exact ⟨w, hw⟩

theorem subsetsStabilize_of_enumerations
    (henum : T.StageSetsHaveDCEnumerations hG)
    (hclosed : ∀ (j k : V) [IsOrdinal j] [IsOrdinal k], j ⊆ k →
      ∀ (α : V) [IsOrdinal α], InternalDependentChoiceAt ((T.stageContext hG j).check α) →
      IsForcingClosedThrough ((T.stageContext hG j).projectionQuotient (T.P k) (T.projection j k))
        (forcingSeparativeOrder ((T.stageContext hG j).projectionQuotient (T.P k) (T.projection j k))
          ((T.stageContext hG j).projectionQuotientOrder (T.P k) (T.R k) (T.projection j k)))
        ((T.stageContext hG j).check α)) : T.SubsetsStabilize hG := by
  intro i hi x
  let xi := (T.stageBoundedEquiv hG i).symm x
  obtain ⟨j, hj, hij, α, hα, hDC, e, he, hr⟩ := henum i xi
  let := hj
  let := hα
  refine ⟨j, hj, hij, ?_⟩
  intro k hk hjk z hz
  let zi := (T.stageBoundedEquiv hG k).symm z
  have hz' : zi ⊆ T.stageInclusion hG (subset_trans hij hjk) xi := by
    apply ((T.stageToBounded hG k).subset_iff _ _).mp
    change T.stageBoundedEquiv hG k zi ⊆ T.stageBoundedEquiv hG k (T.stageInclusion hG (subset_trans hij hjk) xi)
    rw [← T.stageBoundedEquiv_commutes hG (subset_trans hij hjk)]
    simpa only [zi, xi, Equiv.apply_symm_apply] using hz
  obtain ⟨w, hw⟩ := T.stageSubset_stabilization_of_enumeration hG hij hjk xi hDC
    (hclosed j k hjk α hDC) he hr hz'
  refine ⟨T.stageBoundedEquiv hG j w, ?_⟩
  rw [T.stageBoundedEquiv_commutes hG hjk, hw]
  exact (T.stageBoundedEquiv hG k).apply_symm_apply z

end DefinableForcingTower
end ZFVP
