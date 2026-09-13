import ZFVP.ModelTheory.ClassForcingPretamePreparation
import ZFVP.ModelTheory.ClassForcingBoundedCover

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

/-- Eventual DC enumerations and the corresponding set-stage quotient
closure imply pretameness. Collection bounds the ground witness searches;
dependent choice is applied only to sets in an intermediate extension. -/
theorem isPretame_of_enumerations_and_closure [Countable V]
    (henum : ∀ (G : Set V) (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G),
      T.StageSetsHaveDCEnumerations hG)
    (hclosed : ∀ (G : Set V) (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)
      (i K : V) [IsOrdinal i] [IsOrdinal K], i ⊆ K →
      ∀ (α : V) [IsOrdinal α], InternalDependentChoiceAt ((T.stageContext hG i).check α) →
      IsForcingClosedThrough ((T.stageContext hG i).projectionQuotient (T.P K) (T.projection i K))
        (forcingSeparativeOrder ((T.stageContext hG i).projectionQuotient (T.P K) (T.projection i K))
          ((T.stageContext hG i).projectionQuotientOrder (T.P K) (T.R K) (T.projection i K)))
        ((T.stageContext hG i).check α)) : T.IsPretame := by
  intro D hDdef I hD c hc
  obtain ⟨G, hG, hcG⟩ := T.exists_generic hc
  obtain ⟨i, hi, α, hα, hci, hciG, hDC, e, he, her⟩ :=
    T.prepare_pretame_enumeration hG (henum G hG) I hcG
  let := hi
  let := hα
  let A := T.stageContext hG i
  let K := T.witnessStageSchedule D hDdef I i i α
  have hK : IsOrdinal K := T.witnessStageSchedule_ordinal D hDdef I i i α
  let := hK
  have hiK : i ⊆ K := T.witnessStageSchedule_base_subset D hDdef I i i α
  obtain ⟨f, hf, hfD, q, hq, hqc, hqf⟩ := T.denseClasses_stagedChoices A rfl rfl
    (subset_refl i) D hDdef hD hci hciG hDC
    (fun L hL hiL ↦ by
      let := hL
      exact hclosed G hG i L hiL α hDC) e he
  obtain ⟨p, hp, hpc, hpG, hcover⟩ := T.boundedQuotient_cover_from_enumerated_bounds
    A rfl hiK D hDdef he her hf hfD hq hqc hqf
  obtain ⟨r, hr, hrp, _, href⟩ := T.boundedDenseFamily_refinement_of_cover D hDdef hiK hp
    (T.stageFilter_generic hG i) hpG hcover
  exact ⟨⟨K, r⟩ₖ, (T.condition_pair K r).mpr ⟨hK, hr⟩,
    T.le_trans ((T.le_sameStage_iff hr hp).mpr hrp) hpc,
    T.boundedDenseFamily D hDdef I K, href⟩

end DefinableForcingTower
end ZFVP
