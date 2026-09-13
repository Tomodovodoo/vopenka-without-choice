import ZFVP.ModelTheory.ClassForcingQuotientWitnesses
import ZFVP.ModelTheory.ClassForcingWitnessSchedule
import ZFVP.ModelTheory.ForcingModelRank
import ZFVP.SetTheory.StagedForcingDependentChoice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

/-- Apply internal dependent choice to the checked stage and witness tables.
The witnesses may leave the current stage, but stay in the next prescribed
stage. No ground class predicate is used as an extension predicate. -/
theorem quotient_stagedChoices (A : ForcingContext V) {I i α c : V}
    [IsOrdinal i] [IsOrdinal α] (hP : A.P = T.P i) (hR : A.R = T.R i)
    (D : V → V → Prop) (hDdef : ℒₛₑₜ-relation D)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (hord : ∀ β, IsOrdinal β → β ⊆ α → IsOrdinal (F β))
    (hbase : ∀ β, IsOrdinal β → β ⊆ α → i ⊆ F β)
    (hmono : ∀ β γ, IsOrdinal β → IsOrdinal γ → β ⊆ γ → γ ⊆ α → F β ⊆ F γ)
    (hnext : ∀ β ∈ α, T.ProjectedWitnessStage D I i (F β) (F (succ β)))
    (hc : c ∈ T.boundedConditions (F ∅)) (hcG : T.projectCondition i c ∈ A.G)
    (hDC : InternalDependentChoiceAt (A.check α))
    (hclosed : ∀ β, IsOrdinal β → β ⊆ α →
      IsForcingClosedAt (A.projectionQuotient (T.P (F β)) (T.projection i (F β)))
        (forcingSeparativeOrder (A.projectionQuotient (T.P (F β)) (T.projection i (F β)))
          (A.projectionQuotientOrder (T.P (F β)) (T.R (F β)) (T.projection i (F β)))) (A.check β))
    (e : A.Model) (he : e ∈ (A.check I) ^ (A.check α)) :
    let X := T.boundedQuotient A i (F α)
    let S := forcingSeparativeOrder X (T.boundedQuotientOrder A i (F α))
    ∃ f, f ∈ X ^ (A.check α) ∧
      (∀ β ∈ A.check α, f ‘ β ∈ (A.check (T.boundedDenseFamily D hDdef I (F α))) ‘ (e ‘ β)) ∧
      ∃ q ∈ X, ⟨q, A.check c⟩ₖ ∈ S ∧ ∀ β ∈ A.check α, ⟨q, f ‘ β⟩ₖ ∈ S := by
  let X := T.boundedQuotient A i (F α)
  let S := forcingSeparativeOrder X (T.boundedQuotientOrder A i (F α))
  let B := T.quotientStageFamily A F hF i (succ α)
  let E := A.checkedFamilyAlong (T.boundedDenseFamily D hDdef I (F α)) (A.check α) e
  have hK : IsOrdinal (F α) := hord α inferInstance (subset_refl _)
  let := hK
  have hBval (β : V) [IsOrdinal β] (hβα : β ⊆ α) :
      B ‘ (A.check β) = T.boundedQuotient A i (F β) :=
    T.quotientStageFamily_value A F hF i (succ α) (mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hβα))
  have hBα : B ‘ (A.check α) = X := hBval α (subset_refl _)
  have hcar : ∀ β : A.Model, IsOrdinal β → β ⊆ A.check α → B ‘ β ⊆ X := by
    intro β hβ hβα
    let := hβ
    obtain ⟨b, hb, rfl⟩ := A.ordinal_eq_check β
    let := hb
    have hbα := (A.checkEmbedding.subset_iff b α).mp hβα
    have : IsOrdinal (F b) := hord b hb hbα
    rw [hBval b hbα]
    exact T.boundedQuotient_mono A hP (hmono b α hb inferInstance hbα (subset_refl _))
  have hinc : ∀ β γ : A.Model, IsOrdinal β → IsOrdinal γ → β ⊆ γ → γ ⊆ A.check α →
      B ‘ β ⊆ B ‘ γ := by
    intro β γ hβ hγ hβγ hγα
    let := hβ
    let := hγ
    obtain ⟨b, hb, rfl⟩ := A.ordinal_eq_check β
    obtain ⟨g, hg, rfl⟩ := A.ordinal_eq_check γ
    let := hb
    let := hg
    have hbg := (A.checkEmbedding.subset_iff b g).mp hβγ
    have hgα := (A.checkEmbedding.subset_iff g α).mp hγα
    have hbα := subset_trans hbg hgα
    have : IsOrdinal (F b) := hord b hb hbα
    have : IsOrdinal (F g) := hord g hg hgα
    rw [hBval b hbα, hBval g hgα]
    exact T.boundedQuotient_mono A hP (hmono b g hb hg hbg hgα)
  have hinit : A.check c ∈ B ‘ ∅ := by
    have : IsOrdinal (F ∅) := hord ∅ inferInstance (empty_subset _)
    rw [← A.check_empty, hBval ∅ (empty_subset _)]
    exact (T.check_mem_boundedQuotient_iff A hP).mpr ⟨hc, hcG⟩
  have hcl : ∀ β : A.Model, IsOrdinal β → β ⊆ A.check α → IsForcingClosedAt (B ‘ β) S β := by
    intro β hβ hβα
    let := hβ
    obtain ⟨b, hb, rfl⟩ := A.ordinal_eq_check β
    let := hb
    have hbα := (A.checkEmbedding.subset_iff b α).mp hβα
    have : IsOrdinal (F b) := hord b hb hbα
    rw [hBval b hbα]
    exact T.boundedQuotient_closedAt_ambient A hP (hbase b hb hbα)
      (hmono b α hb inferInstance hbα (subset_refl _)) (hclosed b hb hbα)
  have hn : ∀ β ∈ A.check α, ∀ q ∈ B ‘ β,
      ∃ r ∈ B ‘ (succ β), r ∈ E ‘ β ∧ ⟨r, q⟩ₖ ∈ S := by
    intro β hβ q hq
    obtain ⟨b, hb, rfl⟩ := (A.mem_check_iff α β).mp hβ
    have : IsOrdinal b := IsOrdinal.of_mem hb
    have hbα : b ⊆ α := IsOrdinal.toIsTransitive.transitive _ hb
    have hsbα : succ b ⊆ α := by
      intro x hx
      rcases mem_succ_iff.mp hx with rfl | hx
      · exact hb
      · exact IsOrdinal.toIsTransitive.mem_trans hx hb
    have : IsOrdinal (F b) := hord b inferInstance hbα
    have : IsOrdinal (F (succ b)) := hord (succ b) inferInstance hsbα
    have hename := function_value_mem he ((A.check_mem_iff b α).mpr hb)
    obtain ⟨a, ha, hea⟩ := (A.mem_check_iff I (e ‘ (A.check b))).mp hename
    have hstep := T.boundedQuotient_witnessStep A hP
      (hmono b α inferInstance inferInstance hbα (subset_refl _))
      (hmono (succ b) α inferInstance inferInstance hsbα (subset_refl _)) D hDdef ha
      ((hnext b hb).2.2 a ha) hR q (by rwa [hBval b hbα] at hq)
    simpa only [← A.check_succ, hBval (succ b) hsbα, E,
      A.checkedFamilyAlong_value _ ((A.check_mem_iff b α).mpr hb), hea] using hstep
  obtain ⟨f, hf, hfD, _, q, hq, hqc, hqf⟩ := stagedForcingDependentChoice
    (forcingSeparativeOrder_preorder (T.boundedQuotient_preorder A hP)) hDC hcar hinc hinit hcl hn
  refine ⟨f, hf, ?_, q, ?_, hqc, hqf⟩
  swap
  · change q ∈ X
    rwa [← hBα]
  intro β hβ
  have h := (hfD β hβ).2
  change f ‘ β ∈ (A.checkedFamilyAlong (T.boundedDenseFamily D hDdef I (F α)) (A.check α) e) ‘ β at h
  rwa [A.checkedFamilyAlong_value _ hβ] at h

end DefinableForcingTower
end ZFVP
