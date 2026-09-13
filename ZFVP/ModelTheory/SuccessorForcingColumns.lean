import ZFVP.ModelTheory.SuccessorForcingLift
import ZFVP.SetTheory.ForcingLiftExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def successorStageProjection (C π k i : V) : V :=
  definableGraph C (fun a ↦ (π ‘ ⟨i, k⟩ₖ) ‘ (kpair.π₁ a)) (by definability)

noncomputable def successorStageSection (P E k t i : V) : V :=
  definableGraph (P ‘ i) (fun p ↦ ⟨(E ‘ ⟨i, k⟩ₖ) ‘ p, t⟩ₖ) (by definability)

instance successorStageProjection_index_definable (C π k : V) :
    ℒₛₑₜ-function₁[V] (successorStageProjection C π k) := by
  have h : ℒₛₑₜ-relation (fun g i : V ↦ ∀ z, z ∈ g ↔ ∃ a ∈ C,
    z = ⟨a, (π ‘ ⟨i, k⟩ₖ) ‘ (kpair.π₁ a)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = successorStageProjection C π k (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [successorStageProjection, mem_definableGraph_iff]

instance successorStageSection_index_definable (P E k t : V) :
    ℒₛₑₜ-function₁[V] (successorStageSection P E k t) := by
  have h : ℒₛₑₜ-relation (fun g i : V ↦ ∀ z, z ∈ g ↔ ∃ p ∈ P ‘ i,
    z = ⟨p, ⟨(E ‘ ⟨i, k⟩ₖ) ‘ p, t⟩ₖ⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = successorStageSection P E k t (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [successorStageSection, mem_definableGraph_iff]

noncomputable def successorProjectionColumn (θ C π k : V) : V :=
  definableGraph θ (successorStageProjection C π k) (successorStageProjection_index_definable C π k)

noncomputable def successorSectionColumn (θ P E k t : V) : V :=
  definableGraph θ (successorStageSection P E k t) (successorStageSection_index_definable P E k t)

theorem successorProjectionColumn_value {θ C π k i a : V} (hi : i ∈ θ) (ha : a ∈ C) :
    ((successorProjectionColumn θ C π k) ‘ i) ‘ a = (π ‘ ⟨i, k⟩ₖ) ‘ (kpair.π₁ a) := by
  rw [successorProjectionColumn, value_definableGraph _ _ _ hi,
    successorStageProjection, value_definableGraph _ _ _ ha]

theorem successorSectionColumn_value {θ P E k t i p : V} (hi : i ∈ θ) (hp : p ∈ P ‘ i) :
    ((successorSectionColumn θ P E k t) ‘ i) ‘ p = ⟨(E ‘ ⟨i, k⟩ₖ) ‘ p, t⟩ₖ := by
  rw [successorSectionColumn, value_definableGraph _ _ _ hi,
    successorStageSection, value_definableGraph _ _ _ hp]

theorem successor_splitColumn {θ P R π E k Q S t one : V}
    (h : IsSplitForcingSystem θ P π E) (hk : k ∈ θ) (hmax : ∀ i ∈ θ, i ⊆ k)
    (hR : IsForcingPreorder (P ‘ k) (R ‘ k)) (htop : IsForcingTop (P ‘ k) (R ‘ k) one)
    (hQ : IsForcingIterand (P ‘ k) (R ‘ k) Q S t) :
    IsSplitForcingColumn θ P π E (twoStepConditions (P ‘ k) (R ‘ k) Q t)
      (successorProjectionColumn θ (twoStepConditions (P ‘ k) (R ‘ k) Q t) π k)
      (successorSectionColumn θ P E k t) := by
  have base {a : V} (ha : a ∈ twoStepConditions (P ‘ k) (R ‘ k) Q t) : kpair.π₁ a ∈ P ‘ k := by
    obtain ⟨p, hp, τ, _, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp ha
    simpa only [kpair.π₁_kpair] using hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi a ha
    rw [successorProjectionColumn_value hi ha]
    exact h.projMaps i hi k hk (hmax i hi) _ (base ha)
  · intro i hi p hp
    rw [successorSectionColumn_value hi hp]
    exact twoStep_section_mem hR htop hQ (h.secMaps i hi k hk (hmax i hi) p hp)
  · intro i hi j hj hij a ha
    rw [successorProjectionColumn_value hi ha, successorProjectionColumn_value hj ha]
    exact h.projComp i hi j hj k hk hij (hmax j hj) _ (base ha)
  · intro i hi j hj hij p hp
    rw [successorSectionColumn_value hi hp,
      successorSectionColumn_value hj (h.secMaps i hi j hj hij p hp),
      h.secComp i hi j hj k hk hij (hmax j hj) p hp]
  · intro i hi p hp
    rw [successorSectionColumn_value hi hp,
      successorProjectionColumn_value hi (twoStep_section_mem hR htop hQ
        (h.secMaps i hi k hk (hmax i hi) p hp)), kpair.π₁_kpair,
      h.retraction i hi k hk (hmax i hi) p hp]

instance successorForcingLift_index_definable (C P L k : V) :
    ℒₛₑₜ-function₁[V] (fun i ↦ successorForcingLift C (P ‘ i) (L ‘ ⟨i, k⟩ₖ)) := by
  have h : ℒₛₑₜ-relation (fun g i : V ↦ ∀ z, z ∈ g ↔ ∃ a ∈ C ×ˢ (P ‘ i),
    z = ⟨a, successorForcingLiftValue (L ‘ ⟨i, k⟩ₖ) (kpair.π₁ a) (kpair.π₂ a)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = successorForcingLift C (P ‘ (v 1)) (L ‘ ⟨v 1, k⟩ₖ) ↔ _
  rw [mem_ext_iff]
  simp only [successorForcingLift, mem_definableGraph_iff]

noncomputable def successorLiftColumn (θ C P L k : V) : V :=
  definableGraph θ (fun i ↦ successorForcingLift C (P ‘ i) (L ‘ ⟨i, k⟩ₖ))
    (successorForcingLift_index_definable C P L k)

theorem successorLiftColumn_value {θ C P L k i a b : V}
    (hi : i ∈ θ) (ha : a ∈ C) (hb : b ∈ P ‘ i) :
    ((successorLiftColumn θ C P L k) ‘ i) ‘ ⟨a, b⟩ₖ =
      successorForcingLiftValue (L ‘ ⟨i, k⟩ₖ) a b := by
  rw [successorLiftColumn, value_definableGraph _ _ _ hi, successorForcingLift_value ha hb]

theorem successor_coherentLiftColumn {θ P R π L k Q S t one : V}
    (hL : IsCoherentForcingLift θ P R π L) (hk : k ∈ θ) (hmax : ∀ i ∈ θ, i ⊆ k)
    (hR : IsForcingPreorder (P ‘ k) (R ‘ k)) (htop : IsForcingTop (P ‘ k) (R ‘ k) one)
    (hQ : IsForcingIterand (P ‘ k) (R ‘ k) Q S t) :
    IsCoherentForcingLiftColumn θ P R π L (twoStepConditions (P ‘ k) (R ‘ k) Q t)
      (twoStepOrder (P ‘ k) (R ‘ k) Q S t)
      (successorProjectionColumn θ (twoStepConditions (P ‘ k) (R ‘ k) Q t) π k)
      (successorLiftColumn θ (twoStepConditions (P ‘ k) (R ‘ k) Q t) P L k) := by
  have base {a : V} (ha : a ∈ twoStepConditions (P ‘ k) (R ‘ k) Q t) : kpair.π₁ a ∈ P ‘ k := by
    obtain ⟨p, hp, τ, _, rfl, _⟩ := (mem_twoStepConditions _ _ _ _ _).mp ha
    simpa only [kpair.π₁_kpair] using hp
  refine ⟨?_, ?_⟩
  · intro i hi a ha b hb hle
    rw [successorProjectionColumn_value hi ha] at hle
    have hl := hL.lift i hi k hk (hmax i hi) _ (base ha) b hb hle
    have hs := twoStepStronger_lift hR htop hQ ha hl.1 hl.2.1
    have hs' : successorForcingLiftValue (L ‘ ⟨i, k⟩ₖ) a b ∈
        twoStepConditions (P ‘ k) (R ‘ k) Q t := hs.1
    rw [successorLiftColumn_value hi ha hb]
    refine ⟨hs.1, hs.2.1, ?_⟩
    rw [successorProjectionColumn_value hi hs']
    simpa only [successorForcingLiftValue, twoStepStronger, kpair.π₁_kpair] using hl.2.2
  · intro i hi j hj hij a ha b hb hle
    rw [successorProjectionColumn_value hi ha] at hle
    have hl := hL.lift i hi k hk (hmax i hi) _ (base ha) b hb hle
    have hs := twoStepStronger_lift hR htop hQ ha hl.1 hl.2.1
    have hs' : successorForcingLiftValue (L ‘ ⟨i, k⟩ₖ) a b ∈
        twoStepConditions (P ‘ k) (R ‘ k) Q t := hs.1
    rw [successorLiftColumn_value hi ha hb, successorProjectionColumn_value hj hs',
      successorProjectionColumn_value hj ha]
    apply successorForcingLift_commute
    exact hL.commute i hi j hj k hk hij (hmax j hj) _ (base ha) b hb hle

end ZFVP
