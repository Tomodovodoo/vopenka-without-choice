import ZFVP.ModelTheory.GroundForcingGeneric
import ZFVP.SetTheory.CountableSets
import ZFVP.SetTheory.PathDependentChoice
import ZFVP.SetTheory.SequenceCollapseAbsorption

/-! Rasiowa–Sikorski inside a ZF model. A countable family of actual dense
sets is met by an actual descending sequence and its actual generated filter. -/

set_option autoImplicit false

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsInternalDescendingSequence (P R s : V) : Prop :=
  s ∈ P ^ (ω : V) ∧ ∀ n ∈ (ω : V), ⟨s ‘ (succ n), s ‘ n⟩ₖ ∈ R

instance isInternalDescendingSequence_definable : ℒₛₑₜ-relation₃[V] IsInternalDescendingSequence := by
  unfold IsInternalDescendingSequence
  definability

theorem IsInternalDescendingSequence.mono {P R s n m : V}
    (hs : IsInternalDescendingSequence P R s) (hR : IsForcingPreorder P R)
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hnm : n ⊆ m) :
    ⟨s ‘ m, s ‘ n⟩ₖ ∈ R := by
  have hlt : ∀ m ∈ (ω : V), ∀ n ∈ m, ⟨s ‘ m, s ‘ n⟩ₖ ∈ R := by
    apply naturalNumber_induction (fun m ↦ ∀ n ∈ m, ⟨s ‘ m, s ‘ n⟩ₖ ∈ R) (by definability)
    · simp [zero_def]
    · intro m hm ih n hnm
      rcases mem_succ_iff.mp hnm with rfl | hnm
      · exact hs.2 _ hm
      · exact hR.2.2 _ (function_value_mem hs.1 (ω_succ_closed hm))
          _ (function_value_mem hs.1 hm)
          _ (function_value_mem hs.1 (IsOrdinal.toIsTransitive.mem_trans hnm hm))
          (hs.2 m hm) (ih n hnm)
  let : IsOrdinal n := IsOrdinal.of_mem hn
  let : IsOrdinal m := IsOrdinal.of_mem hm
  rcases IsOrdinal.subset_iff.mp hnm with rfl | hnm
  · exact hR.2.1 _ (function_value_mem hs.1 hm)
  · exact hlt m hm n hnm

noncomputable def internalSequenceFilter (P R s : V) : V :=
  {q ∈ P ; ∃ n ∈ (ω : V), ⟨s ‘ n, q⟩ₖ ∈ R}

@[simp] theorem mem_internalSequenceFilter (P R s q : V) :
    q ∈ internalSequenceFilter P R s ↔ q ∈ P ∧ ∃ n ∈ (ω : V), ⟨s ‘ n, q⟩ₖ ∈ R := mem_sep_iff

instance internalSequenceFilter_definable : ℒₛₑₜ-function₃[V] internalSequenceFilter := by
  have h : ℒₛₑₜ-relation₄[V] (fun G P R s ↦
      ∀ q, q ∈ G ↔ q ∈ P ∧ ∃ n ∈ (ω : V), ⟨s ‘ n, q⟩ₖ ∈ R) := by definability
  apply Language.Definable.of_iff h
  intro v
  simp only [mem_ext_iff, mem_internalSequenceFilter]
  rfl

theorem internalSequenceFilter_contains {P R s n : V}
    (hR : IsForcingPreorder P R) (hs : s ∈ P ^ (ω : V)) (hn : n ∈ (ω : V)) :
    s ‘ n ∈ internalSequenceFilter P R s :=
  (mem_internalSequenceFilter _ _ _ _).mpr
    ⟨function_value_mem hs hn, n, hn, hR.2.1 _ (function_value_mem hs hn)⟩

theorem internalSequenceFilter_isFilter {P R s : V} (hR : IsForcingPreorder P R)
    (hs : IsInternalDescendingSequence P R s) : IsForcingFilter P R (internalSequenceFilter P R s) := by
  refine ⟨fun q hq ↦ (mem_internalSequenceFilter _ _ _ _).mp hq |>.1,
    ⟨s ‘ 0, internalSequenceFilter_contains hR hs.1 (by simp)⟩, ?_, ?_⟩
  · intro p hp q hq hpq
    obtain ⟨hpP, n, hn, hnp⟩ := (mem_internalSequenceFilter _ _ _ _).mp hp
    exact (mem_internalSequenceFilter _ _ _ _).mpr
      ⟨hq, n, hn, hR.2.2 _ (function_value_mem hs.1 hn) _ hpP _ hq hnp hpq⟩
  · intro p hp q hq
    obtain ⟨hpP, n, hn, hnp⟩ := (mem_internalSequenceFilter _ _ _ _).mp hp
    obtain ⟨hqP, m, hm, hmq⟩ := (mem_internalSequenceFilter _ _ _ _).mp hq
    have hnm : n ∪ m ∈ (ω : V) := ordinal_union_mem hn hm
    have hnsub : n ⊆ n ∪ m := fun _ hi ↦ mem_union_iff.mpr (Or.inl hi)
    have hmsub : m ⊆ n ∪ m := fun _ hi ↦ mem_union_iff.mpr (Or.inr hi)
    refine ⟨s ‘ (n ∪ m), internalSequenceFilter_contains hR hs.1 hnm, ?_, ?_⟩
    · exact hR.2.2 _ (function_value_mem hs.1 hnm) _ (function_value_mem hs.1 hn) _ hpP
        (hs.mono hR hn hnm hnsub) hnp
    · exact hR.2.2 _ (function_value_mem hs.1 hnm) _ (function_value_mem hs.1 hm) _ hqP
        (hs.mono hR hm hnm hmsub) hmq

theorem exists_internal_descending_sequence_meeting_enumeration
    (hDC : InternalPointedDependentChoice V) {P R e p : V} (hp : p ∈ P)
    (hd : ∀ n ∈ (ω : V), ForcingDense P R (e ‘ n)) :
    ∃ s : V, IsInternalDescendingSequence P R s ∧ s ‘ 0 = p ∧
      ∀ n ∈ (ω : V), s ‘ (succ n) ∈ e ‘ n := by
  let H := (ω : V) ×ˢ P
  let T := {z ∈ H ×ˢ H ;
    kpair.π₁ (kpair.π₂ z) = succ (kpair.π₁ (kpair.π₁ z)) ∧
      kpair.π₂ (kpair.π₂ z) ∈ e ‘ (kpair.π₁ (kpair.π₁ z)) ∧
      ⟨kpair.π₂ (kpair.π₂ z), kpair.π₂ (kpair.π₁ z)⟩ₖ ∈ R}
  have hT (u v : V) : ⟨u, v⟩ₖ ∈ T ↔ u ∈ H ∧ v ∈ H ∧
      kpair.π₁ v = succ (kpair.π₁ u) ∧ kpair.π₂ v ∈ e ‘ (kpair.π₁ u) ∧
        ⟨kpair.π₂ v, kpair.π₂ u⟩ₖ ∈ R := by
    simp only [T, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]
  have hcoords {u : V} (hu : u ∈ H) : kpair.π₁ u ∈ (ω : V) ∧ kpair.π₂ u ∈ P := by
    obtain ⟨n, hn, q, hq, rfl⟩ := mem_prod_iff.mp hu
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using And.intro hn hq
  have hserial : ∀ u ∈ H, ∃ v ∈ H, ⟨u, v⟩ₖ ∈ T := by
    intro u hu
    obtain ⟨hn, hq⟩ := hcoords hu
    obtain ⟨r, hr, hrq⟩ := (hd _ hn).2 _ hq
    have hv : ⟨succ (kpair.π₁ u), r⟩ₖ ∈ H :=
      kpair_mem_iff.mpr ⟨ω_succ_closed hn, (hd _ hn).1 _ hr⟩
    exact ⟨_, hv, (hT _ _).mpr ⟨hu, hv, by simp, by simpa using hr, by simpa using hrq⟩⟩
  obtain ⟨g, hg, hg0, hstep⟩ := hDC H T ⟨0, p⟩ₖ (kpair_mem_iff.mpr ⟨by simp, hp⟩) hserial
  have hindex : ∀ n ∈ (ω : V), kpair.π₁ (g ‘ n) = n := by
    apply naturalNumber_induction (fun n ↦ kpair.π₁ (g ‘ n) = n) (by definability)
    · rw [hg0, kpair.π₁_kpair]
    · intro n hn ih
      rw [((hT _ _).mp (hstep n hn)).2.2.1, ih]
  let s := definableGraph (ω : V) (fun n ↦ kpair.π₂ (g ‘ n)) (by definability)
  have hs : s ∈ P ^ (ω : V) := definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun n hn ↦ (hcoords (function_value_mem hg hn)).2)
  have hval {n : V} (hn : n ∈ (ω : V)) : s ‘ n = kpair.π₂ (g ‘ n) := value_definableGraph _ _ _ hn
  refine ⟨s, ⟨hs, ?_⟩, ?_, ?_⟩
  · intro n hn
    rw [hval (ω_succ_closed hn), hval hn]
    exact ((hT _ _).mp (hstep n hn)).2.2.2.2
  · rw [hval (by simp), hg0, kpair.π₂_kpair]
  · intro n hn
    rw [hval (ω_succ_closed hn)]
    have hh := ((hT _ _).mp (hstep n hn)).2.2.2.1
    rwa [hindex n hn] at hh

theorem internal_rasiowaSikorski_sequence_of_pointedDC (hDC : InternalPointedDependentChoice V)
    {P R F p : V} (hR : IsForcingPreorder P R) (hF : IsInternallyCountable F)
    (hd : ∀ D ∈ F, ForcingDense P R D) (hp : p ∈ P) :
    ∃ s : V, IsInternalDescendingSequence P R s ∧ s ‘ 0 = p ∧
      ∀ D ∈ F, ∃ n ∈ (ω : V), s ‘ n ∈ D := by
  obtain ⟨e, he, hre⟩ := exists_surjection_of_cardLE (internallyCountable_insert hF P)
    (show P ∈ insert P F by simp)
  let : IsFunction e := IsFunction.of_mem he
  have heDense : ∀ n ∈ (ω : V), ForcingDense P R (e ‘ n) := by
    intro n hn
    rcases mem_insert.mp (function_value_mem he hn) with h | h
    · rw [h]
      exact ⟨subset_refl _, fun q hq ↦ ⟨q, hq, hR.2.1 q hq⟩⟩
    · exact hd _ h
  obtain ⟨s, hs, hs0, hsmeet⟩ := exists_internal_descending_sequence_meeting_enumeration hDC hp heDense
  refine ⟨s, hs, hs0, ?_⟩
  intro D hD
  obtain ⟨n, hnD⟩ := mem_range_iff.mp (hre.symm ▸ mem_insert.mpr (Or.inr hD))
  have hn : n ∈ (ω : V) := (mem_of_mem_functions he hnD).1
  exact ⟨succ n, ω_succ_closed hn, (value_eq_of_kpair_mem hnD) ▸ hsmeet n hn⟩

theorem internal_rasiowaSikorski_sequence_of_dependentChoice (hDC : InternalDependentChoice V)
    {P R F p : V} (hR : IsForcingPreorder P R) (hF : IsInternallyCountable F)
    (hd : ∀ D ∈ F, ForcingDense P R D) (hp : p ∈ P) :
    ∃ s : V, IsInternalDescendingSequence P R s ∧ s ‘ 0 = p ∧
      ∀ D ∈ F, ∃ n ∈ (ω : V), s ‘ n ∈ D :=
  internal_rasiowaSikorski_sequence_of_pointedDC (pointedDependentChoice_of_unpointed hDC) hR hF hd hp

theorem internal_rasiowaSikorski_sequence (hAC : InternalChoice V)
    {P R F p : V} (hR : IsForcingPreorder P R) (hF : IsInternallyCountable F)
    (hd : ∀ D ∈ F, ForcingDense P R D) (hp : p ∈ P) :
    ∃ s : V, IsInternalDescendingSequence P R s ∧ s ‘ 0 = p ∧
      ∀ D ∈ F, ∃ n ∈ (ω : V), s ‘ n ∈ D :=
  internal_rasiowaSikorski_sequence_of_pointedDC (pointedDependentChoice_of_internalChoice hAC) hR hF hd hp

theorem internal_rasiowaSikorski_of_dependentChoice (hDC : InternalDependentChoice V)
    {P R F p : V} (hR : IsForcingPreorder P R) (hF : IsInternallyCountable F)
    (hd : ∀ D ∈ F, ForcingDense P R D) (hp : p ∈ P) :
    ∃ G : V, IsForcingFilter P R G ∧ p ∈ G ∧ ∀ D ∈ F, ∃ q ∈ G, q ∈ D := by
  obtain ⟨s, hs, hs0, hmeet⟩ := internal_rasiowaSikorski_sequence_of_dependentChoice hDC hR hF hd hp
  refine ⟨internalSequenceFilter P R s, internalSequenceFilter_isFilter hR hs, ?_, ?_⟩
  · rw [← hs0]
    exact internalSequenceFilter_contains hR hs.1 (by simp)
  · intro D hD
    obtain ⟨n, hn, hnD⟩ := hmeet D hD
    exact ⟨s ‘ n, internalSequenceFilter_contains hR hs.1 hn, hnD⟩

theorem internal_rasiowaSikorski (hAC : InternalChoice V)
    {P R F p : V} (hR : IsForcingPreorder P R) (hF : IsInternallyCountable F)
    (hd : ∀ D ∈ F, ForcingDense P R D) (hp : p ∈ P) :
    ∃ G : V, IsForcingFilter P R G ∧ p ∈ G ∧ ∀ D ∈ F, ∃ q ∈ G, q ∈ D :=
  internal_rasiowaSikorski_of_dependentChoice (dependentChoice_of_internalChoice hAC) hR hF hd hp

end ZFVP
