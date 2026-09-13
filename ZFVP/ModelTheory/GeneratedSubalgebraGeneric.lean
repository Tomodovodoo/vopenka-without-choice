import ZFVP.ModelTheory.GeneratedSubalgebra
import ZFVP.ModelTheory.BooleanAntichains
import ZFVP.SetTheory.StageGenericUniqueness
import ZFVP.SetTheory.EndExtensionRegular
import ZFVP.SetTheory.ForcingNegationCalculus

/-! The generic ultrafilter on the checked Boolean completion inside `V[G]`, and the uniqueness
theorem: any antichain-generic ultrafilter of `V[G]` on the checked regular sets that agrees with
it on the generators agrees with it on the whole checked generated subalgebra. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

variable (A : ForcingContext V)

/-- The generic ultrafilter on the checked regular sets: those met by the generic. -/
noncomputable def boolGenericSet : A.Model :=
  {d ∈ A.check (regularSets A.P A.R) ; ∃ p ∈ A.genericSet, p ∈ d}

theorem check_mem_boolGenericSet_iff (d₀ : V) :
    A.check d₀ ∈ A.boolGenericSet ↔ d₀ ∈ regularSets A.P A.R ∧ ∃ p ∈ A.G, p ∈ d₀ := by
  unfold boolGenericSet
  rw [mem_sep_iff, A.check_mem_iff]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨p, hp, hpd⟩
    obtain ⟨p₀, hp₀, rfl⟩ := (A.mem_genericSet_iff p).mp hp
    exact ⟨p₀, hp₀, (A.check_mem_iff _ _).mp hpd⟩
  · rintro ⟨p₀, hp₀, hpd⟩
    exact ⟨A.check p₀, (A.check_mem_genericSet_iff p₀).mpr hp₀, (A.check_mem_iff _ _).mpr hpd⟩

theorem check_inter (x y : V) : A.check (x ∩ y) = A.check x ∩ A.check y :=
  A.checkEmbedding.map_inter x y

theorem check_insert (x y : V) : A.check (insert x y) = insert (A.check x) (A.check y) :=
  A.checkEmbedding.map_insert x y

/-- The Boolean generic set is an antichain-generic ultrafilter on the checked regular sets. -/
theorem boolGenericSet_antichainGeneric :
    IsAntichainGeneric (A.check (regularSets A.P A.R)) (A.check (boolMaximalAntichains A.P A.R))
      A.boolGenericSet := by
  refine ⟨fun d hd ↦ (mem_sep_iff.mp hd).1, ?_, ?_, ?_, ?_⟩
  · intro d hd d' hd' hsub
    obtain ⟨_, p, hp, hpd⟩ := mem_sep_iff.mp hd
    exact mem_sep_iff.mpr ⟨hd', p, hp, hsub p hpd⟩
  · intro d hd d' hd'
    obtain ⟨hdR, p, hp, hpd⟩ := mem_sep_iff.mp hd
    obtain ⟨hd'R, q, hq, hqd'⟩ := mem_sep_iff.mp hd'
    obtain ⟨d₀, hd₀, rfl⟩ := (A.mem_check_iff _ _).mp hdR
    obtain ⟨d₀', hd₀', rfl⟩ := (A.mem_check_iff _ _).mp hd'R
    obtain ⟨p₀, hp₀, rfl⟩ := (A.mem_genericSet_iff p).mp hp
    obtain ⟨q₀, hq₀, rfl⟩ := (A.mem_genericSet_iff q).mp hq
    obtain ⟨r₀, hr₀, hrp, hrq⟩ := A.generic.1.2.2.2 p₀ hp₀ q₀ hq₀
    have hr₀P : r₀ ∈ A.P := A.generic.1.1 r₀ hr₀
    have hreg := (mem_regularSets_iff _ _ _).mp hd₀
    have hreg' := (mem_regularSets_iff _ _ _).mp hd₀'
    have hrd : r₀ ∈ d₀ := hreg.2.1 p₀ ((A.check_mem_iff _ _).mp hpd) r₀ hr₀P hrp
    have hrd' : r₀ ∈ d₀' := hreg'.2.1 q₀ ((A.check_mem_iff _ _).mp hqd') r₀ hr₀P hrq
    rw [← A.check_inter]
    refine mem_sep_iff.mpr ⟨(A.check_mem_iff _ _).mpr ((mem_regularSets_iff _ _ _).mpr
      (forcingRegular_inter hreg hreg')), A.check r₀, (A.check_mem_genericSet_iff r₀).mpr hr₀, ?_⟩
    exact (A.check_mem_iff _ _).mpr (mem_inter_iff.mpr ⟨hrd, hrd'⟩)
  · intro h
    obtain ⟨_, p, _, hp⟩ := mem_sep_iff.mp h
    exact not_mem_empty hp
  · intro M hM
    obtain ⟨M₀, hM₀, rfl⟩ := (A.mem_check_iff _ _).mp hM
    obtain ⟨a₀, ha₀, p₀, hp₀, hpa⟩ := generic_meets_boolMaximalAntichain A.order A.generic hM₀
    have hAB := ((mem_boolMaximalAntichains_iff _ _ _).mp hM₀).1
    refine ⟨A.check a₀, (A.check_mem_iff _ _).mpr ha₀, (A.check_mem_boolGenericSet_iff a₀).mpr ⟨?_, p₀, hp₀, hpa⟩⟩
    exact (mem_regularSets_iff _ _ _).mpr (booleanConditions_regular (hAB a₀ ha₀))

theorem check_top_mem_boolGenericSet : A.check A.P ∈ A.boolGenericSet := by
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  exact (A.check_mem_boolGenericSet_iff _).mpr
    ⟨(mem_regularSets_iff _ _ _).mpr (forcingRegular_top _ _), p, hp, A.generic.1.1 p hp⟩

/-- Any antichain-generic ultrafilter contains the checked top. -/
theorem check_top_mem_of_antichainGeneric (hAC : InternalChoice V) {U : A.Model}
    (hU : IsAntichainGeneric (A.check (regularSets A.P A.R)) (A.check (boolMaximalAntichains A.P A.R)) U) :
    A.check A.P ∈ U := by
  obtain ⟨M₀, hM₀, hdec⟩ := exists_deciding_antichain hAC A.order (forcingRegular_top A.P A.R)
  obtain ⟨a, ha, haU⟩ := hU.meets (A.check M₀) ((A.check_mem_iff _ _).mpr hM₀)
  obtain ⟨a₀, ha₀, rfl⟩ := (A.mem_check_iff _ _).mp ha
  rcases hdec a₀ ha₀ with h | h
  · exact hU.upward _ haU _ ((A.check_mem_iff _ _).mpr ((mem_regularSets_iff _ _ _).mpr (forcingRegular_top _ _)))
      ((A.checkEmbedding.subset_iff _ _).mpr h)
  · exfalso
    rw [forcingNegation_top A.order] at h
    have ha₀e : a₀ = ∅ := by
      apply mem_ext
      intro z
      exact ⟨fun hz ↦ h z hz, fun hz ↦ (not_mem_empty hz).elim⟩
    rw [ha₀e, A.check_empty] at haU
    exact hU.proper haU

section

variable (hAC : InternalChoice V) {S : V} (hS : S ⊆ regularSets A.P A.R)

include hAC hS in
/-- The checked closure stages form a stage system inside `V[G]`. -/
theorem checkStageSystem :
    IsStageSystem (A.check A.P) (A.check A.R) (A.check (regularSets A.P A.R))
      (A.check (boolMaximalAntichains A.P A.R)) (A.check (℘ (regularSets A.P A.R)))
      (A.check (insert A.P S)) (A.check (closureStages A.P A.R (insert A.P S) (stageBound A.P A.R)))
      (A.check (stageBound A.P A.R)) := by
  let j := A.checkEmbedding
  let Cl := closureStages A.P A.R (insert A.P S) (stageBound A.P A.R)
  let θ := stageBound A.P A.R
  have hS' : insert A.P S ⊆ regularSets A.P A.R := by
    intro d hd
    rcases mem_insert.mp hd with h | hd
    · rw [h]
      exact (mem_regularSets_iff _ _ _).mpr (forcingRegular_top _ _)
    · exact hS d hd
  have hstage : ∀ α₀ ∈ θ, (A.check Cl) ‘ (A.check α₀) = A.check (Cl ‘ α₀) := by
    intro α₀ hα₀
    exact A.check_value (by rw [closureStages_domain]; exact hα₀)
  have hreg := closureStage_regular (θ := θ) A.order hS'
  have hneg : ∀ d₀ : V, forcingNegation (A.check A.P) (A.check A.R) (A.check d₀) =
      A.check (forcingNegation A.P A.R d₀) := fun d₀ ↦ (j.map_forcingNegation _ _ d₀).symm
  have hjoin : ∀ Y₀ : V, regularJoin (A.check A.P) (A.check A.R) (A.check Y₀) =
      A.check (regularJoin A.P A.R Y₀) := fun Y₀ ↦ (j.map_regularJoin _ _ Y₀).symm
  refine ⟨(A.check_ordinal_iff θ).mpr inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [A.check_domain, closureStages_domain]
  · intro d hd
    obtain ⟨d₀, hd₀, rfl⟩ := (A.mem_check_iff _ _).mp hd
    exact j.map_forcingRegular ((mem_regularSets_iff _ _ _).mp hd₀)
  · intro α hα
    obtain ⟨α₀, hα₀, rfl⟩ := (A.mem_check_iff _ _).mp hα
    rw [hstage α₀ hα₀]
    exact (j.subset_iff _ _).mpr (hreg α₀ hα₀)
  · exact (j.subset_iff _ _).mpr hS'
  · intro d hd
    obtain ⟨d₀, hd₀, rfl⟩ := (A.mem_check_iff _ _).mp hd
    rw [hneg]
    exact (A.check_mem_iff _ _).mpr ((mem_regularSets_iff _ _ _).mpr
      (forcingNegation_regular A.order ((mem_regularSets_iff _ _ _).mp hd₀).2.1))
  · intro Y hY
    obtain ⟨Y₀, hY₀, rfl⟩ := (A.mem_check_iff _ _).mp hY
    rw [hjoin]
    exact (A.check_mem_iff _ _).mpr ((mem_regularSets_iff _ _ _).mpr (regularJoin_regular A.order
      (fun y hy ↦ ((mem_regularSets_iff _ _ _).mp (mem_power_iff.mp hY₀ y hy)).1)))
  · intro α hα d hd
    obtain ⟨α₀, hα₀, rfl⟩ := (A.mem_check_iff _ _).mp hα
    rw [hstage α₀ hα₀] at hd
    obtain ⟨d₀, hd₀, rfl⟩ := (A.mem_check_iff _ _).mp hd
    rw [closureStages_value hα₀] at hd₀
    -- membership in the earlier stages, transported
    have hearlier : ∀ x₀ : V, x₀ ∈ insert A.P S ∪ ⋃ˢ range (Cl ↾ α₀) →
        A.check x₀ ∈ A.check (insert A.P S) ∨ ∃ β ∈ A.check α₀, A.check x₀ ∈ (A.check Cl) ‘ β := by
      intro x₀ hx₀
      rcases mem_union_iff.mp hx₀ with h | h
      · exact Or.inl ((A.check_mem_iff _ _).mpr h)
      · obtain ⟨X, hX, hxX⟩ := mem_sUnion_iff.mp h
        obtain ⟨β₀, hβ⟩ := mem_range_iff.mp hX
        obtain ⟨hβ, hβα⟩ := kpair_mem_restrict_iff.mp hβ
        have hβθ : β₀ ∈ θ := IsOrdinal.toIsTransitive.mem_trans hβα hα₀
        refine Or.inr ⟨A.check β₀, (A.check_mem_iff _ _).mpr hβα, ?_⟩
        rw [hstage β₀ hβθ, value_eq_of_kpair_mem hβ]
        exact (A.check_mem_iff _ _).mpr hxX
    have hearlier_reg : ∀ x₀ : V, x₀ ∈ insert A.P S ∪ ⋃ˢ range (Cl ↾ α₀) → x₀ ∈ regularSets A.P A.R := by
      intro x₀ hx₀
      rcases mem_union_iff.mp hx₀ with h | h
      · exact hS' x₀ h
      · obtain ⟨X, hX, hxX⟩ := mem_sUnion_iff.mp h
        obtain ⟨β₀, hβ⟩ := mem_range_iff.mp hX
        obtain ⟨hβ, hβα⟩ := kpair_mem_restrict_iff.mp hβ
        have hβθ : β₀ ∈ θ := IsOrdinal.toIsTransitive.mem_trans hβα hα₀
        rw [← value_eq_of_kpair_mem hβ] at hxX
        exact hreg β₀ hβθ x₀ hxX
    rcases (mem_subalgebraStep_iff _ _ _ _).mp hd₀ with h | ⟨A₀, hA₀, rfl⟩ | ⟨Y₀, hY₀, rfl⟩
    · rcases hearlier d₀ h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr (Or.inl ⟨A.check A₀, hearlier A₀ hA₀, ?_⟩))
      rw [hneg]
    · refine Or.inr (Or.inr (Or.inr ⟨A.check Y₀, (A.check_mem_iff _ _).mpr
        (mem_power_iff.mpr (fun y hy ↦ hearlier_reg y (hY₀ y hy))), ?_, ?_⟩))
      · intro y hy
        obtain ⟨y₀, hy₀, rfl⟩ := (A.mem_check_iff _ _).mp hy
        exact hearlier y₀ (hY₀ y₀ hy₀)
      · rw [hjoin]
  · intro d hd
    obtain ⟨d₀, hd₀, rfl⟩ := (A.mem_check_iff _ _).mp hd
    obtain ⟨M₀, hM₀, hdec⟩ := exists_deciding_antichain hAC A.order ((mem_regularSets_iff _ _ _).mp hd₀)
    refine ⟨A.check M₀, (A.check_mem_iff _ _).mpr hM₀, ?_⟩
    intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := (A.mem_check_iff _ _).mp ha
    rcases hdec a₀ ha₀ with h | h
    · exact Or.inl ((j.subset_iff _ _).mpr h)
    · right
      rw [hneg]
      exact (j.subset_iff _ _).mpr h
  · intro Y hY
    obtain ⟨Y₀, hY₀, rfl⟩ := (A.mem_check_iff _ _).mp hY
    have hY₀reg : ∀ y ∈ Y₀, IsForcingRegular A.P A.R y :=
      fun y hy ↦ (mem_regularSets_iff _ _ _).mp (mem_power_iff.mp hY₀ y hy)
    obtain ⟨M₀, hM₀, href⟩ := exists_refining_antichain hAC A.order hY₀reg
    refine ⟨A.check M₀, (A.check_mem_iff _ _).mpr hM₀, ?_⟩
    intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := (A.mem_check_iff _ _).mp ha
    rcases href a₀ ha₀ with ⟨y₀, hy₀, h⟩ | h
    · exact Or.inl ⟨A.check y₀, (A.check_mem_iff _ _).mpr hy₀, (j.subset_iff _ _).mpr h⟩
    · right
      rw [hjoin, hneg]
      exact (j.subset_iff _ _).mpr h

include hAC hS in
/-- Uniqueness: an antichain-generic ultrafilter of `V[G]` agreeing with the Boolean generic on the
checked generators agrees with it on the checked generated subalgebra. -/
theorem generatedSubalgebra_generic_unique {U : A.Model}
    (hU : IsAntichainGeneric (A.check (regularSets A.P A.R)) (A.check (boolMaximalAntichains A.P A.R)) U)
    (hagree : ∀ s ∈ A.check S, (s ∈ A.boolGenericSet ↔ s ∈ U)) :
    ∀ d ∈ A.check (generatedSubalgebra A.P A.R S), (d ∈ A.boolGenericSet ↔ d ∈ U) := by
  intro d hd
  obtain ⟨d₀, hd₀, rfl⟩ := (A.mem_check_iff _ _).mp hd
  obtain ⟨α₀, hα₀, hdα⟩ := (mem_generatedSubalgebra_iff _ _ _ _).mp hd₀
  have hsys := A.checkStageSystem hAC hS
  have hagree' : ∀ s ∈ A.check (insert A.P S), (s ∈ A.boolGenericSet ↔ s ∈ U) := by
    intro s hs
    rw [A.check_insert] at hs
    rcases mem_insert.mp hs with rfl | hs
    · exact ⟨fun _ ↦ A.check_top_mem_of_antichainGeneric hAC hU, fun _ ↦ A.check_top_mem_boolGenericSet⟩
    · exact hagree s hs
  have hα : A.check α₀ ∈ A.check (stageBound A.P A.R) := (A.check_mem_iff _ _).mpr hα₀
  have hstage : (A.check (closureStages A.P A.R (insert A.P S) (stageBound A.P A.R))) ‘ (A.check α₀) =
      A.check ((closureStages A.P A.R (insert A.P S) (stageBound A.P A.R)) ‘ α₀) :=
    A.check_value (by rw [closureStages_domain]; exact hα₀)
  have := stage_generic_unique (A.checkEmbedding.map_forcingPreorder A.order) hsys
    (A.boolGenericSet_antichainGeneric) hU hagree' (A.check α₀) hα (A.check d₀)
  rw [hstage] at this
  exact this ((A.check_mem_iff _ _).mpr hdα)

end

end ForcingContext

end ZFVP
