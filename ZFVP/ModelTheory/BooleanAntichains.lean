import ZFVP.SetTheory.MaximalAntichains
import ZFVP.SetTheory.WellOrderingChoice
import ZFVP.SetTheory.RegularSetAlgebra
import ZFVP.SetTheory.BooleanCompletionValues
import ZFVP.ModelTheory.ForcingGeneric

/-! Maximal antichains of the Boolean completion `RO(P)` in the ground model: with choice, every
regular set is decided by one and every family of regular sets is refined by one (together with
the complement of its join); a `P`-generic filter meets every such antichain. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The maximal antichains of the Boolean completion. -/
noncomputable def boolMaximalAntichains (P R : V) : V :=
  {A ∈ ℘ (booleanConditions P R) ; IsForcingAntichain (booleanConditions P R) (booleanOrder P R) A ∧
    ∀ b ∈ booleanConditions P R, ∃ a ∈ A, ForcingCompatible (booleanConditions P R) (booleanOrder P R) a b}

theorem mem_boolMaximalAntichains_iff (P R A : V) :
    A ∈ boolMaximalAntichains P R ↔ A ⊆ booleanConditions P R ∧
      IsForcingAntichain (booleanConditions P R) (booleanOrder P R) A ∧
      ∀ b ∈ booleanConditions P R, ∃ a ∈ A, ForcingCompatible (booleanConditions P R) (booleanOrder P R) a b := by
  simp only [boolMaximalAntichains, mem_sep_iff, mem_power_iff]

/-- Compatibility in the Boolean completion is nonempty intersection. -/
theorem boolean_compatible_iff {P R a b : V} (ha : a ∈ booleanConditions P R) (hb : b ∈ booleanConditions P R) :
    ForcingCompatible (booleanConditions P R) (booleanOrder P R) a b ↔ ∃ p, p ∈ a ∩ b := by
  constructor
  · rintro ⟨c, hc, hca, hcb⟩
    obtain ⟨p, hp⟩ := booleanConditions_nonempty hc
    exact ⟨p, mem_inter_iff.mpr ⟨((kpair_mem_booleanOrder_iff _ _ _ _).mp hca).2.2 p hp,
      ((kpair_mem_booleanOrder_iff _ _ _ _).mp hcb).2.2 p hp⟩⟩
  · rintro ⟨p, hp⟩
    have hab := inter_mem_booleanConditions ha hb hp
    exact ⟨a ∩ b, hab, (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hab, ha, fun z hz ↦ (mem_inter_iff.mp hz).1⟩,
      (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hab, hb, fun z hz ↦ (mem_inter_iff.mp hz).2⟩⟩

/-- A maximal antichain inside a dense subset of the completion is a maximal antichain. -/
theorem maximalAntichainIn_dense_mem {P R D A : V} (hR : IsForcingPreorder P R)
    (hD : D ⊆ booleanConditions P R)
    (hdense : ∀ b ∈ booleanConditions P R, ∃ d ∈ D, d ⊆ b)
    (hA : IsMaximalAntichainIn (booleanConditions P R) (booleanOrder P R) D A) :
    A ∈ boolMaximalAntichains P R := by
  refine (mem_boolMaximalAntichains_iff _ _ _).mpr ⟨fun a ha ↦ hD a (hA.2.1 a ha), hA.1, ?_⟩
  intro b hb
  obtain ⟨d, hd, hdb⟩ := hdense b hb
  obtain ⟨a, ha, hc⟩ := hA.2.2 d hd
  have haB := hD a (hA.2.1 a ha)
  obtain ⟨p, hp⟩ := (boolean_compatible_iff haB (hD d hd)).mp hc
  exact ⟨a, ha, (boolean_compatible_iff haB hb).mpr
    ⟨p, mem_inter_iff.mpr ⟨(mem_inter_iff.mp hp).1, hdb p (mem_inter_iff.mp hp).2⟩⟩⟩

/-- Every regular set is decided by a maximal antichain. -/
theorem exists_deciding_antichain (hAC : InternalChoice V) {P R d : V} (hR : IsForcingPreorder P R)
    (hd : IsForcingRegular P R d) :
    ∃ A ∈ boolMaximalAntichains P R, ∀ a ∈ A, a ⊆ d ∨ a ⊆ forcingNegation P R d := by
  let D : V := {b ∈ booleanConditions P R ; b ⊆ d ∨ b ⊆ forcingNegation P R d}
  have hD : D ⊆ booleanConditions P R := fun b hb ↦ (mem_sep_iff.mp hb).1
  have hdense : ∀ b ∈ booleanConditions P R, ∃ d' ∈ D, d' ⊆ b := by
    intro b hb
    by_cases hbd : ∃ p, p ∈ b ∩ d
    · obtain ⟨p, hp⟩ := hbd
      have hbd' : b ∩ d ∈ booleanConditions P R :=
        (mem_booleanConditions_iff _ _ _).mpr ⟨forcingRegular_inter (booleanConditions_regular hb) hd, p, hp⟩
      exact ⟨b ∩ d, mem_sep_iff.mpr ⟨hbd', Or.inl (fun z hz ↦ (mem_inter_iff.mp hz).2)⟩,
        fun z hz ↦ (mem_inter_iff.mp hz).1⟩
    · refine ⟨b, mem_sep_iff.mpr ⟨hb, Or.inr ?_⟩, fun z hz ↦ hz⟩
      apply (subset_forcingNegation_iff hR (booleanConditions_regular hb) hd.1).mpr
      apply mem_ext
      intro p
      exact ⟨fun hp ↦ (hbd ⟨p, hp⟩).elim, fun hp ↦ (not_mem_empty hp).elim⟩
  obtain ⟨A, hA⟩ := exists_maximalAntichain (booleanOrder_poset P R).1 hD (wellOrderable_of_internalChoice hAC D)
  exact ⟨A, maximalAntichainIn_dense_mem hR hD hdense hA, fun a ha ↦ (mem_sep_iff.mp (hA.2.1 a ha)).2⟩

/-- Every family of regular sets is refined, together with the complement of its join, by a
maximal antichain. -/
theorem exists_refining_antichain (hAC : InternalChoice V) {P R Y : V} (hR : IsForcingPreorder P R)
    (hY : ∀ y ∈ Y, IsForcingRegular P R y) :
    ∃ A ∈ boolMaximalAntichains P R, ∀ a ∈ A,
      (∃ y ∈ Y, a ⊆ y) ∨ a ⊆ forcingNegation P R (regularJoin P R Y) := by
  let D : V := {b ∈ booleanConditions P R ; (∃ y ∈ Y, b ⊆ y) ∨ b ⊆ forcingNegation P R (regularJoin P R Y)}
  have hD : D ⊆ booleanConditions P R := fun b hb ↦ (mem_sep_iff.mp hb).1
  have hjoin : IsForcingRegular P R (regularJoin P R Y) := regularJoin_regular hR (fun y hy ↦ (hY y hy).1)
  have hdense : ∀ b ∈ booleanConditions P R, ∃ d' ∈ D, d' ⊆ b := by
    intro b hb
    have hbreg := booleanConditions_regular hb
    by_cases hbj : ∃ p, p ∈ b ∩ regularJoin P R Y
    · obtain ⟨p, hp⟩ := hbj
      obtain ⟨hpb, hpj⟩ := mem_inter_iff.mp hp
      have hpP : p ∈ P := hbreg.1 p hpb
      obtain ⟨_, hcl⟩ := (mem_forcingClosure_iff _ _ _ _).mp hpj
      obtain ⟨r, hr, hrp⟩ := hcl p hpP (hR.2.1 p hpP)
      obtain ⟨y, hy, hry⟩ := mem_sUnion_iff.mp hr
      have hrP : r ∈ P := (hY y hy).1 r hry
      have hrb : r ∈ b := hbreg.2.1 p hpb r hrP hrp
      have hby : b ∩ y ∈ booleanConditions P R :=
        (mem_booleanConditions_iff _ _ _).mpr ⟨forcingRegular_inter hbreg (hY y hy), r, mem_inter_iff.mpr ⟨hrb, hry⟩⟩
      exact ⟨b ∩ y, mem_sep_iff.mpr ⟨hby, Or.inl ⟨y, hy, fun z hz ↦ (mem_inter_iff.mp hz).2⟩⟩,
        fun z hz ↦ (mem_inter_iff.mp hz).1⟩
    · refine ⟨b, mem_sep_iff.mpr ⟨hb, Or.inr ?_⟩, fun z hz ↦ hz⟩
      apply (subset_forcingNegation_iff hR hbreg hjoin.1).mpr
      apply mem_ext
      intro p
      exact ⟨fun hp ↦ (hbj ⟨p, hp⟩).elim, fun hp ↦ (not_mem_empty hp).elim⟩
  obtain ⟨A, hA⟩ := exists_maximalAntichain (booleanOrder_poset P R).1 hD (wellOrderable_of_internalChoice hAC D)
  exact ⟨A, maximalAntichainIn_dense_mem hR hD hdense hA, fun a ha ↦ (mem_sep_iff.mp (hA.2.1 a ha)).2⟩

/-- A `P`-generic filter meets every maximal antichain of the completion. -/
theorem generic_meets_boolMaximalAntichain {P R A : V} {G : Set V} (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (hA : A ∈ boolMaximalAntichains P R) :
    ∃ a ∈ A, ∃ p ∈ G, p ∈ a := by
  obtain ⟨hAB, _, hmax⟩ := (mem_boolMaximalAntichains_iff _ _ _).mp hA
  have hdense : ForcingDense P R {q ∈ P ; ∃ a ∈ A, q ∈ a} := by
    refine ⟨fun q hq ↦ (mem_sep_iff.mp hq).1, fun p hp ↦ ?_⟩
    obtain ⟨a, ha, hc⟩ := hmax _ (coneRegular_mem_booleanConditions hR hp)
    obtain ⟨q, hq⟩ := (boolean_compatible_iff (hAB a ha) (coneRegular_mem_booleanConditions hR hp)).mp hc
    obtain ⟨hqa, hqc⟩ := mem_inter_iff.mp hq
    obtain ⟨hqP, hcone⟩ := mem_coneRegular_iff.mp hqc
    obtain ⟨s, hs, hsp, hsq⟩ := hcone q hqP (hR.2.1 q hqP)
    have hsa : s ∈ a := (booleanConditions_regular (hAB a ha)).2.1 q hqa s hs hsq
    exact ⟨s, mem_sep_iff.mpr ⟨hs, a, ha, hsa⟩, hsp⟩
  obtain ⟨p, hpG, hpD⟩ := hG.2 _ hdense
  obtain ⟨_, a, ha, hpa⟩ := mem_sep_iff.mp hpD
  exact ⟨a, ha, p, hpG, hpa⟩

end ZFVP
