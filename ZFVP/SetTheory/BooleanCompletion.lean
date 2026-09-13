import ZFVP.SetTheory.ForcingRegular
import ZFVP.SetTheory.ForcingNegation

/-! The Boolean completion of a forcing preorder: its regular subsets ordered by inclusion,
with intersection as meet, the forcing negation as complement and the regularization of a
union as join. The nonempty regular sets form a forcing poset into which the cones of
conditions embed densely. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The regular subsets of a forcing preorder. -/
noncomputable def regularSets (P R : V) : V := {A ∈ ℘ P ; IsForcingRegular P R A}

theorem mem_regularSets_iff (P R A : V) : A ∈ regularSets P R ↔ IsForcingRegular P R A := by
  unfold regularSets
  rw [mem_sep_iff, mem_power_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.1, h⟩⟩

instance regularSets_definable : ℒₛₑₜ-function₂[V] regularSets := by
  have hd : ℒₛₑₜ-relation₃[V] (fun S P R ↦ ∀ A, A ∈ S ↔ IsForcingRegular P R A) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = regularSets (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  exact ⟨fun h A ↦ (h A).trans (mem_regularSets_iff _ _ A),
    fun h A ↦ (h A).trans (mem_regularSets_iff _ _ A).symm⟩

/-- The nonzero regular sets: the conditions of the Boolean completion. -/
noncomputable def booleanConditions (P R : V) : V := {A ∈ regularSets P R ; ∃ p, p ∈ A}

theorem mem_booleanConditions_iff (P R A : V) :
    A ∈ booleanConditions P R ↔ IsForcingRegular P R A ∧ ∃ p, p ∈ A := by
  unfold booleanConditions
  rw [mem_sep_iff, mem_regularSets_iff]

instance booleanConditions_definable : ℒₛₑₜ-function₂[V] booleanConditions := by
  have hd : ℒₛₑₜ-relation₃[V] (fun S P R ↦ ∀ A, A ∈ S ↔ IsForcingRegular P R A ∧ ∃ p, p ∈ A) := by
    definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = booleanConditions (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  exact ⟨fun h A ↦ (h A).trans (mem_booleanConditions_iff _ _ A),
    fun h A ↦ (h A).trans (mem_booleanConditions_iff _ _ A).symm⟩

/-- Inclusion on the Boolean conditions. -/
noncomputable def booleanOrder (P R : V) : V :=
  {z ∈ booleanConditions P R ×ˢ booleanConditions P R ; kpair.π₁ z ⊆ kpair.π₂ z}

theorem kpair_mem_booleanOrder_iff (P R A C : V) :
    ⟨A, C⟩ₖ ∈ booleanOrder P R ↔ A ∈ booleanConditions P R ∧ C ∈ booleanConditions P R ∧ A ⊆ C := by
  unfold booleanOrder
  simp only [mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

instance booleanOrder_definable : ℒₛₑₜ-function₂[V] booleanOrder := by
  have hd : ℒₛₑₜ-relation₃[V] (fun S P R ↦ ∀ z, z ∈ S ↔
    z ∈ booleanConditions P R ×ˢ booleanConditions P R ∧ kpair.π₁ z ⊆ kpair.π₂ z) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = booleanOrder (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  exact ⟨fun h z ↦ (h z).trans (show z ∈ booleanOrder (v 1) (v 2) ↔ _ from mem_sep_iff),
    fun h z ↦ (h z).trans (show z ∈ booleanOrder (v 1) (v 2) ↔ _ from mem_sep_iff).symm⟩

theorem booleanOrder_poset (P R : V) : IsForcingPoset (booleanConditions P R) (booleanOrder P R) := by
  refine ⟨⟨sep_subset, fun A hA ↦ ?_, fun A hA C hC D hD hAC hCD ↦ ?_⟩, fun A hA C hC hAC hCA ↦ ?_⟩
  · exact (kpair_mem_booleanOrder_iff P R A A).mpr ⟨hA, hA, subset_refl _⟩
  · exact (kpair_mem_booleanOrder_iff P R A D).mpr ⟨hA, hD,
      subset_trans ((kpair_mem_booleanOrder_iff P R A C).mp hAC).2.2
        ((kpair_mem_booleanOrder_iff P R C D).mp hCD).2.2⟩
  · exact SetTheory.subset_antisymm ((kpair_mem_booleanOrder_iff P R A C).mp hAC).2.2
      ((kpair_mem_booleanOrder_iff P R C A).mp hCA).2.2

theorem top_mem_booleanConditions {P R : V} (hP : ∃ p, p ∈ P) : P ∈ booleanConditions P R :=
  (mem_booleanConditions_iff P R P).mpr ⟨forcingRegular_top P R, hP⟩

theorem booleanOrder_top {P R : V} (hP : ∃ p, p ∈ P) :
    IsForcingTop (booleanConditions P R) (booleanOrder P R) P :=
  ⟨top_mem_booleanConditions hP, fun A hA ↦ (kpair_mem_booleanOrder_iff P R A P).mpr
    ⟨hA, top_mem_booleanConditions hP, ((mem_booleanConditions_iff P R A).mp hA).1.1⟩⟩

/-- The regularization of a union: the join of a family of regular sets. -/
noncomputable def regularJoin (P R X : V) : V := forcingClosure P R (⋃ˢ X)

theorem forcingClosure_mono {P R A B : V} (h : A ⊆ B) : forcingClosure P R A ⊆ forcingClosure P R B := by
  intro p hp
  obtain ⟨hpP, hh⟩ := (mem_forcingClosure_iff P R A p).mp hp
  refine (mem_forcingClosure_iff P R B p).mpr ⟨hpP, fun q hq hqp ↦ ?_⟩
  obtain ⟨r, hr, hrq⟩ := hh q hq hqp
  exact ⟨r, h r hr, hrq⟩

theorem regularJoin_regular {P R X : V} (hR : IsForcingPreorder P R) (hX : ∀ A ∈ X, A ⊆ P) :
    IsForcingRegular P R (regularJoin P R X) :=
  forcingClosure_regular hR (fun p hp ↦ by
    obtain ⟨A, hA, hpA⟩ := mem_sUnion_iff.mp hp
    exact hX A hA p hpA)

theorem subset_regularJoin {P R X A : V} (hR : IsForcingPreorder P R) (hA : A ∈ X)
    (hreg : IsForcingRegular P R A) : A ⊆ regularJoin P R X :=
  subset_trans (subset_forcingClosure hR hreg.1 hreg.2.1)
    (forcingClosure_mono (subset_sUnion_of_mem hA))

theorem regularJoin_subset {P R X C : V} (hR : IsForcingPreorder P R) (hX : ∀ A ∈ X, A ⊆ C)
    (hC : IsForcingRegular P R C) : regularJoin P R X ⊆ C := by
  have h1 : ⋃ˢ X ⊆ C := fun p hp ↦ by
    obtain ⟨A, hA, hpA⟩ := mem_sUnion_iff.mp hp
    exact hX A hA p hpA
  intro p hp
  rw [← forcingClosure_eq hR hC]
  exact forcingClosure_mono h1 p hp

/-- A regular set is disjoint from its negation. -/
theorem inter_forcingNegation_eq_empty {P R A : V} (hR : IsForcingPreorder P R) (hA : A ⊆ P) :
    A ∩ forcingNegation P R A = ∅ := by
  ext p
  simp only [mem_inter_iff, not_mem_empty, iff_false, not_and]
  intro hpA hpn
  exact ((mem_forcingNegation_iff P R A p).mp hpn).2 p (hA p hpA) (hR.2.1 p (hA p hpA)) hpA

/-- The double negation of a regular set is itself. -/
theorem forcingNegation_negation {P R A : V} (hR : IsForcingPreorder P R)
    (hA : IsForcingRegular P R A) : forcingNegation P R (forcingNegation P R A) = A := by
  ext p
  rw [mem_forcingNegation_iff]
  constructor
  · rintro ⟨hpP, hh⟩
    apply hA.2.2 p hpP
    intro q hq hqp
    by_contra hnone
    push Not at hnone
    apply hh q hq hqp
    exact (mem_forcingNegation_iff P R A q).mpr ⟨hq, fun r hr hrq hrA ↦ hnone r hrA hrq⟩
  · intro hpA
    refine ⟨hA.1 p hpA, fun q hq hqp hqn ↦ ?_⟩
    have hqA : q ∈ A := hA.2.1 p hpA q hq hqp
    exact ((mem_forcingNegation_iff P R A q).mp hqn).2 q hq (hR.2.1 q hq) hqA

/-- A regular set and its negation join to the whole poset. -/
theorem regularJoin_negation {P R A : V} (hR : IsForcingPreorder P R) (hA : IsForcingRegular P R A) :
    regularJoin P R ({A, forcingNegation P R A} : V) = P := by
  apply SetTheory.subset_antisymm (forcingClosure_subset _ _ _)
  intro p hp
  refine (mem_forcingClosure_iff _ _ _ p).mpr ⟨hp, fun q hq _ ↦ ?_⟩
  by_cases hqA : q ∈ A
  · exact ⟨q, mem_sUnion_iff.mpr ⟨A, by simp, hqA⟩, hR.2.1 q hq⟩
  · obtain ⟨r, hr, hrq⟩ := exists_forcingNegation_of_not_mem hq hqA hA.2.2
    exact ⟨r, mem_sUnion_iff.mpr ⟨forcingNegation P R A, by simp, hr⟩, hrq⟩

/-- The regular cone of a condition. -/
noncomputable def coneRegular (P R p : V) : V := forcingClosure P R {q ∈ P ; ⟨q, p⟩ₖ ∈ R}

theorem mem_coneRegular_iff {P R p q : V} :
    q ∈ coneRegular P R p ↔ q ∈ P ∧ ∀ r ∈ P, ⟨r, q⟩ₖ ∈ R → ∃ s ∈ P, ⟨s, p⟩ₖ ∈ R ∧ ⟨s, r⟩ₖ ∈ R := by
  unfold coneRegular
  rw [mem_forcingClosure_iff]
  constructor
  · rintro ⟨hq, hh⟩
    refine ⟨hq, fun r hr hrq ↦ ?_⟩
    obtain ⟨s, hs, hsr⟩ := hh r hr hrq
    obtain ⟨hsP, hsp⟩ := mem_sep_iff.mp hs
    exact ⟨s, hsP, hsp, hsr⟩
  · rintro ⟨hq, hh⟩
    refine ⟨hq, fun r hr hrq ↦ ?_⟩
    obtain ⟨s, hsP, hsp, hsr⟩ := hh r hr hrq
    exact ⟨s, mem_sep_iff.mpr ⟨hsP, hsp⟩, hsr⟩

instance coneRegular_definable : ℒₛₑₜ-function₃[V] coneRegular := by
  have hd : ℒₛₑₜ-relation₄[V] (fun C P R p ↦ ∀ q, q ∈ C ↔ q ∈ P ∧
    ∀ r ∈ P, ⟨r, q⟩ₖ ∈ R → ∃ s ∈ P, ⟨s, p⟩ₖ ∈ R ∧ ⟨s, r⟩ₖ ∈ R) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = coneRegular (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  exact ⟨fun h q ↦ (h q).trans mem_coneRegular_iff, fun h q ↦ (h q).trans mem_coneRegular_iff.symm⟩

theorem coneRegular_regular {P R : V} (hR : IsForcingPreorder P R) (p : V) :
    IsForcingRegular P R (coneRegular P R p) :=
  forcingClosure_regular hR sep_subset

theorem self_mem_coneRegular {P R p : V} (hR : IsForcingPreorder P R) (hp : p ∈ P) :
    p ∈ coneRegular P R p :=
  mem_coneRegular_iff.mpr ⟨hp, fun r hr hrp ↦ ⟨r, hr, hrp, hR.2.1 r hr⟩⟩

theorem coneRegular_mem_booleanConditions {P R p : V} (hR : IsForcingPreorder P R) (hp : p ∈ P) :
    coneRegular P R p ∈ booleanConditions P R :=
  (mem_booleanConditions_iff P R _).mpr ⟨coneRegular_regular hR p, p, self_mem_coneRegular hR hp⟩

theorem coneRegular_subset_of_mem {P R A p : V} (hR : IsForcingPreorder P R)
    (hA : IsForcingRegular P R A) (hp : p ∈ A) : coneRegular P R p ⊆ A := by
  have hsub : {q ∈ P ; ⟨q, p⟩ₖ ∈ R} ⊆ A := fun q hq ↦
    hA.2.1 p hp q (mem_sep_iff.mp hq).1 (mem_sep_iff.mp hq).2
  intro q hq
  rw [← forcingClosure_eq hR hA]
  exact forcingClosure_mono hsub q hq

theorem coneRegular_mono {P R p q : V} (hR : IsForcingPreorder P R) (hp : p ∈ P) (hq : q ∈ P)
    (hqp : ⟨q, p⟩ₖ ∈ R) : coneRegular P R q ⊆ coneRegular P R p :=
  coneRegular_subset_of_mem hR (coneRegular_regular hR p)
    (mem_coneRegular_iff.mpr ⟨hq, fun r hr hrq ↦ ⟨r, hr, hR.2.2 r hr q hq p hp hrq hqp, hR.2.1 r hr⟩⟩)

/-- The cones are dense in the Boolean completion. -/
theorem coneRegular_dense {P R : V} (hR : IsForcingPreorder P R) :
    ForcingDense (booleanConditions P R) (booleanOrder P R)
      {C ∈ booleanConditions P R ; ∃ p ∈ P, C = coneRegular P R p} := by
  refine ⟨sep_subset, fun A hA ↦ ?_⟩
  obtain ⟨hAreg, p, hp⟩ := (mem_booleanConditions_iff P R A).mp hA
  have hpP : p ∈ P := hAreg.1 p hp
  refine ⟨coneRegular P R p, mem_sep_iff.mpr ⟨coneRegular_mem_booleanConditions hR hpP, p, hpP, rfl⟩, ?_⟩
  exact (kpair_mem_booleanOrder_iff P R _ A).mpr
    ⟨coneRegular_mem_booleanConditions hR hpP, hA, coneRegular_subset_of_mem hR hAreg hp⟩

end ZFVP
