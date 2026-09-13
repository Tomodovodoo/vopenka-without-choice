import ZFVP.SetTheory.BooleanCompletion

/-! Every regular subset of the Boolean completion `B = RO(P)` (as a forcing poset) is principal:
it is the set of Boolean conditions below the regular join of its members. This identifies the
forcing values of the Boolean poset with elements of `B`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem booleanConditions_subset {P R A : V} (hA : A ∈ booleanConditions P R) : A ⊆ P :=
  ((mem_booleanConditions_iff P R A).mp hA).1.1

theorem booleanConditions_regular {P R A : V} (hA : A ∈ booleanConditions P R) :
    IsForcingRegular P R A :=
  ((mem_booleanConditions_iff P R A).mp hA).1

theorem booleanConditions_nonempty {P R A : V} (hA : A ∈ booleanConditions P R) : ∃ p, p ∈ A :=
  ((mem_booleanConditions_iff P R A).mp hA).2

/-- The intersection of two Boolean conditions with a common member is a Boolean condition. -/
theorem inter_mem_booleanConditions {P R A C p : V} (hA : A ∈ booleanConditions P R)
    (hC : C ∈ booleanConditions P R) (hp : p ∈ A ∩ C) : A ∩ C ∈ booleanConditions P R :=
  (mem_booleanConditions_iff P R _).mpr
    ⟨forcingRegular_inter (booleanConditions_regular hA) (booleanConditions_regular hC), p, hp⟩

/-- The members of a set of Boolean conditions are subsets of `P`. -/
theorem booleanSubset_members {P R S : V} (hS : S ⊆ booleanConditions P R) :
    ∀ A ∈ S, A ⊆ P := fun A hA ↦ booleanConditions_subset (hS A hA)

/-- The join of a set of Boolean conditions is a regular subset of `P`. -/
theorem regularJoin_booleanSubset_regular {P R S : V} (hR : IsForcingPreorder P R)
    (hS : S ⊆ booleanConditions P R) : IsForcingRegular P R (regularJoin P R S) :=
  regularJoin_regular hR (booleanSubset_members hS)

/-- Every member of a regular subset of the Boolean poset lies below the regular join. -/
theorem subset_regularJoin_of_mem {P R S A : V} (hR : IsForcingPreorder P R)
    (hS : S ⊆ booleanConditions P R) (hA : A ∈ S) : A ⊆ regularJoin P R S :=
  subset_regularJoin hR hA (booleanConditions_regular (hS A hA))

/-- Below a Boolean condition contained in the join of `S`, some member of `S` is cut out. -/
theorem exists_mem_below_of_subset_regularJoin {P R S A : V} (hR : IsForcingPreorder P R)
    (hS : S ⊆ booleanConditions P R) (hSd : IsForcingDownwardClosed (booleanConditions P R)
      (booleanOrder P R) S) (hA : A ∈ booleanConditions P R) (hAc : A ⊆ regularJoin P R S) :
    ∃ C ∈ S, C ⊆ A := by
  obtain ⟨p, hp⟩ := booleanConditions_nonempty hA
  have hpc := hAc p hp
  obtain ⟨hpP, hh⟩ := (mem_forcingClosure_iff _ _ _ _).mp hpc
  obtain ⟨r, hr, hrp⟩ := hh p hpP (hR.2.1 p hpP)
  obtain ⟨C, hC, hrC⟩ := mem_sUnion_iff.mp hr
  have hrA : r ∈ A := (booleanConditions_regular hA).2.1 p hp r
    ((booleanConditions_subset (hS C hC)) r hrC) hrp
  have hCA : C ∩ A ∈ booleanConditions P R :=
    inter_mem_booleanConditions (hS C hC) hA (mem_inter_iff.mpr ⟨hrC, hrA⟩)
  refine ⟨C ∩ A, hSd C hC (C ∩ A) hCA ?_, fun x hx ↦ (mem_inter_iff.mp hx).2⟩
  exact (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hCA, hS C hC, fun x hx ↦ (mem_inter_iff.mp hx).1⟩

/-- A regular subset of the Boolean poset is the principal set below its regular join. -/
theorem boolean_regular_eq_principal {P R S : V} (hR : IsForcingPreorder P R)
    (hS : IsForcingRegular (booleanConditions P R) (booleanOrder P R) S) :
    S = {A ∈ booleanConditions P R ; A ⊆ regularJoin P R S} := by
  ext A
  rw [mem_sep_iff]
  constructor
  · intro hA
    exact ⟨hS.1 A hA, subset_regularJoin_of_mem hR hS.1 hA⟩
  · rintro ⟨hA, hAc⟩
    apply hS.2.2 A hA
    intro C hC hCA
    obtain ⟨_, _, hCA'⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hCA
    obtain ⟨D, hD, hDC⟩ := exists_mem_below_of_subset_regularJoin hR hS.1 hS.2.1 hC
      (subset_trans hCA' hAc)
    exact ⟨D, hD, (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hS.1 D hD, hC, hDC⟩⟩

/-- The set of Boolean conditions below the join of a regular set is dense below every Boolean
condition contained in the join. -/
theorem boolean_regular_denseBelow {P R S A : V} (hR : IsForcingPreorder P R)
    (hS : IsForcingRegular (booleanConditions P R) (booleanOrder P R) S)
    (hA : A ∈ booleanConditions P R) (hAc : A ⊆ regularJoin P R S) :
    ForcingDenseBelow (booleanConditions P R) (booleanOrder P R) S A := by
  refine ⟨hS.1, fun C hC hCA ↦ ?_⟩
  obtain ⟨_, _, hCA'⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hCA
  obtain ⟨D, hD, hDC⟩ := exists_mem_below_of_subset_regularJoin hR hS.1 hS.2.1 hC
    (subset_trans hCA' hAc)
  exact ⟨D, hD, (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hS.1 D hD, hC, hDC⟩⟩

/-- The regular join of a nonempty set of Boolean conditions is a Boolean condition. -/
theorem regularJoin_mem_booleanConditions {P R S A : V} (hR : IsForcingPreorder P R)
    (hS : S ⊆ booleanConditions P R) (hA : A ∈ S) : regularJoin P R S ∈ booleanConditions P R := by
  obtain ⟨p, hp⟩ := booleanConditions_nonempty (hS A hA)
  exact (mem_booleanConditions_iff P R _).mpr
    ⟨regularJoin_booleanSubset_regular hR hS, p, subset_regularJoin_of_mem hR hS hA p hp⟩

end ZFVP
