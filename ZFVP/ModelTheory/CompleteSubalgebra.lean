import ZFVP.ModelTheory.SubposetRealization
import ZFVP.ModelTheory.BooleanValues
import ZFVP.SetTheory.RegularSetAlgebra

/-! Complete subalgebras `D` of the Boolean completion `RO(P)`: the trace of the generic on the
nonzero elements of `D` is generic for the sub-poset, so the intermediate extension `V[G ∩ D]`
is a forcing extension by `D` realized inside the Boolean extension. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A complete subalgebra of the regular sets: contains `P`, closed under negation and under
arbitrary regular joins. -/
def IsCompleteSubalgebra (P R D : V) : Prop :=
  D ⊆ regularSets P R ∧ P ∈ D ∧ (∀ A ∈ D, forcingNegation P R A ∈ D) ∧
    ∀ X, X ⊆ D → regularJoin P R X ∈ D

/-- The nonzero elements of a subalgebra: a sub-poset of the Boolean completion. -/
noncomputable def subalgebraConditions (P R D : V) : V := D ∩ booleanConditions P R

theorem mem_subalgebraConditions_iff (P R D A : V) :
    A ∈ subalgebraConditions P R D ↔ A ∈ D ∧ A ∈ booleanConditions P R := mem_inter_iff

theorem subalgebraConditions_subset (P R D : V) :
    subalgebraConditions P R D ⊆ booleanConditions P R := fun _ h ↦ (mem_inter_iff.mp h).2

section

variable {P R D : V} (hD : IsCompleteSubalgebra P R D)
include hD

theorem IsCompleteSubalgebra.regular {A : V} (hA : A ∈ D) : IsForcingRegular P R A :=
  (mem_regularSets_iff P R A).mp (hD.1 A hA)

theorem IsCompleteSubalgebra.inter_mem (hR : IsForcingPreorder P R) {A B : V} (hA : A ∈ D)
    (hB : B ∈ D) : A ∩ B ∈ D := by
  have hAr := hD.regular hA
  have hBr := hD.regular hB
  have hj : regularJoin P R ({forcingNegation P R A, forcingNegation P R B} : V) ∈ D := by
    apply hD.2.2.2
    intro C hC
    rcases mem_insert.mp hC with rfl | hC
    · exact hD.2.2.1 A hA
    · rw [mem_singleton_iff.mp hC]
      exact hD.2.2.1 B hB
  have := hD.2.2.1 _ hj
  rwa [← forcingNegation_inter hR hAr hBr, forcingNegation_negation hR (forcingRegular_inter hAr hBr)]
    at this

theorem IsCompleteSubalgebra.top_mem (hP : ∃ p, p ∈ P) : P ∈ subalgebraConditions P R D :=
  (mem_subalgebraConditions_iff _ _ _ _).mpr ⟨hD.2.1, top_mem_booleanConditions hP⟩

/-- A dense subset of the nonzero elements of a complete subalgebra joins to the top. -/
theorem IsCompleteSubalgebra.regularJoin_dense_eq_top (hR : IsForcingPreorder P R) {E : V}
    (hE : ForcingDense (subalgebraConditions P R D)
      (restrictedOrder (booleanOrder P R) (subalgebraConditions P R D)) E) :
    regularJoin P R E = P := by
  have hED : E ⊆ D := fun e he ↦ ((mem_subalgebraConditions_iff _ _ _ _).mp (hE.1 e he)).1
  have hEB : E ⊆ booleanConditions P R := fun e he ↦ subalgebraConditions_subset _ _ _ e (hE.1 e he)
  have hc : regularJoin P R E ∈ D := hD.2.2.2 E hED
  have hcr := hD.regular hc
  by_contra hne
  have hex : ∃ p ∈ P, p ∉ regularJoin P R E := by
    by_contra h
    push Not at h
    exact hne (SetTheory.subset_antisymm (regularJoin_subset_poset _ _ _) h)
  obtain ⟨p, hp, hpc⟩ := hex
  obtain ⟨q, hq, _⟩ := exists_forcingNegation_of_not_mem hp hpc hcr.2.2
  have hnD : forcingNegation P R (regularJoin P R E) ∈ subalgebraConditions P R D :=
    (mem_subalgebraConditions_iff _ _ _ _).mpr ⟨hD.2.2.1 _ hc,
      (mem_booleanConditions_iff _ _ _).mpr ⟨forcingNegation_regular hR hcr.2.1, q, hq⟩⟩
  obtain ⟨e, he, hen⟩ := hE.2 _ hnD
  obtain ⟨hen', _, _⟩ := (kpair_mem_restrictedOrder_iff _ _ _ _).mp hen
  obtain ⟨_, _, hesub⟩ := (kpair_mem_booleanOrder_iff _ _ _ _).mp hen'
  obtain ⟨r, hr⟩ := booleanConditions_nonempty (hEB e he)
  have h1 : r ∈ regularJoin P R E := subset_regularJoin_of_mem hR hEB he r hr
  have h2 : r ∈ forcingNegation P R (regularJoin P R E) := hesub r hr
  have : r ∈ regularJoin P R E ∩ forcingNegation P R (regularJoin P R E) := mem_inter_iff.mpr ⟨h1, h2⟩
  rw [inter_forcingNegation_eq_empty hR hcr.1] at this
  exact not_mem_empty this

/-- The trace of the Boolean generic on a complete subalgebra is generic for the subalgebra. -/
theorem IsCompleteSubalgebra.trace_generic (hR : IsForcingPreorder P R) {G : Set V}
    (hG : IsExternalForcingGeneric P R G) :
    IsExternalForcingGeneric (subalgebraConditions P R D)
      (restrictedOrder (booleanOrder P R) (subalgebraConditions P R D))
      (traceGeneric (booleanGeneric P R G) (subalgebraConditions P R D)) := by
  have hGB := booleanGeneric_generic hR hG
  refine ⟨⟨fun A hA ↦ hA.2, ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨p, hp⟩ := hG.1.2.1
    have hP : ∃ p, p ∈ P := ⟨p, hG.1.1 p hp⟩
    exact ⟨P, (mem_booleanGeneric_iff _ _ _ _).mpr ⟨top_mem_booleanConditions hP, p, hp, hG.1.1 p hp⟩,
      hD.top_mem hP⟩
  · rintro A ⟨hAG, _⟩ C hC hAC
    obtain ⟨hAC', _, _⟩ := (kpair_mem_restrictedOrder_iff _ _ _ _).mp hAC
    exact ⟨hGB.1.2.2.1 A hAG C (subalgebraConditions_subset _ _ _ C hC) hAC', hC⟩
  · rintro A ⟨hAG, hAD⟩ C ⟨hCG, hCD⟩
    obtain ⟨hAB, p, hp, hpA⟩ := (mem_booleanGeneric_iff _ _ _ _).mp hAG
    obtain ⟨hCB, q, hq, hqC⟩ := (mem_booleanGeneric_iff _ _ _ _).mp hCG
    obtain ⟨r, hr, hrp, hrq⟩ := hG.1.2.2.2 p hp q hq
    have hrP := hG.1.1 r hr
    have hrA : r ∈ A := (booleanConditions_regular hAB).2.1 p hpA r hrP hrp
    have hrC : r ∈ C := (booleanConditions_regular hCB).2.1 q hqC r hrP hrq
    have hAC : A ∩ C ∈ booleanConditions P R :=
      inter_mem_booleanConditions hAB hCB (mem_inter_iff.mpr ⟨hrA, hrC⟩)
    have hACD : A ∩ C ∈ subalgebraConditions P R D :=
      (mem_subalgebraConditions_iff _ _ _ _).mpr
        ⟨hD.inter_mem hR ((mem_subalgebraConditions_iff _ _ _ _).mp hAD).1
          ((mem_subalgebraConditions_iff _ _ _ _).mp hCD).1, hAC⟩
    refine ⟨A ∩ C, ⟨(mem_booleanGeneric_iff _ _ _ _).mpr ⟨hAC, r, hr, mem_inter_iff.mpr ⟨hrA, hrC⟩⟩,
      hACD⟩, ?_, ?_⟩
    · exact (kpair_mem_restrictedOrder_iff _ _ _ _).mpr
        ⟨(kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hAC, hAB, fun x hx ↦ (mem_inter_iff.mp hx).1⟩,
          hACD, hAD⟩
    · exact (kpair_mem_restrictedOrder_iff _ _ _ _).mpr
        ⟨(kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hAC, hCB, fun x hx ↦ (mem_inter_iff.mp hx).2⟩,
          hACD, hCD⟩
  · intro E hE
    have hEB : E ⊆ booleanConditions P R := fun e he ↦ subalgebraConditions_subset _ _ _ e (hE.1 e he)
    have htop := hD.regularJoin_dense_eq_top hR hE
    have hdense : ForcingDense P R (⋃ˢ E) := by
      refine ⟨fun p hp ↦ ?_, fun p hp ↦ ?_⟩
      · obtain ⟨e, he, hpe⟩ := mem_sUnion_iff.mp hp
        exact booleanConditions_subset (hEB e he) p hpe
      · have hp' : p ∈ regularJoin P R E := by rw [htop]; exact hp
        obtain ⟨_, hh⟩ := (mem_regularJoin_iff _ _ _ _).mp hp'
        obtain ⟨r, ⟨e, he, hre⟩, hrp⟩ := hh p hp (hR.2.1 p hp)
        exact ⟨r, mem_sUnion_iff.mpr ⟨e, he, hre⟩, hrp⟩
    obtain ⟨p, hp, hpE⟩ := hG.2 _ hdense
    obtain ⟨e, he, hpe⟩ := mem_sUnion_iff.mp hpE
    exact ⟨e, ⟨(mem_booleanGeneric_iff _ _ _ _).mpr ⟨hEB e he, p, hp, hpe⟩, hE.1 e he⟩, he⟩

end

namespace ForcingContext

variable (A : ForcingContext V) {D : V} (hD : IsCompleteSubalgebra A.P A.R D)

theorem subalgebraConditions_subset_boolean :
    subalgebraConditions A.P A.R D ⊆ A.booleanContext.P :=
  subalgebraConditions_subset A.P A.R D

include hD in
theorem top_mem_subalgebraConditions : A.booleanContext.one ∈ subalgebraConditions A.P A.R D :=
  hD.top_mem ⟨A.one, A.top.1⟩

/-- The forcing extension by a complete subalgebra of the Boolean completion. -/
noncomputable def subalgebraContext : ForcingContext V :=
  A.booleanContext.restrict (A.subalgebraConditions_subset_boolean (D := D))
    (A.top_mem_subalgebraConditions hD) (hD.trace_generic A.order A.generic)

theorem subalgebraContext_P : (A.subalgebraContext hD).P = subalgebraConditions A.P A.R D := rfl

/-- `V[G ∩ D]` realized inside the Boolean extension `V[G]`. -/
noncomputable def subalgebraRealization :
    ForcingRealization (A.subalgebraContext hD) A.booleanContext.Model :=
  A.booleanContext.restrictRealization (A.subalgebraConditions_subset_boolean (D := D))
    (A.top_mem_subalgebraConditions hD) (hD.trace_generic A.order A.generic)

/-- Membership in the intermediate extension `V[G ∩ D]`. -/
def InSubalgebraModel (x : A.booleanContext.Model) : Prop :=
  ∃ y, (A.subalgebraRealization hD).value y = x

theorem inSubalgebraModel_check (x : V) : A.InSubalgebraModel hD (A.booleanContext.check x) :=
  A.booleanContext.inRestrictedModel_check _ _ _ x

theorem inSubalgebraModel_of_mem {x y : A.booleanContext.Model} (hx : A.InSubalgebraModel hD x)
    (hy : y ∈ x) : A.InSubalgebraModel hD y :=
  A.booleanContext.inRestrictedModel_of_mem _ _ _ hx hy

end ForcingContext

end ZFVP
