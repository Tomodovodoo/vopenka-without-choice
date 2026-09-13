import ZFVP.ModelTheory.LevyRelativeSwapPair
import ZFVP.SetTheory.RegularSetAlgebra

/-! The algebra of the projection `levyTrace κ ξ`.

`levyTrace κ ξ b` (ZFVP/ModelTheory/LevyDeterminedTrace.lean) is the least member of the complete
subalgebra `levyDeterminedAlgebra κ ξ` above `b`. This file computes how it interacts with the
Boolean operations of that subalgebra:

* `levyTrace_eq_empty_iff`: the trace is empty only for the empty set.
* `levyTrace_inter_determined`: the trace commutes with meeting a determined set.
* `levyTrace_regularJoin`: the trace of a join of regular sets is the join of the traces.
* `levyTrace_inter_eq_empty_of_forall`: if `b` misses the trace of `b'` then the two traces are
  disjoint.
* `levyTrace_of_nonempty_inter_determined`: a nonzero determined set below the trace of `b` meets
  `b` itself. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Two facts about the ambient algebra -/

/-- A condition outside the negation of `A` has an extension in `A`. -/
theorem exists_mem_of_not_mem_forcingNegation {P R A q : V} (hq : q ∈ P)
    (h : q ∉ forcingNegation P R A) : ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ r ∈ A := by
  by_contra hcon
  exact h ((mem_forcingNegation_iff _ _ _ _).mpr
    ⟨hq, fun r hr hrq hrA ↦ hcon ⟨r, hr, hrq, hrA⟩⟩)

/-- The algebra of sets determined below `ξ` is closed under meets. -/
theorem inter_mem_levyDeterminedAlgebra {κ ξ d d' : V} (hd : d ∈ levyDeterminedAlgebra κ ξ)
    (hd' : d' ∈ levyDeterminedAlgebra κ ξ) : d ∩ d' ∈ levyDeterminedAlgebra κ ξ := by
  obtain ⟨hreg, hdet⟩ := (mem_levyDeterminedAlgebra_iff _ _ _).mp hd
  obtain ⟨hreg', hdet'⟩ := (mem_levyDeterminedAlgebra_iff _ _ _).mp hd'
  refine (mem_levyDeterminedAlgebra_iff _ _ _).mpr
    ⟨forcingRegular_inter hreg hreg', fun p hp ↦ ?_⟩
  simp only [mem_inter_iff]
  rw [hdet p hp, hdet' p hp]

/-! ### Membership in the trace, and its definability -/

theorem mem_levyTrace_iff {κ ξ b q : V} :
    q ∈ levyTrace κ ξ b ↔ q ∈ levyCollapse κ ∧ ∀ r ∈ levyCollapse κ,
      ⟨r, q⟩ₖ ∈ levyOrder κ →
        ∃ s, (s ∈ levyCollapse κ ∧ ∃ p ∈ b, levyCut ξ p ⊆ s) ∧ ⟨s, r⟩ₖ ∈ levyOrder κ := by
  unfold levyTrace
  rw [mem_forcingClosure_iff]
  simp only [mem_levyTraceBase_iff]

/-- The trace is a definable function of the set it is the trace of. -/
theorem levyTrace_definable (κ ξ : V) : ℒₛₑₜ-function₁[V] (levyTrace κ ξ) := by
  have h : ℒₛₑₜ-relation[V] (fun T b : V ↦ ∀ q, q ∈ T ↔ q ∈ levyCollapse κ ∧
      ∀ r ∈ levyCollapse κ, ⟨r, q⟩ₖ ∈ levyOrder κ →
        ∃ s, (s ∈ levyCollapse κ ∧ ∃ p ∈ b, levyCut ξ p ⊆ s) ∧ ⟨s, r⟩ₖ ∈ levyOrder κ) := by
    unfold levyCut
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = levyTrace κ ξ (v 1) ↔ _
  rw [mem_ext_iff]
  exact ⟨fun hh q ↦ (hh q).trans mem_levyTrace_iff, fun hh q ↦ (hh q).trans mem_levyTrace_iff.symm⟩

/-! ### The trace of the empty set -/

theorem levyTrace_empty (κ ξ : V) : levyTrace κ ξ (∅ : V) = (∅ : V) := by
  have hR : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  refine mem_ext (fun p ↦ ⟨fun hp ↦ ?_, fun hp ↦ (not_mem_empty hp).elim⟩)
  obtain ⟨hpP, hh⟩ := mem_levyTrace_iff.mp hp
  obtain ⟨s, ⟨-, q, hq, -⟩, -⟩ := hh p hpP (hR.2.1 p hpP)
  exact (not_mem_empty hq).elim

/-- The trace is empty only for the empty set. -/
theorem levyTrace_eq_empty_iff {κ ξ b : V} (hb : b ⊆ levyCollapse κ) :
    levyTrace κ ξ b = (∅ : V) ↔ b = (∅ : V) := by
  constructor
  · intro h
    refine subset_empty_iff_eq_empty.mp (fun p hp ↦ ?_)
    rw [← h]
    exact subset_levyTrace hb p hp
  · intro h
    rw [h, levyTrace_empty]

/-! ### The trace commutes with meeting a determined set -/

/-- The trace of `b ∩ d` for a determined `d` is the meet of the trace of `b` with `d`. -/
theorem levyTrace_inter_determined {κ ξ b d : V} (hξ : ξ ⊆ κ)
    (hb : IsForcingRegular (levyCollapse κ) (levyOrder κ) b)
    (hd : d ∈ levyDeterminedAlgebra κ ξ) :
    levyTrace κ ξ (b ∩ d) = levyTrace κ ξ b ∩ d := by
  have hR : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  have hdreg := ((mem_levyDeterminedAlgebra_iff _ _ _).mp hd).1
  have hbd : b ∩ d ⊆ levyCollapse κ := fun p hp ↦ hb.1 p (mem_inter_iff.mp hp).1
  have hT : levyTrace κ ξ (b ∩ d) ∈ levyDeterminedAlgebra κ ξ :=
    levyTrace_mem_levyDeterminedAlgebra hξ hbd
  have hTreg : IsForcingRegular (levyCollapse κ) (levyOrder κ) (levyTrace κ ξ (b ∩ d)) :=
    levyTrace_regular κ ξ (b ∩ d)
  have hNreg : IsForcingRegular (levyCollapse κ) (levyOrder κ)
      (forcingNegation (levyCollapse κ) (levyOrder κ) d) :=
    forcingNegation_regular hR hdreg.2.1
  apply SetTheory.subset_antisymm
  · refine levyTrace_subset_of_determined
      (inter_mem_levyDeterminedAlgebra (levyTrace_mem_levyDeterminedAlgebra hξ hb.1) hd)
      (fun p hp ↦ ?_)
    obtain ⟨hpb, hpd⟩ := mem_inter_iff.mp hp
    exact mem_inter_iff.mpr ⟨subset_levyTrace hb.1 p hpb, hpd⟩
  · have hX : ({forcingNegation (levyCollapse κ) (levyOrder κ) d,
        levyTrace κ ξ (b ∩ d)} : V) ⊆ levyDeterminedAlgebra κ ξ := by
      intro C hC
      rcases mem_insert.mp hC with rfl | hC
      · exact (levyDeterminedAlgebra_isCompleteSubalgebra κ ξ).2.2.1 d hd
      · rw [mem_singleton_iff.mp hC]
        exact hT
    have hEalg := (levyDeterminedAlgebra_isCompleteSubalgebra κ ξ).2.2.2 _ hX
    have hEreg := ((mem_levyDeterminedAlgebra_iff _ _ _).mp hEalg).1
    have hbE : b ⊆ regularJoin (levyCollapse κ) (levyOrder κ)
        ({forcingNegation (levyCollapse κ) (levyOrder κ) d, levyTrace κ ξ (b ∩ d)} : V) := by
      intro p hp
      refine hEreg.2.2 p (hb.1 p hp) (fun q hq hqp ↦ ?_)
      have hqb : q ∈ b := hb.2.1 p hp q hq hqp
      by_cases hqN : q ∈ forcingNegation (levyCollapse κ) (levyOrder κ) d
      · exact ⟨q, subset_regularJoin_pair_left hR hNreg q hqN, hR.2.1 q hq⟩
      · obtain ⟨r, hr, hrq, hrd⟩ := exists_mem_of_not_mem_forcingNegation hq hqN
        refine ⟨r, subset_regularJoin_pair_right hR hTreg r ?_, hrq⟩
        exact subset_levyTrace hbd r (mem_inter_iff.mpr ⟨hb.2.1 q hqb r hr hrq, hrd⟩)
    have hTb := levyTrace_subset_of_determined hEalg hbE
    intro x hx
    obtain ⟨hxT, hxd⟩ := mem_inter_iff.mp hx
    exact inter_regularJoin_negation_subset hR hdreg hTreg x
      (mem_inter_iff.mpr ⟨hxd, hTb x hxT⟩)

/-! ### The trace of a join -/

/-- The trace of a join of regular sets is the join of their traces. -/
theorem levyTrace_regularJoin {κ ξ X : V} (hξ : ξ ⊆ κ)
    (hX : ∀ A ∈ X, IsForcingRegular (levyCollapse κ) (levyOrder κ) A) :
    levyTrace κ ξ (regularJoin (levyCollapse κ) (levyOrder κ) X) =
      regularJoin (levyCollapse κ) (levyOrder κ)
        (repl (levyTrace κ ξ) (levyTrace_definable κ ξ) X) := by
  have hR : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  have hjsub : regularJoin (levyCollapse κ) (levyOrder κ) X ⊆ levyCollapse κ :=
    regularJoin_subset_poset _ _ _
  have himg : ∀ C ∈ repl (levyTrace κ ξ) (levyTrace_definable κ ξ) X,
      C ∈ levyDeterminedAlgebra κ ξ := by
    intro C hC
    obtain ⟨A, hA, rfl⟩ := (repl_spec _).mp hC
    exact levyTrace_mem_levyDeterminedAlgebra hξ (hX A hA).1
  have hJ : regularJoin (levyCollapse κ) (levyOrder κ)
      (repl (levyTrace κ ξ) (levyTrace_definable κ ξ) X) ∈ levyDeterminedAlgebra κ ξ :=
    (levyDeterminedAlgebra_isCompleteSubalgebra κ ξ).2.2.2 _ himg
  apply SetTheory.subset_antisymm
  · refine levyTrace_subset_of_determined hJ ?_
    refine regularJoin_subset hR (fun A hA ↦ ?_)
      ((mem_levyDeterminedAlgebra_iff _ _ _).mp hJ).1
    refine subset_trans (subset_levyTrace (κ := κ) (ξ := ξ) (hX A hA).1) ?_
    exact subset_regularJoin hR ((repl_spec _).mpr ⟨A, hA, rfl⟩) (levyTrace_regular κ ξ A)
  · refine regularJoin_subset hR (fun C hC ↦ ?_) (levyTrace_regular κ ξ _)
    obtain ⟨A, hA, rfl⟩ := (repl_spec _).mp hC
    exact levyTrace_mono hξ hjsub (subset_regularJoin hR hA (hX A hA))

/-! ### Disjointness -/

/-- If `b` misses the trace of `b'` then the two traces are disjoint. -/
theorem levyTrace_inter_eq_empty_of_forall {κ ξ b b' : V} (hξ : ξ ⊆ κ)
    (hb : IsForcingRegular (levyCollapse κ) (levyOrder κ) b)
    (hb' : IsForcingRegular (levyCollapse κ) (levyOrder κ) b')
    (h : b ∩ levyTrace κ ξ b' = (∅ : V)) :
    levyTrace κ ξ b ∩ levyTrace κ ξ b' = (∅ : V) := by
  have hkey := inter_determined_eq_empty_iff_levyTrace
    (levyTrace_mem_levyDeterminedAlgebra hξ hb'.1) hb.1 hb.2.1
  rw [SetTheory.inter_comm]
  refine hkey.mp ?_
  rw [SetTheory.inter_comm]
  exact h

/-- A nonzero determined set below the trace of `b` meets `b` itself. -/
theorem levyTrace_of_nonempty_inter_determined {κ ξ b d : V} (hd : d ∈ levyDeterminedAlgebra κ ξ)
    (hb : IsForcingRegular (levyCollapse κ) (levyOrder κ) b) (hne : ∃ x, x ∈ d)
    (hsub : d ⊆ levyTrace κ ξ b) : ∃ x, x ∈ d ∩ b := by
  by_contra hcon
  have hempty : d ∩ b = (∅ : V) := (eq_empty_iff_not_exists_mem _).mpr hcon
  have h2 := (inter_determined_eq_empty_iff_levyTrace hd hb.1 hb.2.1).mp hempty
  obtain ⟨x, hx⟩ := hne
  have : x ∈ d ∩ levyTrace κ ξ b := mem_inter_iff.mpr ⟨hx, hsub x hx⟩
  rw [h2] at this
  exact not_mem_empty this

end ZFVP
