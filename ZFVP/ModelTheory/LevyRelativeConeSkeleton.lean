import ZFVP.ModelTheory.LevyTraceProjection
import ZFVP.ModelTheory.LevyConePartitionData
import ZFVP.ModelTheory.BooleanConeCantorBernstein
import ZFVP.ModelTheory.BooleanAntichains

/-! Two steps toward a relative isomorphism of two cones of the Boolean completion of the Levy
collapse over the algebra `levyDeterminedAlgebra κ ξ` of sets determined below `ξ`.

* `levy_exists_common_cut`: two nonzero elements of the completion with the same trace have
  condition cones inside them given by conditions with the same part below `ξ`.

* `levy_relative_cone_isomorphic_of_dense`: if the two elements can be matched by an equivariant
  isomorphism over a dense set of determined pieces, then their cones are isomorphic by a single
  map that commutes with meeting every determined set.

The second proof takes a maximal antichain of determined pieces that carry such an isomorphism.
The antichain joins to the common trace, because a nonzero remainder would be a determined set
below the trace and the density hypothesis would extend the antichain. Meeting the antichain with
`u` and with `v` gives two cone partitions over the same index set, and
`exists_coneIsomorphism_of_conePartitions_equivariant` glues the piece isomorphisms, chosen with
`choice_for_definable_family`. The side clause of that gluing lemma, that a piece of `u` disjoint
from a determined `e` has partner disjoint from `e`, comes from `sb_piece_disjoint` applied to the
complement of `e`, which is again determined. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### A cut realized by both sides -/

/-- Two nonzero elements of the Boolean completion of `Coll(ω, <κ)` with the same trace over
`levyDeterminedAlgebra κ ξ` have condition cones inside them given by conditions with the same
part below `ξ`. -/
theorem levy_exists_common_cut {κ ξ u v : V} [IsOrdinal κ] (hξ : ξ ⊆ κ)
    (hu : u ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hv : v ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (htr : levyTrace κ ξ u = levyTrace κ ξ v) :
    ∃ r r', r ∈ levyCollapse κ ∧ r' ∈ levyCollapse κ ∧
      coneRegular (levyCollapse κ) (levyOrder κ) r ⊆ u ∧
      coneRegular (levyCollapse κ) (levyOrder κ) r' ⊆ v ∧
      levyCut ξ r = levyCut ξ r' := by
  obtain ⟨r, r', hr, hr', hcu, hcv, -, hcut⟩ :=
    levy_exists_swapPair_of_levyTrace_eq hξ hu hv htr
  exact ⟨r, r', hr, hr', hcu, hcv, hcut⟩

/-! ### Pieces carrying an equivariant isomorphism -/

/-- `h` is an isomorphism of the cone of `u ∩ d` onto the cone of `v ∩ d` in the Boolean
completion of `Coll(ω, <κ)` which commutes with meeting every set determined below `ξ`. -/
def IsLevyPieceIso (κ ξ u v d h : V) : Prop :=
  IsForcingIsomorphism (levyBoolCone κ (u ∩ d)) (levyBoolConeOrder κ (u ∩ d))
      (levyBoolCone κ (v ∩ d)) (levyBoolConeOrder κ (v ∩ d)) h ∧
    ∀ e, e ∈ levyDeterminedAlgebra κ ξ → ∀ x, x ∈ levyBoolCone κ (u ∩ d) →
      x ∩ e ≠ (∅ : V) → h ‘ (x ∩ e) = (h ‘ x) ∩ e

/-- The isomorphisms of the piece `d`, as a set. -/
noncomputable def levyPieceIsoSet (κ ξ u v d : V) : V :=
  sep (℘ (levyBoolCone κ (u ∩ d) ×ˢ levyBoolCone κ (v ∩ d)))
    (fun h ↦ IsLevyPieceIso κ ξ u v d h)
    (by unfold IsLevyPieceIso; definability)

theorem mem_levyPieceIsoSet_iff (κ ξ u v d h : V) :
    h ∈ levyPieceIsoSet κ ξ u v d ↔
      h ∈ ℘ (levyBoolCone κ (u ∩ d) ×ˢ levyBoolCone κ (v ∩ d)) ∧
        IsLevyPieceIso κ ξ u v d h := mem_sep_iff

instance levyPieceIsoSet_definable (κ ξ u v : V) :
    ℒₛₑₜ-function₁[V] (levyPieceIsoSet κ ξ u v) := by
  have hd : ℒₛₑₜ-relation[V] (fun S d ↦ ∀ h, h ∈ S ↔
      h ∈ ℘ (levyBoolCone κ (u ∩ d) ×ˢ levyBoolCone κ (v ∩ d)) ∧
        IsLevyPieceIso κ ξ u v d h) := by
    unfold IsLevyPieceIso
    definability
  apply Language.Definable.of_iff hd
  intro w
  change w 0 = levyPieceIsoSet κ ξ u v (w 1) ↔ _
  rw [mem_ext_iff]
  simp only [levyPieceIsoSet, mem_sep_iff]

/-- The determined pieces below the trace of `u` that carry an equivariant isomorphism of the
cone of their part of `u` onto the cone of their part of `v`. -/
noncomputable def levyGoodPieces (κ ξ u v : V) : V :=
  sep (levyDeterminedAlgebra κ ξ)
    (fun d ↦ d ⊆ levyTrace κ ξ u ∧ d ≠ (∅ : V) ∧
      ∃ h, h ∈ ℘ (levyBoolCone κ (u ∩ d) ×ˢ levyBoolCone κ (v ∩ d)) ∧
        IsLevyPieceIso κ ξ u v d h)
    (by unfold IsLevyPieceIso; definability)

theorem mem_levyGoodPieces_iff (κ ξ u v d : V) :
    d ∈ levyGoodPieces κ ξ u v ↔ d ∈ levyDeterminedAlgebra κ ξ ∧
      (d ⊆ levyTrace κ ξ u ∧ d ≠ (∅ : V) ∧
        ∃ h, h ∈ ℘ (levyBoolCone κ (u ∩ d) ×ˢ levyBoolCone κ (v ∩ d)) ∧
          IsLevyPieceIso κ ξ u v d h) := mem_sep_iff

/-! ### The glued isomorphism -/

/-- The side clause of the gluing lemma: an equivariant isomorphism of the cone of `u ∩ d` onto
the cone of `v ∩ d` cannot take a piece disjoint from a determined `e` to a piece meeting `e`. -/
theorem levy_piece_inter_eq_empty {κ ξ u v d e h : V}
    (hc : u ∩ d ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hb : v ∩ d ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hiso : IsLevyPieceIso κ ξ u v d h) (he : e ∈ levyDeterminedAlgebra κ ξ)
    (hud : (u ∩ d) ∩ e = (∅ : V)) : (v ∩ d) ∩ e = (∅ : V) := by
  have hR : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  have hereg : IsForcingRegular (levyCollapse κ) (levyOrder κ) e :=
    ((mem_levyDeterminedAlgebra_iff _ _ _).mp he).1
  have hneg : forcingNegation (levyCollapse κ) (levyOrder κ) e ∈ levyDeterminedAlgebra κ ξ :=
    (levyDeterminedAlgebra_isCompleteSubalgebra κ ξ).2.2.1 e he
  have hcc : u ∩ d ∈ levyBoolCone κ (u ∩ d) :=
    (mem_boolCone_sub_iff hc).mpr ⟨hc, subset_refl _⟩
  have htop : h ‘ (u ∩ d) = v ∩ d := glue_iso_top hc hb hiso.1
  have hstep := sb_piece_disjoint hR hc hb hiso.1 hereg
    (fun w hw hwn ↦ hiso.2 _ hneg w hw hwn) hcc hud
  rwa [htop] at hstep

set_option maxHeartbeats 2000000 in
/-- If two nonzero elements `u` and `v` of the completion with the same trace can be matched by an
equivariant isomorphism over a dense set of determined pieces, their cones are isomorphic by a
single map commuting with meeting every determined set. -/
theorem levy_relative_cone_isomorphic_of_dense {κ ξ u v : V} [IsOrdinal κ] (hAC : InternalChoice V)
    (hξ : ξ ⊆ κ)
    (hu : u ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hv : v ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (htr : levyTrace κ ξ u = levyTrace κ ξ v)
    (hdense : ∀ d', d' ∈ levyDeterminedAlgebra κ ξ → d' ⊆ levyTrace κ ξ u → d' ≠ (∅ : V) →
      ∃ d, d ∈ levyDeterminedAlgebra κ ξ ∧ d ⊆ d' ∧ d ≠ (∅ : V) ∧
        ∃ h, IsForcingIsomorphism
          (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ)) (u ∩ d))
          (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
            (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
              (booleanOrder (levyCollapse κ) (levyOrder κ)) (u ∩ d)))
          (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ)) (v ∩ d))
          (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
            (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
              (booleanOrder (levyCollapse κ) (levyOrder κ)) (v ∩ d))) h ∧
        ∀ e, e ∈ levyDeterminedAlgebra κ ξ → ∀ x, x ∈ forcingCone (booleanConditions (levyCollapse κ)
          (levyOrder κ)) (booleanOrder (levyCollapse κ) (levyOrder κ)) (u ∩ d) →
          x ∩ e ≠ (∅ : V) → h ‘ (x ∩ e) = (h ‘ x) ∩ e) :
    ∃ H, IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) u)
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) u))
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) v)
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) v)) H ∧
      ∀ e, e ∈ levyDeterminedAlgebra κ ξ → ∀ x, x ∈ forcingCone
        (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) u → x ∩ e ≠ (∅ : V) →
        H ‘ (x ∩ e) = (H ‘ x) ∩ e := by
  have hR : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  have hBpre : IsForcingPreorder (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) :=
    (booleanOrder_poset (levyCollapse κ) (levyOrder κ)).1
  have hureg : IsForcingRegular (levyCollapse κ) (levyOrder κ) u := booleanConditions_regular hu
  have hvreg : IsForcingRegular (levyCollapse κ) (levyOrder κ) v := booleanConditions_regular hv
  have hsalg : levyTrace κ ξ u ∈ levyDeterminedAlgebra κ ξ :=
    levyTrace_mem_levyDeterminedAlgebra hξ hureg.1
  have hsreg : IsForcingRegular (levyCollapse κ) (levyOrder κ) (levyTrace κ ξ u) :=
    levyTrace_regular κ ξ u
  have husub : u ⊆ levyTrace κ ξ u := subset_levyTrace hureg.1
  have hvsub : v ⊆ levyTrace κ ξ u := by
    rw [htr]
    exact subset_levyTrace hvreg.1
  -- the determined pieces below the trace that carry an equivariant isomorphism
  have hmemD : ∀ d : V, d ∈ levyGoodPieces κ ξ u v ↔ d ∈ levyDeterminedAlgebra κ ξ ∧
      (d ⊆ levyTrace κ ξ u ∧ d ≠ (∅ : V) ∧
        ∃ h, h ∈ ℘ (levyBoolCone κ (u ∩ d) ×ˢ levyBoolCone κ (v ∩ d)) ∧
          IsLevyPieceIso κ ξ u v d h) := mem_levyGoodPieces_iff κ ξ u v
  have hDsub : levyGoodPieces κ ξ u v ⊆
      booleanConditions (levyCollapse κ) (levyOrder κ) := by
    intro d hd
    obtain ⟨hdalg, -, hdne, -⟩ := (hmemD d).mp hd
    exact (mem_booleanConditions_iff _ _ _).mpr
      ⟨((mem_levyDeterminedAlgebra_iff _ _ _).mp hdalg).1,
        glue_exists_mem_of_ne_empty hdne⟩
  -- a determined piece produced by the density hypothesis lies in `Dset`
  have hdenseD : ∀ d', d' ∈ levyDeterminedAlgebra κ ξ → d' ⊆ levyTrace κ ξ u → d' ≠ (∅ : V) →
      ∃ d, d ∈ levyGoodPieces κ ξ u v ∧ d ⊆ d' := by
    intro d' hd' hd'sub hd'ne
    obtain ⟨d, hdalg, hdd', hdne, h, hiso, hequi⟩ := hdense d' hd' hd'sub hd'ne
    refine ⟨d, (hmemD d).mpr ⟨hdalg, subset_trans hdd' hd'sub, hdne,
      h, mem_power_iff.mpr (subset_prod_of_mem_function hiso.1), hiso, hequi⟩, hdd'⟩
  -- a maximal antichain of good pieces
  obtain ⟨I, hIanti, hID, hImax⟩ :=
    exists_maximalAntichain hBpre hDsub
      (wellOrderable_of_internalChoice hAC (levyGoodPieces κ ξ u v))
  have hIalg : ∀ i, i ∈ I → i ∈ levyDeterminedAlgebra κ ξ :=
    fun i hi ↦ ((hmemD i).mp (hID i hi)).1
  have hIsub : ∀ i, i ∈ I → i ⊆ levyTrace κ ξ u :=
    fun i hi ↦ ((hmemD i).mp (hID i hi)).2.1
  have hIB : ∀ i, i ∈ I → i ∈ booleanConditions (levyCollapse κ) (levyOrder κ) :=
    fun i hi ↦ hDsub i (hID i hi)
  have hIreg : ∀ i, i ∈ I → IsForcingRegular (levyCollapse κ) (levyOrder κ) i :=
    fun i hi ↦ booleanConditions_regular (hIB i hi)
  -- the antichain joins to the common trace
  have hJalg : regularJoin (levyCollapse κ) (levyOrder κ) I ∈ levyDeterminedAlgebra κ ξ :=
    (levyDeterminedAlgebra_isCompleteSubalgebra κ ξ).2.2.2 I hIalg
  have hJreg : IsForcingRegular (levyCollapse κ) (levyOrder κ)
      (regularJoin (levyCollapse κ) (levyOrder κ) I) :=
    ((mem_levyDeterminedAlgebra_iff _ _ _).mp hJalg).1
  have hJs : regularJoin (levyCollapse κ) (levyOrder κ) I ⊆ levyTrace κ ξ u :=
    regularJoin_subset hR hIsub hsreg
  have hjoin : regularJoin (levyCollapse κ) (levyOrder κ) I = levyTrace κ ξ u := by
    refine SetTheory.subset_antisymm hJs ?_
    have hrem : levyTrace κ ξ u ∩
        forcingNegation (levyCollapse κ) (levyOrder κ)
          (regularJoin (levyCollapse κ) (levyOrder κ) I) = (∅ : V) := by
      by_contra hne
      obtain ⟨z, hz⟩ := glue_exists_mem_of_ne_empty hne
      have hremalg : levyTrace κ ξ u ∩
          forcingNegation (levyCollapse κ) (levyOrder κ)
            (regularJoin (levyCollapse κ) (levyOrder κ) I) ∈ levyDeterminedAlgebra κ ξ :=
        inter_mem_levyDeterminedAlgebra hsalg
          ((levyDeterminedAlgebra_isCompleteSubalgebra κ ξ).2.2.1 _ hJalg)
      obtain ⟨d, hdD, hdrem⟩ := hdenseD _ hremalg (fun x hx ↦ (mem_inter_iff.mp hx).1) hne
      obtain ⟨a, haI, hcompat⟩ := hImax d hdD
      obtain ⟨p, hp⟩ := (boolean_compatible_iff (hIB a haI) (hDsub d hdD)).mp hcompat
      obtain ⟨hpa, hpd⟩ := mem_inter_iff.mp hp
      have hpJ : p ∈ regularJoin (levyCollapse κ) (levyOrder κ) I :=
        subset_regularJoin hR haI (hIreg a haI) p hpa
      exact forcingNegation_disjoint hR (mem_inter_iff.mp (hdrem p hpd)).2 hpJ
    exact sb_subset_of_inter_negation_empty hR hsreg hJreg hrem
  -- the pieces of `u` and of `v`
  have hIne : ∀ i, i ∈ I → ∃ x : V, x ∈ i :=
    fun i hi ↦ glue_exists_mem_of_ne_empty ((hmemD i).mp (hID i hi)).2.2.1
  have hIu : ∀ i, i ∈ I → u ∩ i ∈ booleanConditions (levyCollapse κ) (levyOrder κ) := by
    intro i hi
    obtain ⟨x, hx⟩ := levyTrace_of_nonempty_inter_determined (hIalg i hi) hureg
      (hIne i hi) (hIsub i hi)
    obtain ⟨hxi, hxu⟩ := mem_inter_iff.mp hx
    exact (mem_booleanConditions_iff _ _ _).mpr
      ⟨forcingRegular_inter hureg (hIreg i hi), x, mem_inter_iff.mpr ⟨hxu, hxi⟩⟩
  have hIv : ∀ i, i ∈ I → v ∩ i ∈ booleanConditions (levyCollapse κ) (levyOrder κ) := by
    intro i hi
    have hiv : i ⊆ levyTrace κ ξ v := by rw [← htr]; exact hIsub i hi
    obtain ⟨x, hx⟩ := levyTrace_of_nonempty_inter_determined (hIalg i hi) hvreg
      (hIne i hi) hiv
    obtain ⟨hxi, hxv⟩ := mem_inter_iff.mp hx
    exact (mem_booleanConditions_iff _ _ _).mpr
      ⟨forcingRegular_inter hvreg (hIreg i hi), x, mem_inter_iff.mpr ⟨hxv, hxi⟩⟩
  have hIdisj : ∀ i, i ∈ I → ∀ j, j ∈ I → i ≠ j → i ∩ j = (∅ : V) := by
    intro i hi j hj hij
    by_contra hne
    obtain ⟨x, hx⟩ := glue_exists_mem_of_ne_empty hne
    exact hIanti.2 i hi j hj hij ((boolean_compatible_iff (hIB i hi) (hIB j hj)).mpr ⟨x, hx⟩)
  -- the two cone partitions
  have hAdefin : ℒₛₑₜ-function₁[V] (fun d ↦ u ∩ d) := by definability
  have hBdefin : ℒₛₑₜ-function₁[V] (fun d ↦ v ∩ d) := by definability
  set A : V := definableGraph I (fun d ↦ u ∩ d) hAdefin with hAdef
  set B : V := definableGraph I (fun d ↦ v ∩ d) hBdefin with hBdef
  have hAval : ∀ i, i ∈ I → A ‘ i = u ∩ i :=
    fun i hi ↦ value_definableGraph I (fun d ↦ u ∩ d) hAdefin hi
  have hBval : ∀ i, i ∈ I → B ‘ i = v ∩ i :=
    fun i hi ↦ value_definableGraph I (fun d ↦ v ∩ d) hBdefin hi
  have hApart : IsConePartition (levyCollapse κ) (levyOrder κ) u I A := by
    refine ⟨definableGraph_isFunction _ _ _, domain_definableGraph _ _ _, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [hAval i hi]
      exact hIu i hi
    · intro i hi
      rw [hAval i hi]
      exact fun z hz ↦ (mem_inter_iff.mp hz).1
    · intro i hi j hj hij
      rw [hAval i hi, hAval j hj]
      refine glue_eq_empty_of_forall (fun z hz ↦ ?_)
      obtain ⟨hz1, hz2⟩ := mem_inter_iff.mp hz
      have : z ∈ i ∩ j :=
        mem_inter_iff.mpr ⟨(mem_inter_iff.mp hz1).2, (mem_inter_iff.mp hz2).2⟩
      rw [hIdisj i hi j hj hij] at this
      exact not_mem_empty this
    · rw [hAdef, range_definableGraph, ← inter_regularJoin hR hureg
        (fun C hC ↦ (hIreg C hC).1), hjoin]
      exact glue_inter_eq_left husub
  have hBpart : IsConePartition (levyCollapse κ) (levyOrder κ) v I B := by
    refine ⟨definableGraph_isFunction _ _ _, domain_definableGraph _ _ _, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [hBval i hi]
      exact hIv i hi
    · intro i hi
      rw [hBval i hi]
      exact fun z hz ↦ (mem_inter_iff.mp hz).1
    · intro i hi j hj hij
      rw [hBval i hi, hBval j hj]
      refine glue_eq_empty_of_forall (fun z hz ↦ ?_)
      obtain ⟨hz1, hz2⟩ := mem_inter_iff.mp hz
      have : z ∈ i ∩ j :=
        mem_inter_iff.mpr ⟨(mem_inter_iff.mp hz1).2, (mem_inter_iff.mp hz2).2⟩
      rw [hIdisj i hi j hj hij] at this
      exact not_mem_empty this
    · rw [hBdef, range_definableGraph, ← inter_regularJoin hR hvreg
        (fun C hC ↦ (hIreg C hC).1), hjoin]
      exact glue_inter_eq_left hvsub
  -- choose an isomorphism for every piece
  have hne : ∀ i ∈ I, IsNonempty (levyPieceIsoSet κ ξ u v i) := by
    intro i hi
    obtain ⟨-, -, -, h, hhp, hhiso⟩ := (hmemD i).mp (hID i hi)
    exact ⟨h, (mem_levyPieceIsoSet_iff κ ξ u v i h).mpr ⟨hhp, hhiso⟩⟩
  obtain ⟨F, hFfun, hFdom, hFval⟩ :=
    choice_for_definable_family hAC I (levyPieceIsoSet κ ξ u v)
      (levyPieceIsoSet_definable κ ξ u v) hne
  have hFiso : ∀ i, i ∈ I → IsLevyPieceIso κ ξ u v i (F ‘ i) :=
    fun i hi ↦ ((mem_levyPieceIsoSet_iff κ ξ u v i (F ‘ i)).mp (hFval i hi)).2
  -- glue
  refine exists_coneIsomorphism_of_conePartitions_equivariant hR hu hv hApart hBpart hFfun hFdom
    ?_ (fun d hd ↦ ((mem_levyDeterminedAlgebra_iff _ _ _).mp hd).1) ?_ ?_
  · intro i hi
    rw [hAval i hi, hBval i hi]
    exact (hFiso i hi).1
  · intro i hi e he hie
    rw [hAval i hi] at hie
    rw [hBval i hi]
    exact levy_piece_inter_eq_empty (hIu i hi) (hIv i hi) (hFiso i hi) he hie
  · intro i hi e he x hx hxe
    rw [hAval i hi] at hx
    exact (hFiso i hi).2 e he x hx hxe

end ZFVP
