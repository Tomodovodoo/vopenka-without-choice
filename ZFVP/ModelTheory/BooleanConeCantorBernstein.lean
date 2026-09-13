import ZFVP.ModelTheory.BooleanConePartitionGlue
import ZFVP.SetTheory.TransfiniteIteration

/-! The Schroeder-Bernstein theorem of Sikorski and Tarski for the complete Boolean algebra of
regular sets of a forcing preorder, in cone form.

If the cone of `a` is isomorphic to the cone of a condition `b₀ ⊆ b` and the cone of `b` is
isomorphic to the cone of a condition `a₀ ⊆ a`, then the cone of `a` is isomorphic to the cone
of `b`. The proof is the usual back and forth argument, carried out in the algebra: with
`φ = g ∘ f` and `A 0 = a − a₀`, `A (n+1) = φ (A n)`, the sets `A n` are pairwise disjoint,
`W = ⋁ₙ A n`, and `g` carries `b − f W` onto `c = a − W`. The pieces `A n` together with `c`
partition `a`, the pieces `f (A n)` together with `b − f W` partition `b`, and the two
partitions are matched by `f` on the `A n` and by the inverse of `g` on `c`. Gluing the piece
isomorphisms gives the theorem.

The countable joins are what makes this work; the Kinoshita counterexample is for Boolean
algebras without them and does not apply here.

The second theorem adds equivariance for a set `D` of regular sets closed under complements: if
`f` and `g` commute with meeting every `d ∈ D`, so does the isomorphism produced.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Relative complements in the algebra of regular sets -/

/-- A regular set disjoint from the negation of a regular set is included in it. -/
theorem sb_subset_of_inter_negation_empty {P R U W : V} (hR : IsForcingPreorder P R)
    (hU : IsForcingRegular P R U) (hW : IsForcingRegular P R W)
    (h : U ∩ forcingNegation P R W = (∅ : V)) : U ⊆ W := by
  have hs := (subset_forcingNegation_iff hR hU (forcingNegation_subset P R W)).mpr h
  rwa [forcingNegation_negation hR hW] at hs

/-- The relative complement of a regular set is regular. -/
theorem sb_relComp_regular {P R x W : V} (hR : IsForcingPreorder P R)
    (hx : IsForcingRegular P R x) (hW : IsForcingRegular P R W) :
    IsForcingRegular P R (x ∩ forcingNegation P R W) :=
  forcingRegular_inter hx (forcingNegation_regular hR hW.2.1)

/-- A regular set is disjoint from its relative complement. -/
theorem sb_relComp_disjoint {P R x W : V} (hR : IsForcingPreorder P R) (hW : W ⊆ P) :
    W ∩ (x ∩ forcingNegation P R W) = (∅ : V) := by
  refine glue_eq_empty_of_forall (fun z hz ↦ ?_)
  obtain ⟨hzW, hzx⟩ := mem_inter_iff.mp hz
  have : z ∈ W ∩ forcingNegation P R W :=
    mem_inter_iff.mpr ⟨hzW, (mem_inter_iff.mp hzx).2⟩
  rw [inter_forcingNegation_eq_empty hR hW] at this
  exact not_mem_empty this

/-- A regular set and its relative complement join to the whole. -/
theorem sb_relComp_join {P R x W : V} (hR : IsForcingPreorder P R)
    (hx : IsForcingRegular P R x) (hW : IsForcingRegular P R W) (hWx : W ⊆ x) :
    regularJoin P R ({W, x ∩ forcingNegation P R W} : V) = x := by
  have h := regularJoin_pair_split hR hx hW
  rw [inter_eq_right_of_subset hWx] at h
  exact h.symm

/-- The relative complement is the only complement. -/
theorem sb_relComp_unique {P R x W U : V} (hR : IsForcingPreorder P R)
    (hW : IsForcingRegular P R W) (hU : IsForcingRegular P R U) (hUx : U ⊆ x)
    (hdisj : U ∩ W = (∅ : V)) (hjoin : regularJoin P R ({W, U} : V) = x) :
    U = x ∩ forcingNegation P R W := by
  apply SetTheory.subset_antisymm
  · exact fun z hz ↦ mem_inter_iff.mpr
      ⟨hUx z hz, (subset_forcingNegation_iff hR hU hW.1).mpr hdisj z hz⟩
  · have hcomp : IsForcingRegular P R (x ∩ forcingNegation P R W) := by
      refine sb_relComp_regular hR ?_ hW
      rw [← hjoin]
      exact regularJoin_regular hR (fun C hC ↦ by
        rcases mem_insert.mp hC with rfl | hC
        · exact hW.1
        · rw [mem_singleton_iff.mp hC]; exact hU.1)
    have hdist := inter_regularJoin (A := x ∩ forcingNegation P R W) (X := ({W, U} : V)) hR hcomp
      (fun C hC ↦ by
        rcases mem_insert.mp hC with rfl | hC
        · exact hW.1
        · rw [mem_singleton_iff.mp hC]; exact hU.1)
    rw [hjoin, repl_pair] at hdist
    have h1 : (x ∩ forcingNegation P R W) ∩ W = (∅ : V) := by
      rw [glue_inter_comm]
      exact sb_relComp_disjoint hR hW.1
    have h2 : (x ∩ forcingNegation P R W) ∩ U ⊆ U := fun z hz ↦ (mem_inter_iff.mp hz).2
    rw [h1] at hdist
    have h3 : (x ∩ forcingNegation P R W) ∩ x = x ∩ forcingNegation P R W :=
      glue_inter_eq_left (fun z hz ↦ (mem_inter_iff.mp hz).1)
    rw [h3] at hdist
    rw [hdist, pair_comm_set]
    exact regularJoin_pair_subset hR hU h2 (empty_subset U)

/-- Everything is in the negation of the empty set. -/
theorem sb_mem_negation_empty {P R p : V} (hp : p ∈ P) :
    p ∈ forcingNegation P R (∅ : V) :=
  (mem_forcingNegation_iff _ _ _ _).mpr ⟨hp, fun _ _ _ hq ↦ not_mem_empty hq⟩

/-! ### Transport of the algebra along an isomorphism of cones -/

theorem sb_coneImageMap_definable (P R t f : V) :
    ℒₛₑₜ-function₁ (coneImage P R t f) := by
  unfold coneImage coneBelow
  definability

section Star

variable {P R t s f U W W' X : V}

/-- The image of the top is the top. -/
theorem sb_coneImage_top (ht : t ∈ booleanConditions P R) (hs : s ∈ booleanConditions P R)
    (hf : IsForcingIsomorphism (boolCone P R t) (boolConeOrder P R t)
      (boolCone P R s) (boolConeOrder P R s) f) : coneImage P R t f t = s := by
  have htt : t ∈ boolCone P R t := (mem_boolCone_sub_iff ht).mpr ⟨ht, subset_refl t⟩
  rw [coneImage_value hf htt]
  exact glue_iso_top ht hs hf

/-- The image of a regular subset of the top is regular and below the target top. -/
theorem sb_coneImage_reg (hR : IsForcingPreorder P R) (ht : t ∈ booleanConditions P R)
    (hf : IsForcingIsomorphism (boolCone P R t) (boolConeOrder P R t)
      (boolCone P R s) (boolConeOrder P R s) f)
    (hW : IsForcingRegular P R W) (hWt : W ⊆ t) :
    IsForcingRegular P R (coneImage P R t f W) ∧ coneImage P R t f W ⊆ s :=
  ⟨(coneImage_regular hR hf ht hW hWt).1, (coneImage_regular hR hf ht hW hWt).2.1⟩

/-- The image of a nonzero regular set is nonzero. -/
theorem sb_coneImage_ne_empty (hR : IsForcingPreorder P R) (ht : t ∈ booleanConditions P R)
    (hf : IsForcingIsomorphism (boolCone P R t) (boolConeOrder P R t)
      (boolCone P R s) (boolConeOrder P R s) f)
    (hW : IsForcingRegular P R W) (hWt : W ⊆ t) (hne : W ≠ (∅ : V)) :
    coneImage P R t f W ≠ (∅ : V) := by
  obtain ⟨q, hq⟩ := (coneImage_regular hR hf ht hW hWt).2.2 (glue_exists_mem_of_ne_empty hne)
  intro h
  rw [h] at hq
  exact not_mem_empty hq

/-- An isomorphism of cones takes disjoint regular sets to disjoint regular sets. -/
theorem sb_coneImage_disjoint (hR : IsForcingPreorder P R) (ht : t ∈ booleanConditions P R)
    (hs : s ∈ booleanConditions P R)
    (hf : IsForcingIsomorphism (boolCone P R t) (boolConeOrder P R t)
      (boolCone P R s) (boolConeOrder P R s) f)
    (hW : IsForcingRegular P R W) (hWt : W ⊆ t)
    (hW' : IsForcingRegular P R W') (hW't : W' ⊆ t) (hd : W ∩ W' = (∅ : V)) :
    coneImage P R t f W ∩ coneImage P R t f W' = (∅ : V) := by
  have hfi := isForcingIsomorphism_inverse hf
  have h1 := coneImage_regular hR hf ht hW hWt
  have h2 := coneImage_regular hR hf ht hW' hW't
  refine glue_eq_empty_of_forall (fun p hp ↦ ?_)
  obtain ⟨hp1, hp2⟩ := mem_inter_iff.mp hp
  have hpP : p ∈ P := h1.1.1 p hp1
  have hu1 : coneRegular P R p ⊆ coneImage P R t f W :=
    coneRegular_subset_of_mem hR h1.1 hp1
  have hu2 : coneRegular P R p ⊆ coneImage P R t f W' :=
    coneRegular_subset_of_mem hR h2.1 hp2
  have hureg : IsForcingRegular P R (coneRegular P R p) := coneRegular_regular hR p
  have hus : coneRegular P R p ⊆ s := subset_trans hu1 h1.2.1
  have hstep1 : coneImage P R s (converseGraph f) (coneRegular P R p) ⊆ W := by
    have := coneImage_mono (P := P) (R := R) (b0 := s) (f := converseGraph f) hu1
    rwa [coneImage_inverse_right hf ht hW hWt] at this
  have hstep2 : coneImage P R s (converseGraph f) (coneRegular P R p) ⊆ W' := by
    have := coneImage_mono (P := P) (R := R) (b0 := s) (f := converseGraph f) hu2
    rwa [coneImage_inverse_right hf ht hW' hW't] at this
  obtain ⟨q, hq⟩ := (coneImage_regular hR hfi hs hureg hus).2.2
    ⟨p, self_mem_coneRegular hR hpP⟩
  have : q ∈ W ∩ W' := mem_inter_iff.mpr ⟨hstep1 q hq, hstep2 q hq⟩
  rw [hd] at this
  exact not_mem_empty this

/-- An isomorphism of cones preserves arbitrary joins. -/
theorem sb_coneImage_join (hR : IsForcingPreorder P R) (ht : t ∈ booleanConditions P R)
    (hs : s ∈ booleanConditions P R)
    (hf : IsForcingIsomorphism (boolCone P R t) (boolConeOrder P R t)
      (boolCone P R s) (boolConeOrder P R s) f)
    (hX : ∀ C, C ∈ X → IsForcingRegular P R C ∧ C ⊆ t) :
    coneImage P R t f (regularJoin P R X) =
      regularJoin P R (repl (coneImage P R t f) (sb_coneImageMap_definable P R t f) X) := by
  have hfi := isForcingIsomorphism_inverse hf
  have htreg : IsForcingRegular P R t := booleanConditions_regular ht
  have hsreg : IsForcingRegular P R s := booleanConditions_regular hs
  have hJ : IsForcingRegular P R (regularJoin P R X) :=
    regularJoin_regular hR (fun C hC ↦ (hX C hC).1.1)
  have hJt : regularJoin P R X ⊆ t :=
    regularJoin_subset hR (fun C hC ↦ (hX C hC).2) htreg
  have hfJ := coneImage_regular hR hf ht hJ hJt
  have hmem : ∀ D, D ∈ repl (coneImage P R t f) (sb_coneImageMap_definable P R t f) X →
      IsForcingRegular P R D ∧ D ⊆ s := by
    intro D hD
    obtain ⟨C, hC, rfl⟩ := (repl_spec _).mp hD
    exact ⟨(coneImage_regular hR hf ht (hX C hC).1 (hX C hC).2).1,
      (coneImage_regular hR hf ht (hX C hC).1 (hX C hC).2).2.1⟩
  have hU : IsForcingRegular P R
      (regularJoin P R (repl (coneImage P R t f) (sb_coneImageMap_definable P R t f) X)) :=
    regularJoin_regular hR (fun D hD ↦ (hmem D hD).1.1)
  have hUs : regularJoin P R (repl (coneImage P R t f) (sb_coneImageMap_definable P R t f) X) ⊆ s :=
    regularJoin_subset hR (fun D hD ↦ (hmem D hD).2) hsreg
  apply SetTheory.subset_antisymm
  · have hback := coneImage_regular hR hfi hs hU hUs
    have hJin : regularJoin P R X ⊆
        coneImage P R s (converseGraph f)
          (regularJoin P R (repl (coneImage P R t f) (sb_coneImageMap_definable P R t f) X)) := by
      refine regularJoin_subset hR (fun C hC ↦ ?_) hback.1
      have hsub : coneImage P R t f C ⊆
          regularJoin P R (repl (coneImage P R t f) (sb_coneImageMap_definable P R t f) X) :=
        subset_regularJoin hR ((repl_spec _).mpr ⟨C, hC, rfl⟩)
          (coneImage_regular hR hf ht (hX C hC).1 (hX C hC).2).1
      have := coneImage_mono (P := P) (R := R) (b0 := s) (f := converseGraph f) hsub
      rwa [coneImage_inverse_right hf ht (hX C hC).1 (hX C hC).2] at this
    have hstep := coneImage_mono (P := P) (R := R) (b0 := t) (f := f) hJin
    rwa [coneImage_inverse_left hf hs hU hUs] at hstep
  · refine regularJoin_subset hR (fun D hD ↦ ?_) hfJ.1
    obtain ⟨C, hC, rfl⟩ := (repl_spec _).mp hD
    exact coneImage_mono (subset_regularJoin hR hC (hX C hC).1)

/-- An isomorphism of cones preserves relative complements. -/
theorem sb_coneImage_complement (hR : IsForcingPreorder P R) (ht : t ∈ booleanConditions P R)
    (hs : s ∈ booleanConditions P R)
    (hf : IsForcingIsomorphism (boolCone P R t) (boolConeOrder P R t)
      (boolCone P R s) (boolConeOrder P R s) f)
    (hW : IsForcingRegular P R W) (hWt : W ⊆ t) :
    coneImage P R t f (t ∩ forcingNegation P R W) =
      s ∩ forcingNegation P R (coneImage P R t f W) := by
  have htreg : IsForcingRegular P R t := booleanConditions_regular ht
  have hcomp : IsForcingRegular P R (t ∩ forcingNegation P R W) := sb_relComp_regular hR htreg hW
  have hcompt : t ∩ forcingNegation P R W ⊆ t := fun z hz ↦ (mem_inter_iff.mp hz).1
  have himg := coneImage_regular hR hf ht hW hWt
  have hcimg := coneImage_regular hR hf ht hcomp hcompt
  refine sb_relComp_unique hR himg.1 hcimg.1 hcimg.2.1 ?_ ?_
  · exact sb_coneImage_disjoint hR ht hs hf hcomp hcompt hW hWt (by
      rw [glue_inter_comm]
      exact sb_relComp_disjoint hR hW.1)
  · have hX : ∀ C, C ∈ ({W, t ∩ forcingNegation P R W} : V) →
        IsForcingRegular P R C ∧ C ⊆ t := by
      intro C hC
      rcases mem_insert.mp hC with rfl | hC
      · exact ⟨hW, hWt⟩
      · rw [mem_singleton_iff.mp hC]
        exact ⟨hcomp, hcompt⟩
    have hj := sb_coneImage_join hR ht hs hf hX
    rw [sb_relComp_join hR htreg hW hWt, sb_coneImage_top ht hs hf, repl_pair] at hj
    exact hj.symm

end Star

/-! ### Restricting a cone isomorphism to a subcone -/

/-- The restriction of a map of cones to the cone below a condition. -/
noncomputable def coneRestrict (P R x f : V) : V :=
  definableGraph (boolCone P R x) (fun z ↦ f ‘ z) (by definability)

theorem coneRestrict_value {P R x f z : V} (hz : z ∈ boolCone P R x) :
    (coneRestrict P R x f) ‘ z = f ‘ z :=
  value_definableGraph _ _ _ hz

section Restrict

variable {P R t s f x : V}

/-- The restriction of a cone isomorphism to the cone below a condition is an isomorphism onto
the cone below the image of that condition. -/
theorem sb_coneRestrict_iso (ht : t ∈ booleanConditions P R) (hs : s ∈ booleanConditions P R)
    (hf : IsForcingIsomorphism (boolCone P R t) (boolConeOrder P R t)
      (boolCone P R s) (boolConeOrder P R s) f)
    (hx : x ∈ boolCone P R t) :
    IsForcingIsomorphism (boolCone P R x) (boolConeOrder P R x)
      (boolCone P R (f ‘ x)) (boolConeOrder P R (f ‘ x)) (coneRestrict P R x f) := by
  have hfun : IsFunction f := IsFunction.of_mem hf.1
  have hfi := isForcingIsomorphism_inverse hf
  obtain ⟨hxB, hxt⟩ := (mem_boolCone_sub_iff ht).mp hx
  have hfx : f ‘ x ∈ boolCone P R s := function_value_mem hf.1 hx
  obtain ⟨hfxB, hfxs⟩ := (mem_boolCone_sub_iff hs).mp hfx
  have hcg : (converseGraph f) ‘ (f ‘ x) = x := converseGraph_value_value hf.1 hf.2.1 hx
  have hFP : ∀ z ∈ boolCone P R x, f ‘ z ∈ boolCone P R (f ‘ x) := by
    intro z hz
    obtain ⟨hzB, hzx⟩ := (mem_boolCone_sub_iff hxB).mp hz
    have hzt : z ∈ boolCone P R t :=
      (mem_boolCone_sub_iff ht).mpr ⟨hzB, subset_trans hzx hxt⟩
    exact (mem_boolCone_sub_iff hfxB).mpr
      ⟨((mem_boolCone_sub_iff hs).mp (function_value_mem hf.1 hzt)).1,
        (glue_iso_subset_iff ht hs hf hzt hx).mp hzx⟩
  have hGQ : ∀ w ∈ boolCone P R (f ‘ x), (converseGraph f) ‘ w ∈ boolCone P R x := by
    intro w hw
    obtain ⟨hwB, hwx⟩ := (mem_boolCone_sub_iff hfxB).mp hw
    have hws : w ∈ boolCone P R s :=
      (mem_boolCone_sub_iff hs).mpr ⟨hwB, subset_trans hwx hfxs⟩
    have hstep := (glue_iso_subset_iff hs ht hfi hws hfx).mp hwx
    rw [hcg] at hstep
    exact (mem_boolCone_sub_iff hxB).mpr
      ⟨((mem_boolCone_sub_iff ht).mp (function_value_mem hfi.1 hws)).1, hstep⟩
  have hGF : ∀ z ∈ boolCone P R x, (converseGraph f) ‘ (f ‘ z) = z := by
    intro z hz
    obtain ⟨hzB, hzx⟩ := (mem_boolCone_sub_iff hxB).mp hz
    exact converseGraph_value_value hf.1 hf.2.1
      ((mem_boolCone_sub_iff ht).mpr ⟨hzB, subset_trans hzx hxt⟩)
  have hFG : ∀ w ∈ boolCone P R (f ‘ x), f ‘ ((converseGraph f) ‘ w) = w := by
    intro w hw
    obtain ⟨hwB, hwx⟩ := (mem_boolCone_sub_iff hfxB).mp hw
    exact value_converseGraph_value hf.1 hf.2.1
      (hf.2.2.1.symm ▸ (mem_boolCone_sub_iff hs).mpr ⟨hwB, subset_trans hwx hfxs⟩)
  have hord : ∀ u ∈ boolCone P R x, ∀ v ∈ boolCone P R x,
      (⟨u, v⟩ₖ : V) ∈ boolConeOrder P R x ↔
        (⟨f ‘ u, f ‘ v⟩ₖ : V) ∈ boolConeOrder P R (f ‘ x) := by
    intro u hu v hv
    obtain ⟨huB, hux⟩ := (mem_boolCone_sub_iff hxB).mp hu
    obtain ⟨hvB, hvx⟩ := (mem_boolCone_sub_iff hxB).mp hv
    have hut : u ∈ boolCone P R t :=
      (mem_boolCone_sub_iff ht).mpr ⟨huB, subset_trans hux hxt⟩
    have hvt : v ∈ boolCone P R t :=
      (mem_boolCone_sub_iff ht).mpr ⟨hvB, subset_trans hvx hxt⟩
    have hfu := (mem_boolCone_sub_iff hfxB).mp (hFP u hu)
    have hfv := (mem_boolCone_sub_iff hfxB).mp (hFP v hv)
    rw [kpair_mem_boolConeOrder_iff hxB, kpair_mem_boolConeOrder_iff hfxB]
    constructor
    · rintro ⟨-, -, huv⟩
      exact ⟨hfu, hfv, (glue_iso_subset_iff ht hs hf hut hvt).mp huv⟩
    · rintro ⟨-, -, huv⟩
      exact ⟨⟨huB, hux⟩, ⟨hvB, hvx⟩, (glue_iso_subset_iff ht hs hf hut hvt).mpr huv⟩
  exact isForcingIsomorphism_of_inverse (fun z ↦ f ‘ z) (fun w ↦ (converseGraph f) ‘ w)
    (by definability) hFP hGQ hGF hFG hord

end Restrict

/-! ### Equivariance -/

section Equivariant

variable {P R c e f dd u y : V}

/-- The value of a cone isomorphism at a condition is a condition, so nonzero. -/
theorem sb_value_ne_empty (hf : IsForcingIsomorphism (boolCone P R c) (boolConeOrder P R c)
      (boolCone P R e) (boolConeOrder P R e) f) (hu : u ∈ boolCone P R c) :
    f ‘ u ≠ (∅ : V) := by
  intro h
  exact empty_not_mem_booleanConditions
    (h ▸ boolCone_subset P R e (f ‘ u) (function_value_mem hf.1 hu))

/-- A cone isomorphism commuting with meeting the complement of `dd` carries conditions
disjoint from `dd` to conditions disjoint from `dd`. -/
theorem sb_piece_disjoint (hR : IsForcingPreorder P R) (hc : c ∈ booleanConditions P R)
    (he : e ∈ booleanConditions P R)
    (hf : IsForcingIsomorphism (boolCone P R c) (boolConeOrder P R c)
      (boolCone P R e) (boolConeOrder P R e) f)
    (hdd : IsForcingRegular P R dd)
    (hequin : ∀ w, w ∈ boolCone P R c → w ∩ forcingNegation P R dd ≠ (∅ : V) →
      f ‘ (w ∩ forcingNegation P R dd) = (f ‘ w) ∩ forcingNegation P R dd)
    (hu : u ∈ boolCone P R c) (hud : u ∩ dd = (∅ : V)) : (f ‘ u) ∩ dd = (∅ : V) := by
  obtain ⟨huB, huc⟩ := (mem_boolCone_sub_iff hc).mp hu
  have hureg : IsForcingRegular P R u := booleanConditions_regular huB
  have husub : u ⊆ forcingNegation P R dd :=
    (subset_forcingNegation_iff hR hureg hdd.1).mpr hud
  have hun : u ∩ forcingNegation P R dd = u := glue_inter_eq_left husub
  have hune : u ∩ forcingNegation P R dd ≠ (∅ : V) := by
    rw [hun]
    intro h
    exact empty_not_mem_booleanConditions (h ▸ huB)
  have hkey := hequin u hu hune
  rw [hun] at hkey
  have hfuB := ((mem_boolCone_sub_iff he).mp (function_value_mem hf.1 hu)).1
  refine (subset_forcingNegation_iff hR (booleanConditions_regular hfuB) hdd.1).mp ?_
  rw [hkey]
  exact fun z hz ↦ (mem_inter_iff.mp hz).2

/-- The inverse of a cone isomorphism that commutes with meeting `dd` and with meeting the
complement of `dd` commutes with meeting `dd`. -/
theorem sb_inverse_equivariant (hR : IsForcingPreorder P R) (hc : c ∈ booleanConditions P R)
    (he : e ∈ booleanConditions P R)
    (hf : IsForcingIsomorphism (boolCone P R c) (boolConeOrder P R c)
      (boolCone P R e) (boolConeOrder P R e) f)
    (hdd : IsForcingRegular P R dd)
    (hequi : ∀ w, w ∈ boolCone P R c → w ∩ dd ≠ (∅ : V) →
      f ‘ (w ∩ dd) = (f ‘ w) ∩ dd)
    (hequin : ∀ w, w ∈ boolCone P R c → w ∩ forcingNegation P R dd ≠ (∅ : V) →
      f ‘ (w ∩ forcingNegation P R dd) = (f ‘ w) ∩ forcingNegation P R dd)
    (hy : y ∈ boolCone P R e) (hyd : y ∩ dd ≠ (∅ : V)) :
    (converseGraph f) ‘ (y ∩ dd) = ((converseGraph f) ‘ y) ∩ dd := by
  have hfun : IsFunction f := IsFunction.of_mem hf.1
  have hfi := isForcingIsomorphism_inverse hf
  have hu : (converseGraph f) ‘ y ∈ boolCone P R c := function_value_mem hfi.1 hy
  have hfu : f ‘ ((converseGraph f) ‘ y) = y :=
    value_converseGraph_value hf.1 hf.2.1 (hf.2.2.1.symm ▸ hy)
  obtain ⟨huB, huc⟩ := (mem_boolCone_sub_iff hc).mp hu
  have hud : ((converseGraph f) ‘ y) ∩ dd ≠ (∅ : V) := by
    intro h
    apply hyd
    have := sb_piece_disjoint hR hc he hf hdd hequin hu h
    rwa [hfu] at this
  have hmem : ((converseGraph f) ‘ y) ∩ dd ∈ boolCone P R c :=
    (mem_boolCone_sub_iff hc).mpr
      ⟨(mem_booleanConditions_iff _ _ _).mpr
        ⟨forcingRegular_inter (booleanConditions_regular huB) hdd,
          glue_exists_mem_of_ne_empty hud⟩,
        subset_trans (fun z hz ↦ (mem_inter_iff.mp hz).1) huc⟩
  have hkey := hequi ((converseGraph f) ‘ y) hu hud
  rw [hfu] at hkey
  rw [← hkey, converseGraph_value_value hf.1 hf.2.1 hmem]

end Equivariant

/-! ### The stages of the recursion -/

/-- One step of the recursion: the image under `g ∘ f`. -/
noncomputable def sbStep (P R a b f g x : V) : V := coneImage P R b g (coneImage P R a f x)

theorem sbStep_definable (P R a b f g : V) : ℒₛₑₜ-function₁ (sbStep P R a b f g) := by
  unfold sbStep coneImage coneBelow
  definability

/-- The stages `A 0 = a − a₀`, `A (n+1) = (g ∘ f) (A n)`. -/
noncomputable def sbStage (P R a a₀ b f g : V) : V → V :=
  iterate (sbStep P R a b f g) (sbStep_definable P R a b f g) (a ∩ forcingNegation P R a₀)

theorem sbStage_definable (P R a a₀ b f g : V) :
    ℒₛₑₜ-function₁ (sbStage P R a a₀ b f g) :=
  iterate_definable _ _

theorem sbStage_zero (P R a a₀ b f g : V) :
    sbStage P R a a₀ b f g (∅ : V) = a ∩ forcingNegation P R a₀ :=
  iterate_zero _ _

theorem sbStage_succ (P R a a₀ b f g : V) (n : V) [IsOrdinal n] :
    sbStage P R a a₀ b f g (succ n) = sbStep P R a b f g (sbStage P R a a₀ b f g n) :=
  iterate_succ _ _ _

/-- The data of the theorem: two cones, two conditions below them and two isomorphisms. -/
structure SBSetup (P R a b a₀ b₀ f g : V) : Prop where
  pre : IsForcingPreorder P R
  amem : a ∈ booleanConditions P R
  bmem : b ∈ booleanConditions P R
  a0mem : a₀ ∈ booleanConditions P R
  a0sub : a₀ ⊆ a
  b0mem : b₀ ∈ booleanConditions P R
  b0sub : b₀ ⊆ b
  fiso : IsForcingIsomorphism (boolCone P R a) (boolConeOrder P R a)
    (boolCone P R b₀) (boolConeOrder P R b₀) f
  giso : IsForcingIsomorphism (boolCone P R b) (boolConeOrder P R b)
    (boolCone P R a₀) (boolConeOrder P R a₀) g

namespace SBSetup

variable {P R a b a₀ b₀ f g : V}

theorem areg (H : SBSetup P R a b a₀ b₀ f g) : IsForcingRegular P R a :=
  booleanConditions_regular H.amem

theorem breg (H : SBSetup P R a b a₀ b₀ f g) : IsForcingRegular P R b :=
  booleanConditions_regular H.bmem

theorem a0reg (H : SBSetup P R a b a₀ b₀ f g) : IsForcingRegular P R a₀ :=
  booleanConditions_regular H.a0mem

theorem b0reg (H : SBSetup P R a b a₀ b₀ f g) : IsForcingRegular P R b₀ :=
  booleanConditions_regular H.b0mem

/-- The image of a regular subset of `a` under `f`. -/
theorem imageF (H : SBSetup P R a b a₀ b₀ f g) {W : V} (hW : IsForcingRegular P R W)
    (hWa : W ⊆ a) :
    IsForcingRegular P R (coneImage P R a f W) ∧ coneImage P R a f W ⊆ b₀ :=
  sb_coneImage_reg H.pre H.amem H.fiso hW hWa

/-- The image of a regular subset of `b` under `g`. -/
theorem imageG (H : SBSetup P R a b a₀ b₀ f g) {W : V} (hW : IsForcingRegular P R W)
    (hWb : W ⊆ b) :
    IsForcingRegular P R (coneImage P R b g W) ∧ coneImage P R b g W ⊆ a₀ :=
  sb_coneImage_reg H.pre H.bmem H.giso hW hWb

theorem stepReg (H : SBSetup P R a b a₀ b₀ f g) {W : V} (hW : IsForcingRegular P R W)
    (hWa : W ⊆ a) :
    IsForcingRegular P R (sbStep P R a b f g W) ∧ sbStep P R a b f g W ⊆ a₀ := by
  have h1 := H.imageF hW hWa
  exact H.imageG h1.1 (subset_trans h1.2 H.b0sub)

theorem stepMono {W W' : V} (h : W ⊆ W') : sbStep P R a b f g W ⊆ sbStep P R a b f g W' :=
  coneImage_mono (coneImage_mono h)

/-- The stages are regular subsets of `a`. -/
theorem stageReg (H : SBSetup P R a b a₀ b₀ f g) : ∀ n, n ∈ (ω : V) →
    IsForcingRegular P R (sbStage P R a a₀ b f g n) ∧ sbStage P R a a₀ b f g n ⊆ a := by
  have hdef := sbStage_definable P R a a₀ b f g
  apply naturalNumber_induction (fun n ↦ IsForcingRegular P R (sbStage P R a a₀ b f g n) ∧
    sbStage P R a a₀ b f g n ⊆ a) (by definability)
  · rw [zero_def, sbStage_zero]
    exact ⟨sb_relComp_regular H.pre H.areg H.a0reg, fun z hz ↦ (mem_inter_iff.mp hz).1⟩
  · intro n hn ih
    have : IsOrdinal n := IsOrdinal.of_mem hn
    rw [sbStage_succ]
    have h := H.stepReg ih.1 ih.2
    exact ⟨h.1, subset_trans h.2 H.a0sub⟩

/-- The stages after the first are below `a₀`. -/
theorem stageSuccSub (H : SBSetup P R a b a₀ b₀ f g) {n : V} (hn : n ∈ (ω : V)) :
    sbStage P R a a₀ b f g (succ n) ⊆ a₀ := by
  have : IsOrdinal n := IsOrdinal.of_mem hn
  rw [sbStage_succ]
  exact (H.stepReg (H.stageReg n hn).1 (H.stageReg n hn).2).2

/-- The step map takes disjoint regular subsets of `a` to disjoint sets. -/
theorem stepDisjoint (H : SBSetup P R a b a₀ b₀ f g) {W W' : V} (hW : IsForcingRegular P R W)
    (hWa : W ⊆ a) (hW' : IsForcingRegular P R W') (hW'a : W' ⊆ a) (hd : W ∩ W' = (∅ : V)) :
    sbStep P R a b f g W ∩ sbStep P R a b f g W' = (∅ : V) := by
  have h1 := H.imageF hW hWa
  have h2 := H.imageF hW' hW'a
  exact sb_coneImage_disjoint H.pre H.bmem H.a0mem H.giso h1.1
    (subset_trans h1.2 H.b0sub) h2.1 (subset_trans h2.2 H.b0sub)
    (sb_coneImage_disjoint H.pre H.amem H.b0mem H.fiso hW hWa hW' hW'a hd)

/-- The first stage is disjoint from `a₀`, hence from all later stages. -/
theorem stageZeroDisjoint (H : SBSetup P R a b a₀ b₀ f g) {n : V} (hn : n ∈ (ω : V)) :
    sbStage P R a a₀ b f g (∅ : V) ∩ sbStage P R a a₀ b f g (succ n) = (∅ : V) := by
  rw [sbStage_zero]
  refine glue_eq_empty_of_forall (fun z hz ↦ ?_)
  obtain ⟨hz1, hz2⟩ := mem_inter_iff.mp hz
  have hz0 : z ∈ a₀ := H.stageSuccSub hn z hz2
  have : z ∈ a₀ ∩ forcingNegation P R a₀ :=
    mem_inter_iff.mpr ⟨hz0, (mem_inter_iff.mp hz1).2⟩
  rw [inter_forcingNegation_eq_empty H.pre H.a0reg.1] at this
  exact not_mem_empty this

end SBSetup

/-- Every natural number is zero or a successor. -/
theorem sb_natural_cases : ∀ n, n ∈ (ω : V) → n = (∅ : V) ∨ ∃ m, m ∈ (ω : V) ∧ n = succ m := by
  apply naturalNumber_induction (fun n : V ↦ n = (∅ : V) ∨ ∃ m, m ∈ (ω : V) ∧ n = succ m)
    (by definability)
  · exact Or.inl zero_def
  · intro n hn _
    exact Or.inr ⟨n, hn, rfl⟩

namespace SBSetup

variable {P R a b a₀ b₀ f g : V}

/-- The stages are pairwise disjoint. -/
theorem stageDisjoint (H : SBSetup P R a b a₀ b₀ f g) : ∀ m, m ∈ (ω : V) → ∀ n, n ∈ (ω : V) →
    m ∈ n → sbStage P R a a₀ b f g m ∩ sbStage P R a a₀ b f g n = (∅ : V) := by
  have hdef := sbStage_definable P R a a₀ b f g
  apply naturalNumber_induction (fun m ↦ ∀ n, n ∈ (ω : V) → m ∈ n →
    sbStage P R a a₀ b f g m ∩ sbStage P R a a₀ b f g n = (∅ : V)) (by definability)
  · intro n hn hmn
    rcases sb_natural_cases n hn with rfl | ⟨k, hk, rfl⟩
    · exact absurd hmn not_mem_empty
    · exact H.stageZeroDisjoint hk
  · intro m hm ih n hn hmn
    rcases sb_natural_cases n hn with rfl | ⟨k, hk, rfl⟩
    · exact absurd hmn not_mem_empty
    · have : IsOrdinal m := IsOrdinal.of_mem hm
      have : IsOrdinal k := IsOrdinal.of_mem hk
      have hmk : m ∈ k := by
        rcases mem_succ_iff.mp hmn with h | h
        · exact h ▸ mem_succ_self m
        · exact IsOrdinal.toIsTransitive.mem_trans (mem_succ_self m) h
      rw [sbStage_succ, sbStage_succ]
      exact H.stepDisjoint (H.stageReg m hm).1 (H.stageReg m hm).2
        (H.stageReg k hk).1 (H.stageReg k hk).2 (ih k hk hmk)

end SBSetup

/-! ### The join of the stages and the residual piece -/

/-- The stages as a function on `ω`. -/
noncomputable def sbSeq (P R a a₀ b f g : V) : V :=
  definableGraph (ω : V) (sbStage P R a a₀ b f g) (sbStage_definable P R a a₀ b f g)

/-- The join of all stages. -/
noncomputable def sbJoin (P R a a₀ b f g : V) : V :=
  regularJoin P R (range (sbSeq P R a a₀ b f g))

theorem sb_mem_range_iff (P R a a₀ b f g C : V) :
    C ∈ range (sbSeq P R a a₀ b f g) ↔
      ∃ n, n ∈ (ω : V) ∧ C = sbStage P R a a₀ b f g n := by
  unfold sbSeq
  rw [range_definableGraph, repl_spec]

theorem sb_repl_repl (P R a b f g X : V) :
    repl (coneImage P R b g) (sb_coneImageMap_definable P R b g)
        (repl (coneImage P R a f) (sb_coneImageMap_definable P R a f) X)
      = repl (sbStep P R a b f g) (sbStep_definable P R a b f g) X := by
  apply mem_ext
  intro z
  simp only [repl_spec]
  constructor
  · rintro ⟨D, ⟨C, hC, rfl⟩, rfl⟩
    exact ⟨C, hC, rfl⟩
  · rintro ⟨C, hC, rfl⟩
    exact ⟨coneImage P R a f C, ⟨C, hC, rfl⟩, rfl⟩

namespace SBSetup

variable {P R a b a₀ b₀ f g : V}

theorem rangeReg (H : SBSetup P R a b a₀ b₀ f g) : ∀ C, C ∈ range (sbSeq P R a a₀ b f g) →
    IsForcingRegular P R C ∧ C ⊆ a := by
  intro C hC
  obtain ⟨n, hn, rfl⟩ := (sb_mem_range_iff _ _ _ _ _ _ _ _).mp hC
  exact H.stageReg n hn

theorem joinReg (H : SBSetup P R a b a₀ b₀ f g) :
    IsForcingRegular P R (sbJoin P R a a₀ b f g) ∧ sbJoin P R a a₀ b f g ⊆ a :=
  ⟨regularJoin_regular H.pre (fun C hC ↦ (H.rangeReg C hC).1.1),
    regularJoin_subset H.pre (fun C hC ↦ (H.rangeReg C hC).2) H.areg⟩

theorem stageSubJoin (H : SBSetup P R a b a₀ b₀ f g) {n : V} (hn : n ∈ (ω : V)) :
    sbStage P R a a₀ b f g n ⊆ sbJoin P R a a₀ b f g :=
  subset_regularJoin H.pre ((sb_mem_range_iff _ _ _ _ _ _ _ _).mpr ⟨n, hn, rfl⟩)
    (H.stageReg n hn).1

/-- The step map sends the join of the stages to the join of the later stages. -/
theorem stepJoin (H : SBSetup P R a b a₀ b₀ f g) :
    sbStep P R a b f g (sbJoin P R a a₀ b f g) =
      regularJoin P R (repl (sbStep P R a b f g) (sbStep_definable P R a b f g)
        (range (sbSeq P R a a₀ b f g))) := by
  have h1 := sb_coneImage_join H.pre H.amem H.b0mem H.fiso H.rangeReg
  have hY : ∀ D, D ∈ repl (coneImage P R a f) (sb_coneImageMap_definable P R a f)
      (range (sbSeq P R a a₀ b f g)) → IsForcingRegular P R D ∧ D ⊆ b := by
    intro D hD
    obtain ⟨C, hC, rfl⟩ := (repl_spec _).mp hD
    have h := H.imageF (H.rangeReg C hC).1 (H.rangeReg C hC).2
    exact ⟨h.1, subset_trans h.2 H.b0sub⟩
  have h2 := sb_coneImage_join H.pre H.bmem H.a0mem H.giso hY
  show coneImage P R b g (coneImage P R a f (sbJoin P R a a₀ b f g)) = _
  unfold sbJoin
  rw [h1, h2, sb_repl_repl]

/-- The join of the stages splits into the first stage and the image of the join. -/
theorem joinSplit (H : SBSetup P R a b a₀ b₀ f g) :
    regularJoin P R ({sbStage P R a a₀ b f g (∅ : V),
      sbStep P R a b f g (sbJoin P R a a₀ b f g)} : V) = sbJoin P R a a₀ b f g := by
  have hstep := H.stepJoin
  have hstepsub : sbStep P R a b f g (sbJoin P R a a₀ b f g) ⊆ sbJoin P R a a₀ b f g := by
    rw [hstep]
    refine regularJoin_subset H.pre (fun D hD ↦ ?_) H.joinReg.1
    obtain ⟨C, hC, rfl⟩ := (repl_spec _).mp hD
    obtain ⟨n, hn, rfl⟩ := (sb_mem_range_iff _ _ _ _ _ _ _ _).mp hC
    have : IsOrdinal n := IsOrdinal.of_mem hn
    rw [← sbStage_succ]
    exact H.stageSubJoin (ω_succ_closed hn)
  apply SetTheory.subset_antisymm
  · exact regularJoin_pair_subset H.pre H.joinReg.1 (H.stageSubJoin empty_mem_ω) hstepsub
  · have hpairreg : IsForcingRegular P R (regularJoin P R
        ({sbStage P R a a₀ b f g (∅ : V),
          sbStep P R a b f g (sbJoin P R a a₀ b f g)} : V)) := by
      refine regularJoin_regular H.pre (fun C hC ↦ ?_)
      rcases mem_insert.mp hC with rfl | hC
      · exact (H.stageReg _ empty_mem_ω).1.1
      · rw [mem_singleton_iff.mp hC]
        exact (H.stepReg H.joinReg.1 H.joinReg.2).1.1
    refine regularJoin_subset H.pre (fun C hC ↦ ?_) hpairreg
    obtain ⟨n, hn, rfl⟩ := (sb_mem_range_iff _ _ _ _ _ _ _ _).mp hC
    rcases sb_natural_cases n hn with rfl | ⟨m, hm, rfl⟩
    · exact subset_regularJoin_pair_left H.pre (H.stageReg _ empty_mem_ω).1
    · have : IsOrdinal m := IsOrdinal.of_mem hm
      rw [sbStage_succ]
      exact subset_trans (stepMono (H.stageSubJoin hm))
        (subset_regularJoin_pair_right H.pre (H.stepReg H.joinReg.1 H.joinReg.2).1)

/-- The complement of the first stage in `a` is `a₀`. -/
theorem negStageZero (H : SBSetup P R a b a₀ b₀ f g) :
    a ∩ forcingNegation P R (sbStage P R a a₀ b f g (∅ : V)) = a₀ := by
  rw [sbStage_zero]
  refine (sb_relComp_unique H.pre (sb_relComp_regular H.pre H.areg H.a0reg) H.a0reg H.a0sub
    (sb_relComp_disjoint H.pre H.a0reg.1) ?_).symm
  rw [pair_comm_set]
  exact sb_relComp_join H.pre H.areg H.a0reg H.a0sub

/-- The residual piece of `a` is the complement of the image of the join inside `a₀`. -/
theorem coneC (H : SBSetup P R a b a₀ b₀ f g) :
    a ∩ forcingNegation P R (sbJoin P R a a₀ b f g) =
      a₀ ∩ forcingNegation P R (sbStep P R a b f g (sbJoin P R a a₀ b f g)) := by
  have hpairreg : ∀ C, C ∈ ({sbStage P R a a₀ b f g (∅ : V),
      sbStep P R a b f g (sbJoin P R a a₀ b f g)} : V) → IsForcingRegular P R C := by
    intro C hC
    rcases mem_insert.mp hC with rfl | hC
    · exact (H.stageReg _ empty_mem_ω).1
    · rw [mem_singleton_iff.mp hC]
      exact (H.stepReg H.joinReg.1 H.joinReg.2).1
  have hzero : sbStage P R a a₀ b f g (∅ : V) ∈ ({sbStage P R a a₀ b f g (∅ : V),
      sbStep P R a b f g (sbJoin P R a a₀ b f g)} : V) := mem_insert.mpr (Or.inl rfl)
  have hone : sbStep P R a b f g (sbJoin P R a a₀ b f g) ∈
      ({sbStage P R a a₀ b f g (∅ : V),
        sbStep P R a b f g (sbJoin P R a a₀ b f g)} : V) :=
    mem_insert.mpr (Or.inr (mem_singleton_iff.mpr rfl))
  apply mem_ext
  intro p
  constructor
  · intro hp
    obtain ⟨hpa, hpn⟩ := mem_inter_iff.mp hp
    rw [← H.joinSplit, mem_forcingNegation_regularJoin_iff H.pre hpairreg] at hpn
    have hp0 : p ∈ a₀ := by
      rw [← H.negStageZero]
      exact mem_inter_iff.mpr ⟨hpa, hpn.2 _ hzero⟩
    exact mem_inter_iff.mpr ⟨hp0, hpn.2 _ hone⟩
  · intro hp
    obtain ⟨hp0, hpn⟩ := mem_inter_iff.mp hp
    rw [← H.negStageZero] at hp0
    obtain ⟨hpa, hpn0⟩ := mem_inter_iff.mp hp0
    refine mem_inter_iff.mpr ⟨hpa, ?_⟩
    rw [← H.joinSplit, mem_forcingNegation_regularJoin_iff H.pre hpairreg]
    refine ⟨H.areg.1 p hpa, fun C hC ↦ ?_⟩
    rcases mem_insert.mp hC with rfl | hC
    · exact hpn0
    · rw [mem_singleton_iff.mp hC]
      exact hpn

/-- The image under `g` of the residual piece of `b` is the residual piece of `a`. -/
theorem gResidual (H : SBSetup P R a b a₀ b₀ f g) :
    coneImage P R b g (b ∩ forcingNegation P R
        (coneImage P R a f (sbJoin P R a a₀ b f g))) =
      a ∩ forcingNegation P R (sbJoin P R a a₀ b f g) := by
  have hWb := H.imageF H.joinReg.1 H.joinReg.2
  have h := sb_coneImage_complement H.pre H.bmem H.a0mem H.giso hWb.1
    (subset_trans hWb.2 H.b0sub)
  rw [h]
  exact H.coneC.symm

end SBSetup

/-! ### The two matched partitions -/

open scoped Classical

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
/-- A definable map with one value changed is definable. -/
theorem sb_if_definable {F : V → V} (hF : ℒₛₑₜ-function₁ F) (w c : V) :
    ℒₛₑₜ-function₁ (fun i : V ↦ if i = w then c else F i) := by
  classical
  have h : ℒₛₑₜ-relation (fun y i : V ↦ (i = w ∧ y = c) ∨ (i ≠ w ∧ y = F i)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = (if v 1 = w then c else F (v 1)) ↔ _
  by_cases hc : v 1 = w
  · simp [hc]
  · simp [hc]

theorem coneRestrict_mem_iff (P R x f z : V) :
    z ∈ coneRestrict P R x f ↔ ∃ u, u ∈ boolCone P R x ∧ z = ⟨u, f ‘ u⟩ₖ := by
  unfold coneRestrict
  rw [mem_definableGraph_iff]

theorem coneRestrictMap_definable (P R f : V) :
    ℒₛₑₜ-function₁ (fun x : V ↦ coneRestrict P R x f) := by
  have h : ℒₛₑₜ-relation (fun y x : V ↦ ∀ z, z ∈ y ↔ ∃ u, u ∈ boolCone P R x ∧ z = ⟨u, f ‘ u⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = coneRestrict P R (v 1) f ↔ _
  rw [mem_ext_iff]
  simp only [coneRestrict_mem_iff]

/-- The restriction of an equivariant cone map to a subcone is equivariant. -/
theorem sb_restrict_equivariant {P R t x f dd : V} (ht : t ∈ booleanConditions P R)
    (hx : x ∈ boolCone P R t) (hdd : IsForcingRegular P R dd)
    (hequi : ∀ w, w ∈ boolCone P R t → w ∩ dd ≠ (∅ : V) → f ‘ (w ∩ dd) = (f ‘ w) ∩ dd) :
    ∀ w, w ∈ boolCone P R x → w ∩ dd ≠ (∅ : V) →
      (coneRestrict P R x f) ‘ (w ∩ dd) = ((coneRestrict P R x f) ‘ w) ∩ dd := by
  obtain ⟨hxB, hxt⟩ := (mem_boolCone_sub_iff ht).mp hx
  intro w hw hne
  obtain ⟨hwB, hwx⟩ := (mem_boolCone_sub_iff hxB).mp hw
  have hwt : w ∈ boolCone P R t :=
    (mem_boolCone_sub_iff ht).mpr ⟨hwB, subset_trans hwx hxt⟩
  have hwd : w ∩ dd ∈ boolCone P R x :=
    (mem_boolCone_sub_iff hxB).mpr
      ⟨(mem_booleanConditions_iff _ _ _).mpr
        ⟨forcingRegular_inter (booleanConditions_regular hwB) hdd,
          glue_exists_mem_of_ne_empty hne⟩,
        subset_trans (fun z hz ↦ (mem_inter_iff.mp hz).1) hwx⟩
  rw [coneRestrict_value hwd, coneRestrict_value hw]
  exact hequi w hwt hne

/-- The residual piece of `a`. -/
noncomputable def sbC (P R a a₀ b f g : V) : V :=
  a ∩ forcingNegation P R (sbJoin P R a a₀ b f g)

/-- The residual piece of `b`. -/
noncomputable def sbD (P R a a₀ b f g : V) : V :=
  b ∩ forcingNegation P R (coneImage P R a f (sbJoin P R a a₀ b f g))

/-- The pieces of `a`, indexed by `ω` together with `ω` itself. -/
noncomputable def sbAval (P R a a₀ b f g i : V) : V :=
  if i = (ω : V) then sbC P R a a₀ b f g else sbStage P R a a₀ b f g i

/-- The pieces of `b`, matched with the pieces of `a`. -/
noncomputable def sbBval (P R a a₀ b f g i : V) : V :=
  if i = (ω : V) then sbD P R a a₀ b f g
  else coneImage P R a f (sbStage P R a a₀ b f g i)

/-- The piece isomorphisms. -/
noncomputable def sbFval (P R a a₀ b f g i : V) : V :=
  if i = (ω : V) then converseGraph (coneRestrict P R (sbD P R a a₀ b f g) g)
  else coneRestrict P R (sbStage P R a a₀ b f g i) f

theorem sbImageStage_definable (P R a a₀ b f g : V) :
    ℒₛₑₜ-function₁ (fun i : V ↦ coneImage P R a f (sbStage P R a a₀ b f g i)) := by
  have h := sbStage_definable P R a a₀ b f g
  unfold coneImage coneBelow
  definability

theorem sbRestrictStage_definable (P R a a₀ b f g : V) :
    ℒₛₑₜ-function₁ (fun i : V ↦ coneRestrict P R (sbStage P R a a₀ b f g i) f) := by
  have h1 := coneRestrictMap_definable P R f
  have h2 := sbStage_definable P R a a₀ b f g
  definability

theorem sbAval_definable (P R a a₀ b f g : V) :
    ℒₛₑₜ-function₁ (sbAval P R a a₀ b f g) := by
  unfold sbAval
  exact sb_if_definable (sbStage_definable P R a a₀ b f g) _ _

theorem sbBval_definable (P R a a₀ b f g : V) :
    ℒₛₑₜ-function₁ (sbBval P R a a₀ b f g) := by
  unfold sbBval
  exact sb_if_definable (sbImageStage_definable P R a a₀ b f g) _ _

theorem sbFval_definable (P R a a₀ b f g : V) :
    ℒₛₑₜ-function₁ (sbFval P R a a₀ b f g) := by
  unfold sbFval
  exact sb_if_definable (sbRestrictStage_definable P R a a₀ b f g) _ _

/-- The index set: the stages together with `ω` for the residual piece, with the empty pieces
dropped. -/
noncomputable def sbIndex (P R a a₀ b f g : V) : V :=
  sep (succ (ω : V)) (fun i ↦ sbAval P R a a₀ b f g i ≠ (∅ : V))
    (by have := sbAval_definable P R a a₀ b f g; definability)

theorem mem_sbIndex_iff (P R a a₀ b f g i : V) :
    i ∈ sbIndex P R a a₀ b f g ↔
      i ∈ succ (ω : V) ∧ sbAval P R a a₀ b f g i ≠ (∅ : V) :=
  mem_sep_iff

theorem sbAval_omega (P R a a₀ b f g : V) :
    sbAval P R a a₀ b f g (ω : V) = sbC P R a a₀ b f g := by simp [sbAval]

theorem sbBval_omega (P R a a₀ b f g : V) :
    sbBval P R a a₀ b f g (ω : V) = sbD P R a a₀ b f g := by simp [sbBval]

theorem sbFval_omega (P R a a₀ b f g : V) :
    sbFval P R a a₀ b f g (ω : V) =
      converseGraph (coneRestrict P R (sbD P R a a₀ b f g) g) := by simp [sbFval]

theorem sb_ne_omega {n : V} (hn : n ∈ (ω : V)) : n ≠ (ω : V) :=
  fun h ↦ mem_irrefl (ω : V) (h ▸ hn)

theorem sbAval_nat (P R a a₀ b f g : V) {n : V} (hn : n ∈ (ω : V)) :
    sbAval P R a a₀ b f g n = sbStage P R a a₀ b f g n := by
  simp [sbAval, sb_ne_omega hn]

theorem sbBval_nat (P R a a₀ b f g : V) {n : V} (hn : n ∈ (ω : V)) :
    sbBval P R a a₀ b f g n = coneImage P R a f (sbStage P R a a₀ b f g n) := by
  simp [sbBval, sb_ne_omega hn]

theorem sbFval_nat (P R a a₀ b f g : V) {n : V} (hn : n ∈ (ω : V)) :
    sbFval P R a a₀ b f g n = coneRestrict P R (sbStage P R a a₀ b f g n) f := by
  simp [sbFval, sb_ne_omega hn]

namespace SBSetup

variable {P R a b a₀ b₀ f g : V}

theorem coneCreg (H : SBSetup P R a b a₀ b₀ f g) :
    IsForcingRegular P R (sbC P R a a₀ b f g) ∧ sbC P R a a₀ b f g ⊆ a :=
  ⟨sb_relComp_regular H.pre H.areg H.joinReg.1, fun _z hz ↦ (mem_inter_iff.mp hz).1⟩

theorem coneDreg (H : SBSetup P R a b a₀ b₀ f g) :
    IsForcingRegular P R (sbD P R a a₀ b f g) ∧ sbD P R a a₀ b f g ⊆ b :=
  ⟨sb_relComp_regular H.pre H.breg (H.imageF H.joinReg.1 H.joinReg.2).1,
    fun _z hz ↦ (mem_inter_iff.mp hz).1⟩

theorem gConeD (H : SBSetup P R a b a₀ b₀ f g) :
    coneImage P R b g (sbD P R a a₀ b f g) = sbC P R a a₀ b f g := H.gResidual

theorem coneD_ne (H : SBSetup P R a b a₀ b₀ f g) (hC : sbC P R a a₀ b f g ≠ (∅ : V)) :
    sbD P R a a₀ b f g ≠ (∅ : V) := by
  intro h
  apply hC
  rw [← H.gConeD, h, coneImage_empty]

theorem coneC_ne (H : SBSetup P R a b a₀ b₀ f g) (hD : sbD P R a a₀ b f g ≠ (∅ : V)) :
    sbC P R a a₀ b f g ≠ (∅ : V) := by
  rw [← H.gConeD]
  exact sb_coneImage_ne_empty H.pre H.bmem H.giso H.coneDreg.1 H.coneDreg.2 hD

theorem stageInterC (H : SBSetup P R a b a₀ b₀ f g) {n : V} (hn : n ∈ (ω : V)) :
    sbStage P R a a₀ b f g n ∩ sbC P R a a₀ b f g = (∅ : V) := by
  refine glue_eq_empty_of_forall (fun z hz ↦ ?_)
  obtain ⟨hz1, hz2⟩ := mem_inter_iff.mp hz
  have : z ∈ sbJoin P R a a₀ b f g ∩ forcingNegation P R (sbJoin P R a a₀ b f g) :=
    mem_inter_iff.mpr ⟨H.stageSubJoin hn z hz1, (mem_inter_iff.mp hz2).2⟩
  rw [inter_forcingNegation_eq_empty H.pre H.joinReg.1.1] at this
  exact not_mem_empty this

theorem imageStageInterD (H : SBSetup P R a b a₀ b₀ f g) {n : V} (hn : n ∈ (ω : V)) :
    coneImage P R a f (sbStage P R a a₀ b f g n) ∩ sbD P R a a₀ b f g = (∅ : V) := by
  refine glue_eq_empty_of_forall (fun z hz ↦ ?_)
  obtain ⟨hz1, hz2⟩ := mem_inter_iff.mp hz
  have hsub : coneImage P R a f (sbStage P R a a₀ b f g n) ⊆
      coneImage P R a f (sbJoin P R a a₀ b f g) := coneImage_mono (H.stageSubJoin hn)
  have : z ∈ coneImage P R a f (sbJoin P R a a₀ b f g) ∩
      forcingNegation P R (coneImage P R a f (sbJoin P R a a₀ b f g)) :=
    mem_inter_iff.mpr ⟨hsub z hz1, (mem_inter_iff.mp hz2).2⟩
  rw [inter_forcingNegation_eq_empty H.pre (H.imageF H.joinReg.1 H.joinReg.2).1.1] at this
  exact not_mem_empty this

theorem avalReg (H : SBSetup P R a b a₀ b₀ f g) {i : V} (hi : i ∈ succ (ω : V)) :
    IsForcingRegular P R (sbAval P R a a₀ b f g i) ∧ sbAval P R a a₀ b f g i ⊆ a := by
  rcases mem_succ_iff.mp hi with rfl | hn
  · rw [sbAval_omega]
    exact H.coneCreg
  · rw [sbAval_nat _ _ _ _ _ _ _ hn]
    exact H.stageReg i hn

theorem bvalReg (H : SBSetup P R a b a₀ b₀ f g) {i : V} (hi : i ∈ succ (ω : V)) :
    IsForcingRegular P R (sbBval P R a a₀ b f g i) ∧ sbBval P R a a₀ b f g i ⊆ b := by
  rcases mem_succ_iff.mp hi with rfl | hn
  · rw [sbBval_omega]
    exact H.coneDreg
  · rw [sbBval_nat _ _ _ _ _ _ _ hn]
    have h := H.imageF (H.stageReg i hn).1 (H.stageReg i hn).2
    exact ⟨h.1, subset_trans h.2 H.b0sub⟩

theorem bval_ne (H : SBSetup P R a b a₀ b₀ f g) {i : V} (hi : i ∈ succ (ω : V))
    (hne : sbAval P R a a₀ b f g i ≠ (∅ : V)) : sbBval P R a a₀ b f g i ≠ (∅ : V) := by
  rcases mem_succ_iff.mp hi with rfl | hn
  · rw [sbBval_omega]
    rw [sbAval_omega] at hne
    exact H.coneD_ne hne
  · rw [sbBval_nat _ _ _ _ _ _ _ hn]
    rw [sbAval_nat _ _ _ _ _ _ _ hn] at hne
    exact sb_coneImage_ne_empty H.pre H.amem H.fiso (H.stageReg i hn).1 (H.stageReg i hn).2 hne

theorem aval_ne_of_bval (H : SBSetup P R a b a₀ b₀ f g) {i : V} (hi : i ∈ succ (ω : V))
    (hne : sbBval P R a a₀ b f g i ≠ (∅ : V)) : sbAval P R a a₀ b f g i ≠ (∅ : V) := by
  rcases mem_succ_iff.mp hi with rfl | hn
  · rw [sbAval_omega]
    rw [sbBval_omega] at hne
    exact H.coneC_ne hne
  · rw [sbAval_nat _ _ _ _ _ _ _ hn]
    rw [sbBval_nat _ _ _ _ _ _ _ hn] at hne
    intro h
    apply hne
    rw [h, coneImage_empty]

theorem avalCone (H : SBSetup P R a b a₀ b₀ f g) {i : V} (hi : i ∈ sbIndex P R a a₀ b f g) :
    sbAval P R a a₀ b f g i ∈ boolCone P R a := by
  obtain ⟨hsucc, hne⟩ := (mem_sbIndex_iff _ _ _ _ _ _ _ _).mp hi
  exact (mem_boolCone_sub_iff H.amem).mpr
    ⟨(mem_booleanConditions_iff _ _ _).mpr
      ⟨(H.avalReg hsucc).1, glue_exists_mem_of_ne_empty hne⟩, (H.avalReg hsucc).2⟩

theorem bvalCone (H : SBSetup P R a b a₀ b₀ f g) {i : V} (hi : i ∈ sbIndex P R a a₀ b f g) :
    sbBval P R a a₀ b f g i ∈ boolCone P R b := by
  obtain ⟨hsucc, hne⟩ := (mem_sbIndex_iff _ _ _ _ _ _ _ _).mp hi
  exact (mem_boolCone_sub_iff H.bmem).mpr
    ⟨(mem_booleanConditions_iff _ _ _).mpr
      ⟨(H.bvalReg hsucc).1, glue_exists_mem_of_ne_empty (H.bval_ne hsucc hne)⟩,
      (H.bvalReg hsucc).2⟩

/-- Distinct stages are disjoint. -/
theorem stageDisjoint' (H : SBSetup P R a b a₀ b₀ f g) {i j : V} (hi : i ∈ (ω : V))
    (hj : j ∈ (ω : V)) (hij : i ≠ j) :
    sbStage P R a a₀ b f g i ∩ sbStage P R a a₀ b f g j = (∅ : V) := by
  have : IsOrdinal i := IsOrdinal.of_mem hi
  have : IsOrdinal j := IsOrdinal.of_mem hj
  rcases IsOrdinal.mem_trichotomy (α := i) (β := j) with h | h | h
  · exact H.stageDisjoint i hi j hj h
  · exact absurd h hij
  · rw [glue_inter_comm]
    exact H.stageDisjoint j hj i hi h

/-- The pieces of `a` are pairwise disjoint. -/
theorem avalDisjoint (H : SBSetup P R a b a₀ b₀ f g) {i j : V}
    (hi : i ∈ succ (ω : V)) (hj : j ∈ succ (ω : V)) (hij : i ≠ j) :
    sbAval P R a a₀ b f g i ∩ sbAval P R a a₀ b f g j = (∅ : V) := by
  rcases mem_succ_iff.mp hi with rfl | hin
  · rcases mem_succ_iff.mp hj with rfl | hjn
    · exact absurd rfl hij
    · rw [sbAval_omega, sbAval_nat _ _ _ _ _ _ _ hjn, glue_inter_comm]
      exact H.stageInterC hjn
  · rcases mem_succ_iff.mp hj with rfl | hjn
    · rw [sbAval_omega, sbAval_nat _ _ _ _ _ _ _ hin]
      exact H.stageInterC hin
    · rw [sbAval_nat _ _ _ _ _ _ _ hin, sbAval_nat _ _ _ _ _ _ _ hjn]
      exact H.stageDisjoint' hin hjn hij

/-- The pieces of `b` are pairwise disjoint. -/
theorem bvalDisjoint (H : SBSetup P R a b a₀ b₀ f g) {i j : V}
    (hi : i ∈ succ (ω : V)) (hj : j ∈ succ (ω : V)) (hij : i ≠ j) :
    sbBval P R a a₀ b f g i ∩ sbBval P R a a₀ b f g j = (∅ : V) := by
  rcases mem_succ_iff.mp hi with rfl | hin
  · rcases mem_succ_iff.mp hj with rfl | hjn
    · exact absurd rfl hij
    · rw [sbBval_omega, sbBval_nat _ _ _ _ _ _ _ hjn, glue_inter_comm]
      exact H.imageStageInterD hjn
  · rcases mem_succ_iff.mp hj with rfl | hjn
    · rw [sbBval_omega, sbBval_nat _ _ _ _ _ _ _ hin]
      exact H.imageStageInterD hin
    · rw [sbBval_nat _ _ _ _ _ _ _ hin, sbBval_nat _ _ _ _ _ _ _ hjn]
      exact sb_coneImage_disjoint H.pre H.amem H.b0mem H.fiso
        (H.stageReg i hin).1 (H.stageReg i hin).2 (H.stageReg j hjn).1 (H.stageReg j hjn).2
        (H.stageDisjoint' hin hjn hij)

end SBSetup

/-- The pieces of `a` as a function on the index set. -/
noncomputable def sbAfun (P R a a₀ b f g : V) : V :=
  definableGraph (sbIndex P R a a₀ b f g) (sbAval P R a a₀ b f g)
    (sbAval_definable P R a a₀ b f g)

/-- The pieces of `b` as a function on the index set. -/
noncomputable def sbBfun (P R a a₀ b f g : V) : V :=
  definableGraph (sbIndex P R a a₀ b f g) (sbBval P R a a₀ b f g)
    (sbBval_definable P R a a₀ b f g)

/-- The piece isomorphisms as a function on the index set. -/
noncomputable def sbFfun (P R a a₀ b f g : V) : V :=
  definableGraph (sbIndex P R a a₀ b f g) (sbFval P R a a₀ b f g)
    (sbFval_definable P R a a₀ b f g)

theorem sbAfun_value {P R a a₀ b f g i : V} (hi : i ∈ sbIndex P R a a₀ b f g) :
    (sbAfun P R a a₀ b f g) ‘ i = sbAval P R a a₀ b f g i :=
  value_definableGraph _ _ _ hi

theorem sbBfun_value {P R a a₀ b f g i : V} (hi : i ∈ sbIndex P R a a₀ b f g) :
    (sbBfun P R a a₀ b f g) ‘ i = sbBval P R a a₀ b f g i :=
  value_definableGraph _ _ _ hi

theorem sbFfun_value {P R a a₀ b f g i : V} (hi : i ∈ sbIndex P R a a₀ b f g) :
    (sbFfun P R a a₀ b f g) ‘ i = sbFval P R a a₀ b f g i :=
  value_definableGraph _ _ _ hi

theorem sbFfun_isFunction (P R a a₀ b f g : V) : IsFunction (sbFfun P R a a₀ b f g) := by
  unfold sbFfun
  exact definableGraph_isFunction _ _ _

theorem sbFfun_domain (P R a a₀ b f g : V) :
    domain (sbFfun P R a a₀ b f g) = sbIndex P R a a₀ b f g := by
  unfold sbFfun
  exact domain_definableGraph _ _ _

theorem mem_range_sbAfun (P R a a₀ b f g C : V) :
    C ∈ range (sbAfun P R a a₀ b f g) ↔
      ∃ i, i ∈ sbIndex P R a a₀ b f g ∧ C = sbAval P R a a₀ b f g i := by
  unfold sbAfun
  rw [range_definableGraph, repl_spec]

theorem mem_range_sbBfun (P R a a₀ b f g C : V) :
    C ∈ range (sbBfun P R a a₀ b f g) ↔
      ∃ i, i ∈ sbIndex P R a a₀ b f g ∧ C = sbBval P R a a₀ b f g i := by
  unfold sbBfun
  rw [range_definableGraph, repl_spec]

namespace SBSetup

variable {P R a b a₀ b₀ f g : V}

/-- The pieces of `a` form a cone partition of `a`. -/
theorem partitionA (H : SBSetup P R a b a₀ b₀ f g) :
    IsConePartition P R a (sbIndex P R a a₀ b f g) (sbAfun P R a a₀ b f g) := by
  have hrangeReg : ∀ C, C ∈ range (sbAfun P R a a₀ b f g) →
      IsForcingRegular P R C ∧ C ⊆ a := by
    intro C hC
    obtain ⟨i, hi, rfl⟩ := (mem_range_sbAfun _ _ _ _ _ _ _ _).mp hC
    exact H.avalReg ((mem_sbIndex_iff _ _ _ _ _ _ _ _).mp hi).1
  refine ⟨definableGraph_isFunction _ _ _, domain_definableGraph _ _ _, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [sbAfun_value hi]
    exact boolCone_subset P R a _ (H.avalCone hi)
  · intro i hi
    rw [sbAfun_value hi]
    exact (H.avalReg ((mem_sbIndex_iff _ _ _ _ _ _ _ _).mp hi).1).2
  · intro i hi j hj hij
    rw [sbAfun_value hi, sbAfun_value hj]
    exact H.avalDisjoint ((mem_sbIndex_iff _ _ _ _ _ _ _ _).mp hi).1
      ((mem_sbIndex_iff _ _ _ _ _ _ _ _).mp hj).1 hij
  · apply SetTheory.subset_antisymm
    · exact regularJoin_subset H.pre (fun C hC ↦ (hrangeReg C hC).2) H.areg
    · refine sb_subset_of_inter_negation_empty H.pre H.areg
        (regularJoin_regular H.pre (fun C hC ↦ (hrangeReg C hC).1.1)) ?_
      refine glue_eq_empty_of_forall (fun p hp ↦ ?_)
      obtain ⟨hpa, hpn⟩ := mem_inter_iff.mp hp
      have hpP : p ∈ P := H.areg.1 p hpa
      have hall := (mem_forcingNegation_regularJoin_iff H.pre
        (fun C hC ↦ (hrangeReg C hC).1)).mp hpn
      have hstage : ∀ n, n ∈ (ω : V) →
          p ∈ forcingNegation P R (sbStage P R a a₀ b f g n) := by
        intro n hn
        by_cases hne : sbStage P R a a₀ b f g n = (∅ : V)
        · rw [hne]
          exact sb_mem_negation_empty hpP
        · have hnI : n ∈ sbIndex P R a a₀ b f g :=
            (mem_sbIndex_iff _ _ _ _ _ _ _ _).mpr
              ⟨mem_succ_iff.mpr (Or.inr hn), by
                rw [sbAval_nat _ _ _ _ _ _ _ hn]; exact hne⟩
          exact hall.2 _ ((mem_range_sbAfun _ _ _ _ _ _ _ _).mpr
            ⟨n, hnI, (sbAval_nat _ _ _ _ _ _ _ hn).symm⟩)
      have hpW : p ∈ forcingNegation P R (sbJoin P R a a₀ b f g) := by
        refine (mem_forcingNegation_regularJoin_iff H.pre
          (fun C hC ↦ (H.rangeReg C hC).1)).mpr ⟨hpP, fun C hC ↦ ?_⟩
        obtain ⟨n, hn, rfl⟩ := (sb_mem_range_iff _ _ _ _ _ _ _ _).mp hC
        exact hstage n hn
      have hpC : p ∈ sbC P R a a₀ b f g := mem_inter_iff.mpr ⟨hpa, hpW⟩
      by_cases hCne : sbC P R a a₀ b f g = (∅ : V)
      · rw [hCne] at hpC
        exact not_mem_empty hpC
      · have hωI : (ω : V) ∈ sbIndex P R a a₀ b f g :=
          (mem_sbIndex_iff _ _ _ _ _ _ _ _).mpr
            ⟨mem_succ_self _, by rw [sbAval_omega]; exact hCne⟩
        have hmem := hall.2 (sbC P R a a₀ b f g)
          ((mem_range_sbAfun _ _ _ _ _ _ _ _).mpr
            ⟨(ω : V), hωI, (sbAval_omega _ _ _ _ _ _ _).symm⟩)
        have hcc : p ∈ sbC P R a a₀ b f g ∩ forcingNegation P R (sbC P R a a₀ b f g) :=
          mem_inter_iff.mpr ⟨hpC, hmem⟩
        rw [inter_forcingNegation_eq_empty H.pre H.coneCreg.1.1] at hcc
        exact not_mem_empty hcc

/-- The pieces of `b` form a cone partition of `b`. -/
theorem partitionB (H : SBSetup P R a b a₀ b₀ f g) :
    IsConePartition P R b (sbIndex P R a a₀ b f g) (sbBfun P R a a₀ b f g) := by
  have hrangeReg : ∀ C, C ∈ range (sbBfun P R a a₀ b f g) →
      IsForcingRegular P R C ∧ C ⊆ b := by
    intro C hC
    obtain ⟨i, hi, rfl⟩ := (mem_range_sbBfun _ _ _ _ _ _ _ _).mp hC
    exact H.bvalReg ((mem_sbIndex_iff _ _ _ _ _ _ _ _).mp hi).1
  refine ⟨definableGraph_isFunction _ _ _, domain_definableGraph _ _ _, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [sbBfun_value hi]
    exact boolCone_subset P R b _ (H.bvalCone hi)
  · intro i hi
    rw [sbBfun_value hi]
    exact (H.bvalReg ((mem_sbIndex_iff _ _ _ _ _ _ _ _).mp hi).1).2
  · intro i hi j hj hij
    rw [sbBfun_value hi, sbBfun_value hj]
    exact H.bvalDisjoint ((mem_sbIndex_iff _ _ _ _ _ _ _ _).mp hi).1
      ((mem_sbIndex_iff _ _ _ _ _ _ _ _).mp hj).1 hij
  · apply SetTheory.subset_antisymm
    · exact regularJoin_subset H.pre (fun C hC ↦ (hrangeReg C hC).2) H.breg
    · refine sb_subset_of_inter_negation_empty H.pre H.breg
        (regularJoin_regular H.pre (fun C hC ↦ (hrangeReg C hC).1.1)) ?_
      refine glue_eq_empty_of_forall (fun p hp ↦ ?_)
      obtain ⟨hpb, hpn⟩ := mem_inter_iff.mp hp
      have hpP : p ∈ P := H.breg.1 p hpb
      have hall := (mem_forcingNegation_regularJoin_iff H.pre
        (fun C hC ↦ (hrangeReg C hC).1)).mp hpn
      have hstage : ∀ n, n ∈ (ω : V) →
          p ∈ forcingNegation P R (coneImage P R a f (sbStage P R a a₀ b f g n)) := by
        intro n hn
        by_cases hne : sbStage P R a a₀ b f g n = (∅ : V)
        · rw [hne, coneImage_empty]
          exact sb_mem_negation_empty hpP
        · have hnI : n ∈ sbIndex P R a a₀ b f g :=
            (mem_sbIndex_iff _ _ _ _ _ _ _ _).mpr
              ⟨mem_succ_iff.mpr (Or.inr hn), by
                rw [sbAval_nat _ _ _ _ _ _ _ hn]; exact hne⟩
          exact hall.2 _ ((mem_range_sbBfun _ _ _ _ _ _ _ _).mpr
            ⟨n, hnI, (sbBval_nat _ _ _ _ _ _ _ hn).symm⟩)
      have hWbjoin : coneImage P R a f (sbJoin P R a a₀ b f g) =
          regularJoin P R (repl (coneImage P R a f) (sb_coneImageMap_definable P R a f)
            (range (sbSeq P R a a₀ b f g))) :=
        sb_coneImage_join H.pre H.amem H.b0mem H.fiso H.rangeReg
      have hpWb : p ∈ forcingNegation P R (coneImage P R a f (sbJoin P R a a₀ b f g)) := by
        rw [hWbjoin]
        refine (mem_forcingNegation_regularJoin_iff H.pre (fun D hD ↦ ?_)).mpr
          ⟨hpP, fun D hD ↦ ?_⟩
        · obtain ⟨C, hC, rfl⟩ := (repl_spec _).mp hD
          exact (H.imageF (H.rangeReg C hC).1 (H.rangeReg C hC).2).1
        · obtain ⟨C, hC, rfl⟩ := (repl_spec _).mp hD
          obtain ⟨n, hn, rfl⟩ := (sb_mem_range_iff _ _ _ _ _ _ _ _).mp hC
          exact hstage n hn
      have hpD : p ∈ sbD P R a a₀ b f g := mem_inter_iff.mpr ⟨hpb, hpWb⟩
      by_cases hDne : sbD P R a a₀ b f g = (∅ : V)
      · rw [hDne] at hpD
        exact not_mem_empty hpD
      · have hωI : (ω : V) ∈ sbIndex P R a a₀ b f g :=
          (mem_sbIndex_iff _ _ _ _ _ _ _ _).mpr
            ⟨mem_succ_self _, by
              rw [sbAval_omega]
              exact H.coneC_ne hDne⟩
        have hmem := hall.2 (sbD P R a a₀ b f g)
          ((mem_range_sbBfun _ _ _ _ _ _ _ _).mpr
            ⟨(ω : V), hωI, (sbBval_omega _ _ _ _ _ _ _).symm⟩)
        have hdd : p ∈ sbD P R a a₀ b f g ∩ forcingNegation P R (sbD P R a a₀ b f g) :=
          mem_inter_iff.mpr ⟨hpD, hmem⟩
        rw [inter_forcingNegation_eq_empty H.pre H.coneDreg.1.1] at hdd
        exact not_mem_empty hdd

end SBSetup

namespace SBSetup

variable {P R a b a₀ b₀ f g D : V}

theorem coneD_cone (H : SBSetup P R a b a₀ b₀ f g) (hne : sbD P R a a₀ b f g ≠ (∅ : V)) :
    sbD P R a a₀ b f g ∈ boolCone P R b :=
  (mem_boolCone_sub_iff H.bmem).mpr
    ⟨(mem_booleanConditions_iff _ _ _).mpr
      ⟨H.coneDreg.1, glue_exists_mem_of_ne_empty hne⟩, H.coneDreg.2⟩

theorem gConeD_value (H : SBSetup P R a b a₀ b₀ f g) (hne : sbD P R a a₀ b f g ≠ (∅ : V)) :
    g ‘ (sbD P R a a₀ b f g) = sbC P R a a₀ b f g := by
  rw [← coneImage_value H.giso (H.coneD_cone hne)]
  exact H.gConeD

theorem stage_cone (H : SBSetup P R a b a₀ b₀ f g) {n : V} (hn : n ∈ (ω : V))
    (hne : sbStage P R a a₀ b f g n ≠ (∅ : V)) :
    sbStage P R a a₀ b f g n ∈ boolCone P R a :=
  (mem_boolCone_sub_iff H.amem).mpr
    ⟨(mem_booleanConditions_iff _ _ _).mpr
      ⟨(H.stageReg n hn).1, glue_exists_mem_of_ne_empty hne⟩, (H.stageReg n hn).2⟩

/-- Each piece map is an isomorphism of the cone of the piece of `a` onto the cone of the
matching piece of `b`. -/
theorem pieceIso (H : SBSetup P R a b a₀ b₀ f g) {i : V} (hi : i ∈ sbIndex P R a a₀ b f g) :
    IsForcingIsomorphism (boolCone P R (sbAval P R a a₀ b f g i))
      (boolConeOrder P R (sbAval P R a a₀ b f g i))
      (boolCone P R (sbBval P R a a₀ b f g i))
      (boolConeOrder P R (sbBval P R a a₀ b f g i)) (sbFval P R a a₀ b f g i) := by
  obtain ⟨hsucc, hne⟩ := (mem_sbIndex_iff _ _ _ _ _ _ _ _).mp hi
  rcases mem_succ_iff.mp hsucc with rfl | hn
  · rw [sbAval_omega] at hne
    have hd := H.coneD_ne hne
    rw [sbFval_omega, sbAval_omega, sbBval_omega]
    have hiso := sb_coneRestrict_iso H.bmem H.a0mem H.giso (H.coneD_cone hd)
    rw [H.gConeD_value hd] at hiso
    exact isForcingIsomorphism_inverse hiso
  · rw [sbAval_nat _ _ _ _ _ _ _ hn] at hne
    rw [sbFval_nat _ _ _ _ _ _ _ hn, sbAval_nat _ _ _ _ _ _ _ hn, sbBval_nat _ _ _ _ _ _ _ hn]
    have hiso := sb_coneRestrict_iso H.amem H.b0mem H.fiso (H.stage_cone hn hne)
    rw [← coneImage_value H.fiso (H.stage_cone hn hne)] at hiso
    exact hiso

/-- The clause `hDpiece` of the gluing theorem: a `d` missing a piece of `a` misses the
matching piece of `b`. -/
theorem pieceMissing (H : SBSetup P R a b a₀ b₀ f g)
    (hDreg : ∀ d, d ∈ D → IsForcingRegular P R d)
    (hDneg : ∀ d, d ∈ D → forcingNegation P R d ∈ D)
    (hfequi : ∀ d, d ∈ D → ∀ x, x ∈ boolCone P R a → x ∩ d ≠ (∅ : V) →
      f ‘ (x ∩ d) = (f ‘ x) ∩ d)
    (hgequi : ∀ d, d ∈ D → ∀ y, y ∈ boolCone P R b → y ∩ d ≠ (∅ : V) →
      g ‘ (y ∩ d) = (g ‘ y) ∩ d)
    {i : V} (hi : i ∈ sbIndex P R a a₀ b f g) {d : V} (hd : d ∈ D)
    (hmiss : sbAval P R a a₀ b f g i ∩ d = (∅ : V)) :
    sbBval P R a a₀ b f g i ∩ d = (∅ : V) := by
  obtain ⟨hsucc, hne⟩ := (mem_sbIndex_iff _ _ _ _ _ _ _ _).mp hi
  rcases mem_succ_iff.mp hsucc with rfl | hn
  · rw [sbAval_omega] at hne hmiss
    have hdne := H.coneD_ne hne
    rw [sbBval_omega]
    by_contra hcon
    have hdd : sbD P R a a₀ b f g ∩ d ∈ boolCone P R b :=
      (mem_boolCone_sub_iff H.bmem).mpr
        ⟨(mem_booleanConditions_iff _ _ _).mpr
          ⟨forcingRegular_inter H.coneDreg.1 (hDreg d hd), glue_exists_mem_of_ne_empty hcon⟩,
          subset_trans (fun z hz ↦ (mem_inter_iff.mp hz).1) H.coneDreg.2⟩
    have hval := hgequi d hd (sbD P R a a₀ b f g) (H.coneD_cone hdne) hcon
    rw [H.gConeD_value hdne, hmiss] at hval
    exact sb_value_ne_empty H.giso hdd hval
  · rw [sbAval_nat _ _ _ _ _ _ _ hn] at hne hmiss
    rw [sbBval_nat _ _ _ _ _ _ _ hn, coneImage_value H.fiso (H.stage_cone hn hne)]
    exact sb_piece_disjoint H.pre H.amem H.b0mem H.fiso (hDreg d hd)
      (hfequi (forcingNegation P R d) (hDneg d hd)) (H.stage_cone hn hne) hmiss

/-- The piece maps are equivariant. -/
theorem pieceEqui (H : SBSetup P R a b a₀ b₀ f g)
    (hDreg : ∀ d, d ∈ D → IsForcingRegular P R d)
    (hDneg : ∀ d, d ∈ D → forcingNegation P R d ∈ D)
    (hfequi : ∀ d, d ∈ D → ∀ x, x ∈ boolCone P R a → x ∩ d ≠ (∅ : V) →
      f ‘ (x ∩ d) = (f ‘ x) ∩ d)
    (hgequi : ∀ d, d ∈ D → ∀ y, y ∈ boolCone P R b → y ∩ d ≠ (∅ : V) →
      g ‘ (y ∩ d) = (g ‘ y) ∩ d)
    {i : V} (hi : i ∈ sbIndex P R a a₀ b f g) {d : V} (hd : d ∈ D)
    {x : V} (hx : x ∈ boolCone P R (sbAval P R a a₀ b f g i)) (hxd : x ∩ d ≠ (∅ : V)) :
    (sbFval P R a a₀ b f g i) ‘ (x ∩ d) = ((sbFval P R a a₀ b f g i) ‘ x) ∩ d := by
  obtain ⟨hsucc, hne⟩ := (mem_sbIndex_iff _ _ _ _ _ _ _ _).mp hi
  rcases mem_succ_iff.mp hsucc with rfl | hn
  · rw [sbAval_omega] at hne hx
    have hdne := H.coneD_ne hne
    have hiso := sb_coneRestrict_iso H.bmem H.a0mem H.giso (H.coneD_cone hdne)
    rw [H.gConeD_value hdne] at hiso
    have hDB : sbD P R a a₀ b f g ∈ booleanConditions P R :=
      boolCone_subset P R b _ (H.coneD_cone hdne)
    have hCB : sbC P R a a₀ b f g ∈ booleanConditions P R :=
      (mem_booleanConditions_iff _ _ _).mpr
        ⟨H.coneCreg.1, glue_exists_mem_of_ne_empty hne⟩
    rw [sbFval_omega]
    exact sb_inverse_equivariant H.pre hDB hCB hiso (hDreg d hd)
      (sb_restrict_equivariant H.bmem (H.coneD_cone hdne) (hDreg d hd) (hgequi d hd))
      (sb_restrict_equivariant H.bmem (H.coneD_cone hdne)
        (hDreg (forcingNegation P R d) (hDneg d hd))
        (hgequi (forcingNegation P R d) (hDneg d hd))) hx hxd
  · rw [sbAval_nat _ _ _ _ _ _ _ hn] at hne hx
    rw [sbFval_nat _ _ _ _ _ _ _ hn]
    exact sb_restrict_equivariant H.amem (H.stage_cone hn hne) (hDreg d hd) (hfequi d hd)
      x hx hxd

end SBSetup

/-! ### The theorem -/

/-- Schroeder-Bernstein for cones of the Boolean completion, with equivariance for a set `D` of
regular sets closed under complements. If the cone of `a` is isomorphic to the cone of `b₀ ⊆ b`
by an equivariant `f`, and the cone of `b` is isomorphic to the cone of `a₀ ⊆ a` by an
equivariant `g`, then the cone of `a` is isomorphic to the cone of `b` by an equivariant map. -/
theorem exists_coneIsomorphism_of_mutual_equivariant {P R a b a₀ b₀ f g D : V}
    (hR : IsForcingPreorder P R)
    (ha : a ∈ booleanConditions P R) (hb : b ∈ booleanConditions P R)
    (ha₀ : a₀ ∈ booleanConditions P R) (ha₀a : a₀ ⊆ a)
    (hb₀ : b₀ ∈ booleanConditions P R) (hb₀b : b₀ ⊆ b)
    (hf : IsForcingIsomorphism
      (forcingCone (booleanConditions P R) (booleanOrder P R) a)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) a))
      (forcingCone (booleanConditions P R) (booleanOrder P R) b₀)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) b₀)) f)
    (hg : IsForcingIsomorphism
      (forcingCone (booleanConditions P R) (booleanOrder P R) b)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) b))
      (forcingCone (booleanConditions P R) (booleanOrder P R) a₀)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) a₀)) g)
    (hDreg : ∀ d, d ∈ D → IsForcingRegular P R d)
    (hDneg : ∀ d, d ∈ D → forcingNegation P R d ∈ D)
    (hfequi : ∀ d, d ∈ D → ∀ x, x ∈ forcingCone (booleanConditions P R) (booleanOrder P R) a →
      x ∩ d ≠ (∅ : V) → f ‘ (x ∩ d) = (f ‘ x) ∩ d)
    (hgequi : ∀ d, d ∈ D → ∀ y, y ∈ forcingCone (booleanConditions P R) (booleanOrder P R) b →
      y ∩ d ≠ (∅ : V) → g ‘ (y ∩ d) = (g ‘ y) ∩ d) :
    ∃ h, IsForcingIsomorphism
      (forcingCone (booleanConditions P R) (booleanOrder P R) a)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) a))
      (forcingCone (booleanConditions P R) (booleanOrder P R) b)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) b)) h ∧
      ∀ d, d ∈ D → ∀ x, x ∈ forcingCone (booleanConditions P R) (booleanOrder P R) a →
        x ∩ d ≠ (∅ : V) → h ‘ (x ∩ d) = (h ‘ x) ∩ d := by
  have H : SBSetup P R a b a₀ b₀ f g := ⟨hR, ha, hb, ha₀, ha₀a, hb₀, hb₀b, hf, hg⟩
  refine exists_coneIsomorphism_of_conePartitions_equivariant (F := sbFfun P R a a₀ b f g)
    hR ha hb H.partitionA H.partitionB
    (sbFfun_isFunction P R a a₀ b f g) (sbFfun_domain P R a a₀ b f g) ?_ hDreg ?_ ?_
  · intro i hi
    rw [sbAfun_value hi, sbBfun_value hi, sbFfun_value hi]
    exact H.pieceIso hi
  · intro i hi d hd hmiss
    rw [sbAfun_value hi] at hmiss
    rw [sbBfun_value hi]
    exact H.pieceMissing hDreg hDneg hfequi hgequi hi hd hmiss
  · intro i hi d hd x hx hxd
    rw [sbAfun_value hi] at hx
    rw [sbFfun_value hi]
    exact H.pieceEqui hDreg hDneg hfequi hgequi hi hd hx hxd

/-- Schroeder-Bernstein for cones of the Boolean completion: mutually embeddable cones are
isomorphic. -/
theorem exists_coneIsomorphism_of_mutual {P R a b a₀ b₀ f g : V} (hR : IsForcingPreorder P R)
    (ha : a ∈ booleanConditions P R) (hb : b ∈ booleanConditions P R)
    (ha₀ : a₀ ∈ booleanConditions P R) (ha₀a : a₀ ⊆ a)
    (hb₀ : b₀ ∈ booleanConditions P R) (hb₀b : b₀ ⊆ b)
    (hf : IsForcingIsomorphism
      (forcingCone (booleanConditions P R) (booleanOrder P R) a)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) a))
      (forcingCone (booleanConditions P R) (booleanOrder P R) b₀)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) b₀)) f)
    (hg : IsForcingIsomorphism
      (forcingCone (booleanConditions P R) (booleanOrder P R) b)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) b))
      (forcingCone (booleanConditions P R) (booleanOrder P R) a₀)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) a₀)) g) :
    ∃ h, IsForcingIsomorphism
      (forcingCone (booleanConditions P R) (booleanOrder P R) a)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) a))
      (forcingCone (booleanConditions P R) (booleanOrder P R) b)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) b)) h := by
  obtain ⟨h, hh, -⟩ := exists_coneIsomorphism_of_mutual_equivariant (D := (∅ : V))
    hR ha hb ha₀ ha₀a hb₀ hb₀b hf hg (fun d hd ↦ absurd hd not_mem_empty)
    (fun d hd ↦ absurd hd not_mem_empty) (fun d hd ↦ absurd hd not_mem_empty)
    (fun d hd ↦ absurd hd not_mem_empty)
  exact ⟨h, hh⟩

end ZFVP
