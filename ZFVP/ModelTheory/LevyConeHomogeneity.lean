import ZFVP.ModelTheory.BooleanConePartitionGlue
import ZFVP.ModelTheory.LevyConePartitionData
import ZFVP.ModelTheory.LevyBooleanHomogeneity
import ZFVP.SetTheory.SchroederBernstein
import ZFVP.SetTheory.Hessenberg

/-! Homogeneity of the Boolean completion of the Levy collapse.

Write `B` for `booleanConditions (levyCollapse κ) (levyOrder κ)` with the order
`booleanOrder (levyCollapse κ) (levyOrder κ)`. This file proves `B|a ≅ B` for every nonzero `a`
of `B`, and hence `B|a ≅ B|b` for any two nonzero conditions.

The docstring of `LevyBooleanHomogeneity.lean` records homogeneity as open and says a proof would
need an absorption theorem below an arbitrary condition plus a uniqueness theorem for the collapse
algebra. That is wrong: neither is used below. This file supersedes the "what is not proved"
section of that docstring, which is left unedited.

The argument is a matching of partitions, not a Cantor-Bernstein argument.

* `levy_exists_conePartition` splits a nonzero `a` into a disjoint family `A` of pieces, indexed by
  a set `I`, whose cones are each isomorphic to all of `B`. The pieces are pairwise disjoint
  nonzero conditions, so `range A` is an antichain, and the chain condition
  (`levyBooleanAntichain_not_cardLE`) gives `¬ κ ≤# I`. So `I` has a well-ordered cardinal `γ ∈ κ`,
  and `lam := γ ∪ ω` is an ordinal in `κ` with `ω ⊆ lam` and `I ≤# lam`.

* `levy_exists_top_conePartition` splits the top of `B`, which is `levyCollapse κ` itself, into
  `lam` pieces whose cones are again each isomorphic to `B`.

* An isomorphism of Boolean cones carries a cone partition of its source to a cone partition of its
  target (`coneIso_image_conePartition` below). Pulling the `lam`-indexed partition of the top back
  through the isomorphism of the cone of `A ‘ i` with `B` refines the partition of `a` to one
  indexed by `I ×ˢ lam` (`conePartition_refine`), still with all cones isomorphic to `B`.

* `I ×ˢ lam ≋ lam` by Hessenberg, so `schroeder_bernstein` gives a bijection of `I ×ˢ lam` with
  `lam` and `conePartition_reindex` moves the `lam`-indexed partition of the top onto the index set
  `I ×ˢ lam`. Both partitions now sit over one index set with all pieces' cones isomorphic to `B`,
  so `exists_coneIsomorphism_of_conePartitions` glues an isomorphism of the cone of `a` with the
  cone of the top, which is `B`.

Nothing here needs an absorption theorem or a uniqueness theorem for the collapse algebra.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The cone of the top -/

section Top

variable (P R : V)

/-- The cone of the top of the Boolean completion is the whole completion. -/
theorem forcingCone_top_eq (hP : ∃ p, p ∈ P) :
    forcingCone (booleanConditions P R) (booleanOrder P R) P = booleanConditions P R := by
  apply mem_ext
  intro x
  rw [mem_forcingCone_booleanOrder_iff (top_mem_booleanConditions hP)]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, (booleanConditions_regular h).1⟩⟩

/-- The Boolean order restricted to the Boolean conditions is the Boolean order. -/
theorem restrictedOrder_booleanOrder_eq :
    restrictedOrder (booleanOrder P R) (booleanConditions P R) = booleanOrder P R := by
  apply mem_ext
  intro z
  unfold restrictedOrder
  rw [mem_inter_iff]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, (booleanOrder_poset P R).1.1 z h⟩⟩

theorem boolCone_top_eq (hP : ∃ p, p ∈ P) : boolCone P R P = booleanConditions P R :=
  forcingCone_top_eq P R hP

theorem boolConeOrder_top_eq (hP : ∃ p, p ∈ P) : boolConeOrder P R P = booleanOrder P R := by
  unfold boolConeOrder
  rw [boolCone_top_eq P R hP, restrictedOrder_booleanOrder_eq P R]

end Top

/-! ### The image of a cone partition under an isomorphism of cones -/

/-- The images of the pieces of a family under a map. -/
noncomputable def coneImageFamily (J A g : V) : V :=
  repl (fun j ↦ g ‘ (A ‘ j)) (by definability) J

theorem mem_coneImageFamily_iff (J A g w : V) :
    w ∈ coneImageFamily J A g ↔ ∃ j, j ∈ J ∧ w = g ‘ (A ‘ j) := by
  simp only [coneImageFamily, repl_spec]

section Transport

variable {P R c e J A g : V}

/-- An isomorphism of the cone of `c` with the cone of `e` carries a cone partition of `c` to a
cone partition of `e`, piece by piece. -/
theorem coneIso_image_conePartition (hR : IsForcingPreorder P R)
    (hc : c ∈ booleanConditions P R) (he : e ∈ booleanConditions P R)
    (hg : IsForcingIsomorphism (boolCone P R c) (boolConeOrder P R c)
      (boolCone P R e) (boolConeOrder P R e) g)
    (hA : IsConePartition P R c J A) :
    (∀ j, j ∈ J → g ‘ (A ‘ j) ∈ booleanConditions P R) ∧
    (∀ j, j ∈ J → g ‘ (A ‘ j) ⊆ e) ∧
    (∀ j, j ∈ J → ∀ j', j' ∈ J → j ≠ j' →
      (g ‘ (A ‘ j)) ∩ (g ‘ (A ‘ j')) = (∅ : V)) ∧
    regularJoin P R (coneImageFamily J A g) = e := by
  have hmemc : ∀ j, j ∈ J → A ‘ j ∈ boolCone P R c := fun j hj ↦
    (mem_boolCone_sub_iff hc).mpr ⟨hA.2.2.1 j hj, hA.2.2.2.1 j hj⟩
  have hmeme : ∀ j, j ∈ J → g ‘ (A ‘ j) ∈ boolCone P R e := fun j hj ↦
    function_value_mem hg.1 (hmemc j hj)
  have hcond : ∀ j, j ∈ J → g ‘ (A ‘ j) ∈ booleanConditions P R := fun j hj ↦
    ((mem_boolCone_sub_iff he).mp (hmeme j hj)).1
  have hsub : ∀ j, j ∈ J → g ‘ (A ‘ j) ⊆ e := fun j hj ↦
    ((mem_boolCone_sub_iff he).mp (hmeme j hj)).2
  refine ⟨hcond, hsub, fun j hj j' hj' hne ↦ glue_iso_inter_eq_empty hc he hg (hmemc j hj)
    (hmemc j' hj') (hA.2.2.2.2.1 j hj j' hj' hne), ?_⟩
  have hXsub : ∀ C, C ∈ coneImageFamily J A g → C ⊆ e := by
    intro C hC
    obtain ⟨j, hj, rfl⟩ := (mem_coneImageFamily_iff J A g C).mp hC
    exact hsub j hj
  have hSsub : regularJoin P R (coneImageFamily J A g) ⊆ e :=
    regularJoin_subset hR hXsub (booleanConditions_regular he)
  obtain ⟨p0, hp0⟩ := booleanConditions_nonempty hc
  have hJne : ∃ j, j ∈ J := by
    by_contra hno
    have hall : ∀ C, C ∈ range A → C = (∅ : V) := by
      intro C hC
      obtain ⟨j, hj, -⟩ := hA.exists_index hC
      exact absurd ⟨j, hj⟩ hno
    have h0 := glue_regularJoin_eq_empty hR hall
    rw [hA.2.2.2.2.2] at h0
    rw [h0] at hp0
    exact not_mem_empty hp0
  obtain ⟨j0, hj0⟩ := hJne
  have hj0X : g ‘ (A ‘ j0) ∈ coneImageFamily J A g :=
    (mem_coneImageFamily_iff J A g _).mpr ⟨j0, hj0, rfl⟩
  have hSreg : IsForcingRegular P R (regularJoin P R (coneImageFamily J A g)) :=
    regularJoin_regular hR (by
      intro C hC
      obtain ⟨j, hj, rfl⟩ := (mem_coneImageFamily_iff J A g C).mp hC
      exact (booleanConditions_regular (hcond j hj)).1)
  obtain ⟨q0, hq0⟩ := booleanConditions_nonempty (hcond j0 hj0)
  have hq0S : q0 ∈ regularJoin P R (coneImageFamily J A g) :=
    subset_regularJoin hR hj0X (booleanConditions_regular (hcond j0 hj0)) q0 hq0
  have hSmem : regularJoin P R (coneImageFamily J A g) ∈ boolCone P R e :=
    (mem_boolCone_sub_iff he).mpr
      ⟨(mem_booleanConditions_iff _ _ _).mpr ⟨hSreg, ⟨q0, hq0S⟩⟩, hSsub⟩
  obtain ⟨u, hu, hgu⟩ := glue_exists_preimage hg hSmem
  have hAu : ∀ C, C ∈ range A → C ⊆ u := by
    intro C hC
    obtain ⟨j, hj, rfl⟩ := hA.exists_index hC
    refine (glue_iso_subset_iff hc he hg (hmemc j hj) hu).mpr ?_
    rw [hgu]
    exact subset_regularJoin hR ((mem_coneImageFamily_iff J A g _).mpr ⟨j, hj, rfl⟩)
      (booleanConditions_regular (hcond j hj))
  have hcu : c ⊆ u := by
    rw [← hA.2.2.2.2.2]
    exact regularJoin_subset hR hAu
      (booleanConditions_regular ((mem_boolCone_sub_iff hc).mp hu).1)
  have huc : u = c := SetTheory.subset_antisymm ((mem_boolCone_sub_iff hc).mp hu).2 hcu
  rw [← hgu, huc]
  exact glue_iso_top hc he hg

end Transport

/-! ### Refining a cone partition -/

section Refine

variable {P R a I K A N : V}

/-- A cone partition of `a` over `I` whose pieces are themselves partitioned over `K`, with the
refined pieces read off a single function `N` on `I ×ˢ K`, is a cone partition of `a` over
`I ×ˢ K`. The last hypothesis is the join clause in the form it is used: `A ‘ i` is below every
regular set containing all its refined pieces. -/
theorem conePartition_refine (hR : IsForcingPreorder P R)
    (hA : IsConePartition P R a I A) (hN : IsFunction N) (hNdom : domain N = I ×ˢ K)
    (hcond : ∀ i, i ∈ I → ∀ k, k ∈ K → N ‘ (⟨i, k⟩ₖ : V) ∈ booleanConditions P R)
    (hsub : ∀ i, i ∈ I → ∀ k, k ∈ K → N ‘ (⟨i, k⟩ₖ : V) ⊆ A ‘ i)
    (hdisj : ∀ i, i ∈ I → ∀ k, k ∈ K → ∀ k', k' ∈ K → k ≠ k' →
      (N ‘ (⟨i, k⟩ₖ : V)) ∩ (N ‘ (⟨i, k'⟩ₖ : V)) = (∅ : V))
    (hjoin : ∀ i, i ∈ I → ∀ T, IsForcingRegular P R T →
      (∀ k, k ∈ K → N ‘ (⟨i, k⟩ₖ : V) ⊆ T) → A ‘ i ⊆ T) :
    IsConePartition P R a (I ×ˢ K) N := by
  have hNf : IsFunction N := hN
  have hpieceB : ∀ z, z ∈ I ×ˢ K → N ‘ z ∈ booleanConditions P R := by
    intro z hz
    obtain ⟨i, hi, k, hk, rfl⟩ := mem_prod_iff.mp hz
    exact hcond i hi k hk
  have hpieceA : ∀ z, z ∈ I ×ˢ K → N ‘ z ⊆ a := by
    intro z hz
    obtain ⟨i, hi, k, hk, rfl⟩ := mem_prod_iff.mp hz
    exact subset_trans (hsub i hi k hk) (hA.2.2.2.1 i hi)
  have hmemran : ∀ z, z ∈ I ×ˢ K → N ‘ z ∈ range N := fun z hz ↦
    mem_range_of_kpair_mem (kpair_value_mem (hNdom ▸ hz))
  have hranmem : ∀ C, C ∈ range N → ∃ z, z ∈ I ×ˢ K ∧ C = N ‘ z := by
    intro C hC
    obtain ⟨z, hz⟩ := mem_range_iff.mp hC
    exact ⟨z, hNdom ▸ mem_domain_of_kpair_mem hz, (value_eq_of_kpair_mem hz).symm⟩
  refine ⟨hN, hNdom, hpieceB, hpieceA, ?_, ?_⟩
  · intro z hz z' hz' hne
    obtain ⟨i, hi, k, hk, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨i', hi', k', hk', rfl⟩ := mem_prod_iff.mp hz'
    by_cases hii : i = i'
    · subst hii
      refine hdisj i hi k hk k' hk' (fun hkk ↦ hne ?_)
      rw [hkk]
    · refine glue_eq_empty_of_forall (fun w hw ↦ ?_)
      obtain ⟨hw1, hw2⟩ := mem_inter_iff.mp hw
      have hd := hA.2.2.2.2.1 i hi i' hi' hii
      have : w ∈ (A ‘ i) ∩ (A ‘ i') :=
        mem_inter_iff.mpr ⟨hsub i hi k hk w hw1, hsub i' hi' k' hk' w hw2⟩
      rw [hd] at this
      exact not_mem_empty this
  · have hTreg : IsForcingRegular P R (regularJoin P R (range N)) :=
      regularJoin_regular hR (by
        intro C hC
        obtain ⟨z, hz, rfl⟩ := hranmem C hC
        exact (booleanConditions_regular (hpieceB z hz)).1)
    have hareg : IsForcingRegular P R a := by
      rw [← hA.2.2.2.2.2]
      exact regularJoin_regular hR (fun C hC ↦ hA.range_subset_poset hC)
    refine SetTheory.subset_antisymm ?_ ?_
    · refine regularJoin_subset hR ?_ hareg
      intro C hC
      obtain ⟨z, hz, rfl⟩ := hranmem C hC
      exact hpieceA z hz
    · rw [← hA.2.2.2.2.2]
      refine regularJoin_subset hR ?_ hTreg
      intro C hC
      obtain ⟨i, hi, rfl⟩ := hA.exists_index hC
      refine hjoin i hi _ hTreg (fun k hk ↦ ?_)
      exact subset_regularJoin hR (hmemran _ (kpair_mem_iff.mpr ⟨hi, hk⟩))
        (booleanConditions_regular (hcond i hi k hk))

end Refine

/-! ### Reindexing a cone partition -/

/-- The piece of `A` at the image of `k` under `h`. -/
noncomputable def reindexPiece (A h k : V) : V := A ‘ (h ‘ k)

instance reindexPiece_definable (A h : V) : ℒₛₑₜ-function₁[V] (reindexPiece A h) := by
  unfold reindexPiece
  definability

/-- The `k`-th refined piece: the image of `A2 ‘ π₂ k` under the inverse of `F ‘ π₁ k`. -/
noncomputable def refinePiece (F A2 z : V) : V :=
  (converseGraph (F ‘ (kpair.π₁ z))) ‘ (A2 ‘ (kpair.π₂ z))

instance refinePiece_definable (F A2 : V) : ℒₛₑₜ-function₁[V] (refinePiece F A2) := by
  unfold refinePiece
  definability

theorem value_map_definable (A : V) : ℒₛₑₜ-function₁[V] (fun i ↦ A ‘ i) := by definability

theorem kpair_left_definable (i0 : V) : ℒₛₑₜ-function₁[V] (fun k ↦ (⟨i0, k⟩ₖ : V)) := by
  definability

theorem refinePiece_kpair (F A2 i k : V) :
    refinePiece F A2 (⟨i, k⟩ₖ : V) = (converseGraph (F ‘ i)) ‘ (A2 ‘ k) := by
  simp only [refinePiece, kpair.π₁_kpair, kpair.π₂_kpair]

section Reindex

variable {P R a J K A h : V}

/-- A cone partition transported along a bijection of index sets. -/
theorem conePartition_reindex (hA : IsConePartition P R a J A)
    (hmaps : ∀ k, k ∈ K → h ‘ k ∈ J)
    (hinj : ∀ k, k ∈ K → ∀ k', k' ∈ K → h ‘ k = h ‘ k' → k = k')
    (hsurj : ∀ j, j ∈ J → ∃ k, k ∈ K ∧ h ‘ k = j) :
    IsConePartition P R a K
      (definableGraph K (reindexPiece A h) (reindexPiece_definable A h)) := by
  have hval : ∀ k, k ∈ K →
      (definableGraph K (reindexPiece A h) (reindexPiece_definable A h) : V) ‘ k
        = A ‘ (h ‘ k) :=
    fun k hk ↦ value_definableGraph _ _ _ hk
  refine ⟨definableGraph_isFunction _ _ _, domain_definableGraph _ _ _, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [hval k hk]
    exact hA.2.2.1 _ (hmaps k hk)
  · intro k hk
    rw [hval k hk]
    exact hA.2.2.2.1 _ (hmaps k hk)
  · intro k hk k' hk' hne
    rw [hval k hk, hval k' hk']
    exact hA.2.2.2.2.1 _ (hmaps k hk) _ (hmaps k' hk')
      (fun he ↦ hne (hinj k hk k' hk' he))
  · have hran : range (definableGraph K (reindexPiece A h) (reindexPiece_definable A h) : V)
      = range A := by
      rw [range_definableGraph]
      apply mem_ext
      intro w
      rw [repl_spec]
      simp only [reindexPiece]
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact hA.value_mem_range (hmaps k hk)
      · intro hw
        obtain ⟨j, hj, rfl⟩ := hA.exists_index hw
        obtain ⟨k, hk, hkj⟩ := hsurj j hj
        exact ⟨k, hk, by rw [hkj]⟩
    rw [hran]
    exact hA.2.2.2.2.2

end Reindex

/-! ### Isomorphisms between two cones, as a set -/

/-- The isomorphisms of the cone of `x` onto the cone of `y`. -/
noncomputable def coneIsoSet (P R x y : V) : V :=
  {f ∈ ℘ (forcingCone (booleanConditions P R) (booleanOrder P R) x ×ˢ
      forcingCone (booleanConditions P R) (booleanOrder P R) y) ;
    IsForcingIsomorphism
      (forcingCone (booleanConditions P R) (booleanOrder P R) x)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) x))
      (forcingCone (booleanConditions P R) (booleanOrder P R) y)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) y)) f}

theorem mem_coneIsoSet_iff (P R x y f : V) :
    f ∈ coneIsoSet P R x y ↔
      f ∈ ℘ (forcingCone (booleanConditions P R) (booleanOrder P R) x ×ˢ
          forcingCone (booleanConditions P R) (booleanOrder P R) y) ∧
        IsForcingIsomorphism
          (forcingCone (booleanConditions P R) (booleanOrder P R) x)
          (restrictedOrder (booleanOrder P R)
            (forcingCone (booleanConditions P R) (booleanOrder P R) x))
          (forcingCone (booleanConditions P R) (booleanOrder P R) y)
          (restrictedOrder (booleanOrder P R)
            (forcingCone (booleanConditions P R) (booleanOrder P R) y)) f := mem_sep_iff

/-- The isomorphisms of the cone of `A ‘ i` onto the cone of `B ‘ i`, as a family in `i`. -/
noncomputable def coneIsoFamily (P R A B i : V) : V := coneIsoSet P R (A ‘ i) (B ‘ i)

instance coneIsoFamily_definable (P R A B : V) :
    ℒₛₑₜ-function₁[V] (coneIsoFamily P R A B) := by
  have hd : ℒₛₑₜ-relation[V] (fun S i ↦ ∀ f, f ∈ S ↔
      (f ∈ ℘ (forcingCone (booleanConditions P R) (booleanOrder P R) (A ‘ i) ×ˢ
          forcingCone (booleanConditions P R) (booleanOrder P R) (B ‘ i)) ∧
        IsForcingIsomorphism
          (forcingCone (booleanConditions P R) (booleanOrder P R) (A ‘ i))
          (restrictedOrder (booleanOrder P R)
            (forcingCone (booleanConditions P R) (booleanOrder P R) (A ‘ i)))
          (forcingCone (booleanConditions P R) (booleanOrder P R) (B ‘ i))
          (restrictedOrder (booleanOrder P R)
            (forcingCone (booleanConditions P R) (booleanOrder P R) (B ‘ i))) f)) := by
    definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = coneIsoFamily P R A B (v 1) ↔ _
  rw [mem_ext_iff]
  exact ⟨fun h f ↦ (h f).trans (mem_coneIsoSet_iff P R (A ‘ (v 1)) (B ‘ (v 1)) f),
    fun h f ↦ (h f).trans (mem_coneIsoSet_iff P R (A ‘ (v 1)) (B ‘ (v 1)) f).symm⟩

/-! ### Homogeneity of the Levy algebra -/

section Levy

variable {κ U a b : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)

include hAC hU hc hω hκ in
/-- Homogeneity of the Boolean completion of `Coll(ω, <κ)`: the cone of every nonzero condition is
isomorphic to the whole completion. -/
theorem levy_cone_isomorphic_completion
    (ha : a ∈ booleanConditions (levyCollapse κ) (levyOrder κ)) :
    ∃ F, IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) a)
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) a))
      (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) F := by
  have hPre : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  have hBpre : IsForcingPreorder (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) :=
    (booleanOrder_poset _ _).1
  have hPne : ∃ p, p ∈ (levyCollapse κ : V) := ⟨(∅ : V), empty_mem_levyCollapse κ⟩
  have hTop : (levyCollapse κ : V) ∈ booleanConditions (levyCollapse κ) (levyOrder κ) :=
    top_mem_booleanConditions hPne
  obtain ⟨I, A, F, hIcard, hIne, hAfun, hAdom, hAcond, hAsub, hAdisj, hAjoin,
    hFfun, hFdom, hFiso⟩ := levy_exists_conePartition hAC hU hc hω hκ ha
  have hApart : IsConePartition (levyCollapse κ) (levyOrder κ) a I A :=
    ⟨hAfun, hAdom, hAcond, hAsub, hAdisj, hAjoin⟩
  -- `range A` is an antichain, so `I` is small
  have hAinj : ∀ i, i ∈ I → ∀ j, j ∈ I → A ‘ i = A ‘ j → i = j := by
    intro i hi j hj he
    by_contra hne
    have hd := hAdisj i hi j hj hne
    rw [he] at hd
    obtain ⟨p, hp⟩ := booleanConditions_nonempty (hAcond j hj)
    have hpp : p ∈ (A ‘ j) ∩ (A ‘ j) := mem_inter_iff.mpr ⟨hp, hp⟩
    rw [hd] at hpp
    exact not_mem_empty hpp
  have hanti : IsForcingAntichain (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) (range A) := by
    refine ⟨fun C hC ↦ ?_, ?_⟩
    · obtain ⟨i, hi, rfl⟩ := hApart.exists_index hC
      exact hAcond i hi
    · intro C hC D hD hne hcompat
      obtain ⟨i, hi, rfl⟩ := hApart.exists_index hC
      obtain ⟨j, hj, rfl⟩ := hApart.exists_index hD
      obtain ⟨p, hp⟩ := (boolean_compatible_iff (hAcond i hi) (hAcond j hj)).mp hcompat
      have hij : i ≠ j := fun he ↦ hne (by rw [he])
      have hd := hAdisj i hi j hj hij
      rw [hd] at hp
      exact not_mem_empty hp
  have hnotI : ¬ (κ : V) ≤# I := by
    intro hle
    refine levyBooleanAntichain_not_cardLE hAC hU hc hω hκ hanti (hle.trans ?_)
    exact cardLE_of_injective_map (fun i ↦ A ‘ i) (value_map_definable A)
      (fun i hi ↦ hApart.value_mem_range hi) hAinj
  have hIwo : IsWellOrderable I := wellOrderable_of_internalChoice hAC I
  have hγEQ : wellOrderedCardinal I ≋ I := wellOrderedCardinal_cardEQ hIwo
  have hγord : IsOrdinal (wellOrderedCardinal I : V) := (wellOrderedCardinal_initial hIwo).1
  have hγκ : (wellOrderedCardinal I : V) ∈ κ := by
    rcases IsOrdinal.subset_or_supset (α := (κ : V)) (β := (wellOrderedCardinal I : V)) with h | h
    · exact absurd ((cardLE_of_subset h).trans hγEQ.1) hnotI
    · rcases IsOrdinal.subset_iff.mp h with he | hm
      · refine absurd ?_ hnotI
        rw [← he]
        exact hγEQ.1
      · exact hm
  have hγordI : IsOrdinal (wellOrderedCardinal I : V) := hγord
  obtain ⟨lam, hlamdef⟩ : ∃ lam : V, lam = (wellOrderedCardinal I : V) ∪ (ω : V) := ⟨_, rfl⟩
  have hlamord : IsOrdinal lam := by
    rw [hlamdef]
    exact ordinal_union_isOrdinal _ _
  have hlamκ : lam ∈ κ := by
    rw [hlamdef]
    exact union_mem_of_ordinals hγκ hω
  have hωlam : (ω : V) ⊆ lam := by
    rw [hlamdef]
    exact subset_union_right _ _
  have hIlam : I ≤# lam := hγEQ.2.trans (cardLE_of_subset (by
    rw [hlamdef]; exact subset_union_left _ _))
  -- the top partition
  obtain ⟨A2, hA2fun, hA2dom, hA2cond, hA2disj, hA2join, hA2cone⟩ :=
    levy_exists_top_conePartition (κ := κ) hlamκ hωlam
  have hA2part : IsConePartition (levyCollapse κ) (levyOrder κ) (levyCollapse κ) lam A2 :=
    ⟨hA2fun, hA2dom, hA2cond, fun i hi ↦ (booleanConditions_regular (hA2cond i hi)).1,
      hA2disj, hA2join⟩
  have hA2iso : ∀ k, k ∈ lam → ∃ f, IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) (A2 ‘ k))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) (A2 ‘ k)))
      (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) f := by
    intro k hk
    obtain ⟨p, hp, hpk⟩ := hA2cone k hk
    rw [hpk]
    exact levy_forcingCone_coneRegular_isomorphic hp
  -- the inverse piece isomorphisms
  have hFiso' : ∀ i, i ∈ I → IsForcingIsomorphism
      (boolCone (levyCollapse κ) (levyOrder κ) (A ‘ i))
      (boolConeOrder (levyCollapse κ) (levyOrder κ) (A ‘ i))
      (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) (F ‘ i) := hFiso
  have hginv : ∀ i, i ∈ I → IsForcingIsomorphism
      (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ))
      (boolCone (levyCollapse κ) (levyOrder κ) (A ‘ i))
      (boolConeOrder (levyCollapse κ) (levyOrder κ) (A ‘ i))
      (converseGraph (F ‘ i)) := fun i hi ↦ isForcingIsomorphism_inverse (hFiso' i hi)
  have hginv' : ∀ i, i ∈ I → IsForcingIsomorphism
      (boolCone (levyCollapse κ) (levyOrder κ) (levyCollapse κ))
      (boolConeOrder (levyCollapse κ) (levyOrder κ) (levyCollapse κ))
      (boolCone (levyCollapse κ) (levyOrder κ) (A ‘ i))
      (boolConeOrder (levyCollapse κ) (levyOrder κ) (A ‘ i))
      (converseGraph (F ‘ i)) := by
    intro i hi
    rw [boolCone_top_eq _ _ hPne, boolConeOrder_top_eq _ _ hPne]
    exact hginv i hi
  -- the refined partition of `a`
  obtain ⟨N, hNdef⟩ : ∃ N : V,
      N = definableGraph (I ×ˢ lam) (refinePiece F A2) (refinePiece_definable F A2) :=
    ⟨_, rfl⟩
  have hNval : ∀ i, i ∈ I → ∀ k, k ∈ lam →
      N ‘ (⟨i, k⟩ₖ : V) = (converseGraph (F ‘ i)) ‘ (A2 ‘ k) := by
    intro i hi k hk
    rw [hNdef, value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hi, hk⟩), refinePiece_kpair]
  have htrans : ∀ i, i ∈ I →
      (∀ k, k ∈ lam → (converseGraph (F ‘ i)) ‘ (A2 ‘ k) ∈
        booleanConditions (levyCollapse κ) (levyOrder κ)) ∧
      (∀ k, k ∈ lam → (converseGraph (F ‘ i)) ‘ (A2 ‘ k) ⊆ A ‘ i) ∧
      (∀ k, k ∈ lam → ∀ k', k' ∈ lam → k ≠ k' →
        ((converseGraph (F ‘ i)) ‘ (A2 ‘ k)) ∩ ((converseGraph (F ‘ i)) ‘ (A2 ‘ k')) =
          (∅ : V)) ∧
      regularJoin (levyCollapse κ) (levyOrder κ)
        (coneImageFamily lam A2 (converseGraph (F ‘ i))) = A ‘ i := fun i hi ↦
    coneIso_image_conePartition hPre hTop (hAcond i hi) (hginv' i hi) hA2part
  have hNpart : IsConePartition (levyCollapse κ) (levyOrder κ) a (I ×ˢ lam) N := by
    refine conePartition_refine hPre hApart
      (by rw [hNdef]; exact definableGraph_isFunction _ _ _)
      (by rw [hNdef]; exact domain_definableGraph _ _ _) ?_ ?_ ?_ ?_
    · intro i hi k hk
      rw [hNval i hi k hk]
      exact (htrans i hi).1 k hk
    · intro i hi k hk
      rw [hNval i hi k hk]
      exact (htrans i hi).2.1 k hk
    · intro i hi k hk k' hk' hne
      rw [hNval i hi k hk, hNval i hi k' hk']
      exact (htrans i hi).2.2.1 k hk k' hk' hne
    · intro i hi T hT hsubT
      rw [← (htrans i hi).2.2.2]
      refine regularJoin_subset hPre ?_ hT
      intro C hC
      obtain ⟨k, hk, rfl⟩ := (mem_coneImageFamily_iff _ _ _ _).mp hC
      rw [← hNval i hi k hk]
      exact hsubT k hk
  -- the two index sets have the same size
  have hprod1 : I ×ˢ lam ≤# lam := by
    refine (prod_cardLE_prod hIlam (CardLE.refl lam)).trans ?_
    have h := ordinal_prod_cardLE_union_omega (V := V) lam
    rwa [union_eq_iff_right.mpr hωlam] at h
  obtain ⟨i0, hi0⟩ := hIne
  have hprod2 : lam ≤# I ×ˢ lam :=
    cardLE_of_injective_map (fun k ↦ (⟨i0, k⟩ₖ : V)) (kpair_left_definable i0)
      (fun k hk ↦ kpair_mem_iff.mpr ⟨hi0, hk⟩)
      (fun k _ k' _ he ↦ (kpair_inj he).2)
  obtain ⟨hbij, hbijmem, hbijinj, hbijran⟩ :=
    exists_bijection_of_cardEQ (A := I ×ˢ lam) (B := lam) ⟨hprod1, hprod2⟩
  have hbijfun : IsFunction hbij := IsFunction.of_mem hbijmem
  have hbijdom : domain hbij = I ×ˢ lam := domain_eq_of_mem_function hbijmem
  have hbijmaps : ∀ z, z ∈ I ×ˢ lam → hbij ‘ z ∈ lam := fun z hz ↦
    function_value_mem hbijmem hz
  have hbijinj' : ∀ z, z ∈ I ×ˢ lam → ∀ z', z' ∈ I ×ˢ lam → hbij ‘ z = hbij ‘ z' → z = z' := by
    intro z hz z' hz' he
    refine hbijinj z z' (hbij ‘ z) (kpair_value_mem (hbijdom ▸ hz)) ?_
    rw [he]
    exact kpair_value_mem (hbijdom ▸ hz')
  have hbijsurj : ∀ j, j ∈ lam → ∃ z, z ∈ I ×ˢ lam ∧ hbij ‘ z = j := by
    intro j hj
    obtain ⟨z, hz⟩ := mem_range_iff.mp (hbijran ▸ hj)
    exact ⟨z, hbijdom ▸ mem_domain_of_kpair_mem hz, value_eq_of_kpair_mem hz⟩
  obtain ⟨A2', hA2'def⟩ : ∃ A2' : V,
      A2' = definableGraph (I ×ˢ lam) (reindexPiece A2 hbij) (reindexPiece_definable A2 hbij) :=
    ⟨_, rfl⟩
  have hA2'val : ∀ z, z ∈ I ×ˢ lam → A2' ‘ z = A2 ‘ (hbij ‘ z) := by
    intro z hz
    rw [hA2'def, value_definableGraph _ _ _ hz]
    rfl
  have hA2'part : IsConePartition (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
      (I ×ˢ lam) A2' := by
    rw [hA2'def]
    exact conePartition_reindex hA2part hbijmaps hbijinj' hbijsurj
  -- every piece on both sides has a cone isomorphic to the whole completion
  have hNiso : ∀ z, z ∈ I ×ˢ lam → ∃ f, IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) (N ‘ z))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) (N ‘ z)))
      (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) f := by
    intro z hz
    obtain ⟨i, hi, k, hk, rfl⟩ := mem_prod_iff.mp hz
    obtain ⟨w, hw⟩ := exists_coneIsomorphism_of_isomorphism (hginv i hi) (hA2cond k hk)
    have hmemcone : (converseGraph (F ‘ i)) ‘ (A2 ‘ k) ∈
        boolCone (levyCollapse κ) (levyOrder κ) (A ‘ i) :=
      function_value_mem (hginv i hi).1 (hA2cond k hk)
    simp only [boolCone, boolConeOrder] at hw
    rw [forcingCone_forcingCone hBpre (hAcond i hi) hmemcone,
      restrictedOrder_forcingCone_forcingCone hBpre (hAcond i hi) hmemcone] at hw
    obtain ⟨f2, hf2⟩ := hA2iso k hk
    rw [hNval i hi k hk]
    exact ⟨compose (converseGraph w) f2,
      isForcingIsomorphism_compose (isForcingIsomorphism_inverse hw) hf2⟩
  have hA2'iso : ∀ z, z ∈ I ×ˢ lam → ∃ f, IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) (A2' ‘ z))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) (A2' ‘ z)))
      (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) f := by
    intro z hz
    rw [hA2'val z hz]
    exact hA2iso _ (hbijmaps z hz)
  -- choose the matching isomorphisms
  have hnonempty : ∀ z, z ∈ I ×ˢ lam →
      IsNonempty (coneIsoFamily (levyCollapse κ) (levyOrder κ) N A2' z) := by
    intro z hz
    obtain ⟨f1, hf1⟩ := hNiso z hz
    obtain ⟨f2, hf2⟩ := hA2'iso z hz
    have hcomp := isForcingIsomorphism_compose hf1 (isForcingIsomorphism_inverse hf2)
    exact ⟨compose f1 (converseGraph f2), (mem_coneIsoSet_iff _ _ _ _ _).mpr
      ⟨mem_power_iff.mpr (subset_prod_of_mem_function hcomp.1), hcomp⟩⟩
  obtain ⟨Fam, hFamfun, hFamdom, hFamval⟩ :=
    choice_for_definable_family hAC (I ×ˢ lam)
      (coneIsoFamily (levyCollapse κ) (levyOrder κ) N A2')
      (coneIsoFamily_definable _ _ _ _) hnonempty
  obtain ⟨G, hG⟩ := exists_coneIsomorphism_of_conePartitions hPre ha hTop hNpart hA2'part
    hFamfun hFamdom (fun z hz ↦ ((mem_coneIsoSet_iff _ _ _ _ _).mp (hFamval z hz)).2)
  rw [forcingCone_top_eq _ _ hPne, restrictedOrder_booleanOrder_eq] at hG
  exact ⟨G, hG⟩

include hAC hU hc hω hκ in
/-- Any two cones of the Boolean completion of `Coll(ω, <κ)` are isomorphic. -/
theorem levy_cone_isomorphic_cone
    (ha : a ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hb : b ∈ booleanConditions (levyCollapse κ) (levyOrder κ)) :
    ∃ F, IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) a)
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) a))
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) b)
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) b)) F := by
  obtain ⟨F1, h1⟩ := levy_cone_isomorphic_completion hAC hU hc hω hκ ha
  obtain ⟨F2, h2⟩ := levy_cone_isomorphic_completion hAC hU hc hω hκ hb
  exact ⟨compose F1 (converseGraph F2),
    isForcingIsomorphism_compose h1 (isForcingIsomorphism_inverse h2)⟩

end Levy

end ZFVP
