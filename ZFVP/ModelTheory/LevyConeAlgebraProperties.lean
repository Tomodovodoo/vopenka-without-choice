import ZFVP.ModelTheory.LevyBooleanHomogeneity
import ZFVP.ModelTheory.LevyBooleanAntichainSupport
import ZFVP.ModelTheory.LevyGroundStages
import ZFVP.SetTheory.WellOrderedSurjection

/-! Structural properties of a cone of the Boolean completion of the Levy collapse.

Write `B` for `booleanConditions (levyCollapse κ) (levyOrder κ)` ordered by
`booleanOrder (levyCollapse κ) (levyOrder κ)`, and `B↾a` for the cone
`forcingCone B (booleanOrder …) a` with the order restricted to it, for a nonzero `a` of `B`.
This file proves the three inputs of the uniqueness theorem for the Levy algebra:

* `levy_cone_coneRegular_dense`: the regular cones of conditions of the collapse that lie below
  `a` are dense in `B↾a`. No hypothesis on `κ`; the general poset version is
  `coneRegularsBelow_dense`.

* `levy_cone_dense_cardLE`: `B↾a` has a dense subset of size at most `κ`, namely the nonzero
  values of `p ↦ coneRegular (levyCollapse κ) (levyOrder κ) p ∩ a` for `p` in the collapse.

* `levy_cone_chainCondition`: no antichain of `B↾a` has size `κ`. The route is
  `forcingCone_antichain`, which turns an antichain of a cone into an antichain of the whole
  poset, and `levyBooleanAntichain_not_cardLE`, the `κ`-chain condition of the completion.

The last two carry the standing Levy hypotheses `hAC hU hc hω hκ`, which is what the
repository's size bound `levyCollapse_cardLE_self` and chain condition
`levyAntichain_not_cardLE` need. The first needs none of them.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Cones of a general forcing poset -/

section General

variable {P R a c A : V}

/-- The nonzero conditions of the Boolean completion below `a` that are regular cones of
conditions of `P`. -/
noncomputable def coneRegularsBelow (P R a : V) : V :=
  {b ∈ booleanConditions P R ; (∃ p, p ∈ P ∧ b = coneRegular P R p) ∧ b ⊆ a}

theorem mem_coneRegularsBelow_iff (P R a b : V) :
    b ∈ coneRegularsBelow P R a ↔ b ∈ booleanConditions P R ∧
      (∃ p, p ∈ P ∧ b = coneRegular P R p) ∧ b ⊆ a := mem_sep_iff

/-- A subset of `a` that is a Boolean condition is a member of the cone of `a`. -/
theorem mem_forcingCone_booleanOrder {b : V} (hb : b ∈ booleanConditions P R)
    (ha : a ∈ booleanConditions P R) (hsub : b ⊆ a) :
    b ∈ forcingCone (booleanConditions P R) (booleanOrder P R) a :=
  (mem_forcingCone_iff _ _ _ _).mpr
    ⟨hb, (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨hb, ha, hsub⟩⟩

/-- Membership in the cone of `a`, unfolded to inclusion. -/
theorem mem_forcingCone_booleanOrder_iff {b : V} (ha : a ∈ booleanConditions P R) :
    b ∈ forcingCone (booleanConditions P R) (booleanOrder P R) a ↔
      b ∈ booleanConditions P R ∧ b ⊆ a := by
  rw [mem_forcingCone_iff]
  exact ⟨fun h ↦ ⟨h.1, ((kpair_mem_booleanOrder_iff _ _ _ _).mp h.2).2.2⟩,
    fun h ↦ ⟨h.1, (kpair_mem_booleanOrder_iff _ _ _ _).mpr ⟨h.1, ha, h.2⟩⟩⟩

/-- The order of the cone of `a`, unfolded to inclusion. -/
theorem kpair_mem_coneOrder_iff {b c : V} (ha : a ∈ booleanConditions P R) :
    ⟨b, c⟩ₖ ∈ restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) a) ↔
      (b ∈ booleanConditions P R ∧ b ⊆ a) ∧ (c ∈ booleanConditions P R ∧ c ⊆ a) ∧ b ⊆ c := by
  rw [kpair_mem_restrictedOrder_iff, mem_forcingCone_booleanOrder_iff ha,
    mem_forcingCone_booleanOrder_iff ha, kpair_mem_booleanOrder_iff]
  exact ⟨fun h ↦ ⟨h.2.1, h.2.2, h.1.2.2⟩, fun h ↦ ⟨⟨h.1.1, h.2.1.1, h.2.2⟩, h.1, h.2.1⟩⟩

/-- The regular cones of conditions of `P` lying below `a` are dense in the cone of `a`. -/
theorem coneRegularsBelow_dense (hR : IsForcingPreorder P R)
    (ha : a ∈ booleanConditions P R) :
    ForcingDense (forcingCone (booleanConditions P R) (booleanOrder P R) a)
      (restrictedOrder (booleanOrder P R)
        (forcingCone (booleanConditions P R) (booleanOrder P R) a))
      (coneRegularsBelow P R a) := by
  constructor
  · intro b hb
    obtain ⟨hbB, -, hba⟩ := (mem_coneRegularsBelow_iff P R a b).mp hb
    exact mem_forcingCone_booleanOrder hbB ha hba
  · intro c hc
    obtain ⟨hcB, hca⟩ := (mem_forcingCone_booleanOrder_iff ha).mp hc
    obtain ⟨q, hq, hqc⟩ := exists_coneRegular_subset hR hcB
    have hqB : coneRegular P R q ∈ booleanConditions P R := coneRegular_mem_booleanConditions hR hq
    refine ⟨coneRegular P R q, (mem_coneRegularsBelow_iff P R a _).mpr
      ⟨hqB, ⟨q, hq, rfl⟩, subset_trans hqc hca⟩, ?_⟩
    exact (kpair_mem_coneOrder_iff ha).mpr
      ⟨⟨hqB, subset_trans hqc hca⟩, ⟨hcB, hca⟩, hqc⟩

/-- An antichain of the cone of `a` is an antichain of the whole poset. Compatibility inside the
cone is compatibility in `P`: a common extension of two elements of the cone already lies in the
cone. -/
theorem forcingCone_antichain (hR : IsForcingPreorder P R) (ha : a ∈ P)
    (hA : IsForcingAntichain (forcingCone P R a) (restrictedOrder R (forcingCone P R a)) A) :
    IsForcingAntichain P R A := by
  refine ⟨subset_trans hA.1 (forcingCone_subset P R a), ?_⟩
  rintro b hb c hc hbc ⟨r, hr, hrb, hrc⟩
  have hbC := hA.1 b hb
  have hcC := hA.1 c hc
  obtain ⟨hbP, hba⟩ := (mem_forcingCone_iff _ _ _ _).mp hbC
  have hrC : r ∈ forcingCone P R a :=
    (mem_forcingCone_iff _ _ _ _).mpr ⟨hr, hR.2.2 r hr b hbP a ha hrb hba⟩
  exact hA.2 b hb c hc hbc
    ⟨r, hrC, (kpair_mem_restrictedOrder_iff _ _ _ _).mpr ⟨hrb, hrC, hbC⟩,
      (kpair_mem_restrictedOrder_iff _ _ _ _).mpr ⟨hrc, hrC, hcC⟩⟩

end General

/-! ### The Levy collapse -/

section Levy

variable {κ U a A : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)

omit [IsOrdinal κ] in
/-- The regular cones of conditions of `Coll(ω, <κ)` lying below a nonzero `a` are dense in the
cone of `a` in the Boolean completion. No hypothesis on `κ`. -/
theorem levy_cone_coneRegular_dense
    (ha : a ∈ booleanConditions (levyCollapse κ) (levyOrder κ)) :
    ForcingDense
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) a)
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) a))
      (coneRegularsBelow (levyCollapse κ) (levyOrder κ) a) :=
  coneRegularsBelow_dense (levyCollapse_poset κ).1 ha

/-- The nonzero values of `p ↦ coneRegular p ∩ a` for `p` a condition of the collapse. -/
noncomputable def levyConeDenseSet (κ a : V) : V :=
  {b ∈ booleanConditions (levyCollapse κ) (levyOrder κ) ;
    ∃ p, p ∈ levyCollapse κ ∧ b = coneRegular (levyCollapse κ) (levyOrder κ) p ∩ a}

theorem mem_levyConeDenseSet_iff (κ a b : V) :
    b ∈ levyConeDenseSet κ a ↔ b ∈ booleanConditions (levyCollapse κ) (levyOrder κ) ∧
      ∃ p, p ∈ levyCollapse κ ∧ b = coneRegular (levyCollapse κ) (levyOrder κ) p ∩ a :=
  mem_sep_iff

omit [IsOrdinal κ] in
/-- `levyConeDenseSet κ a` is dense in the cone of `a`. -/
theorem levyConeDenseSet_dense
    (ha : a ∈ booleanConditions (levyCollapse κ) (levyOrder κ)) :
    ForcingDense
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) a)
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) a))
      (levyConeDenseSet κ a) := by
  constructor
  · intro b hb
    obtain ⟨hbB, p, -, rfl⟩ := (mem_levyConeDenseSet_iff κ a b).mp hb
    exact mem_forcingCone_booleanOrder hbB ha (fun z hz ↦ (mem_inter_iff.mp hz).2)
  · intro c hc
    obtain ⟨hcB, hca⟩ := (mem_forcingCone_booleanOrder_iff ha).mp hc
    obtain ⟨q, hq, hqc⟩ := exists_coneRegular_subset (levyCollapse_poset κ).1 hcB
    have hqa : coneRegular (levyCollapse κ) (levyOrder κ) q ⊆ a := subset_trans hqc hca
    have hqeq : coneRegular (levyCollapse κ) (levyOrder κ) q ∩ a =
        coneRegular (levyCollapse κ) (levyOrder κ) q := by
      apply SetTheory.subset_antisymm (fun z hz ↦ (mem_inter_iff.mp hz).1)
      exact fun z hz ↦ mem_inter_iff.mpr ⟨hz, hqa z hz⟩
    have hqB : coneRegular (levyCollapse κ) (levyOrder κ) q ∈
        booleanConditions (levyCollapse κ) (levyOrder κ) :=
      coneRegular_mem_booleanConditions (levyCollapse_poset κ).1 hq
    refine ⟨coneRegular (levyCollapse κ) (levyOrder κ) q,
      (mem_levyConeDenseSet_iff κ a _).mpr ⟨hqB, q, hq, hqeq.symm⟩, ?_⟩
    exact (kpair_mem_coneOrder_iff ha).mpr ⟨⟨hqB, hqa⟩, ⟨hcB, hca⟩, hqc⟩

include hAC hU hc hω hκ in
/-- The cone of a nonzero condition `a` of the Boolean completion of `Coll(ω, <κ)` has a dense
subset of size at most `κ`. The bound on the size comes from `levyCollapse_cardLE_self`, that
`Coll(ω, <κ)` has at most `κ` conditions below a measurable `κ`; the dense set itself is the
image of the collapse under `p ↦ coneRegular p ∩ a` with the empty values dropped, and needs no
hypothesis on `κ` (`levyConeDenseSet_dense`). -/
theorem levy_cone_dense_cardLE
    (ha : a ∈ booleanConditions (levyCollapse κ) (levyOrder κ)) :
    ∃ D, ForcingDense
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) a)
        (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ)) a))
        D ∧ D ≤# κ := by
  refine ⟨levyConeDenseSet κ a, levyConeDenseSet_dense ha, ?_⟩
  refine CardLE.trans ?_ (levyCollapse_cardLE_self hAC hU hc hω hκ)
  refine cardLE_of_separating_relation (wellOrderable_of_internalChoice hAC (levyCollapse κ))
    (fun b p ↦ b = coneRegular (levyCollapse κ) (levyOrder κ) p ∩ a) (by definability) ?_ ?_
  · intro b hb
    obtain ⟨-, p, hp, hbp⟩ := (mem_levyConeDenseSet_iff κ a b).mp hb
    exact ⟨p, hp, hbp⟩
  · intro x _ z _ y _ hx hz
    exact hx.trans hz.symm

include hAC hU hc hω hκ in
/-- No antichain of the Boolean completion of `Coll(ω, <κ)` has size `κ`. Choosing a condition
inside each element of the antichain gives an antichain of the collapse of the same size, and
`levyAntichain_not_cardLE` bounds that. -/
theorem levyBooleanAntichain_not_cardLE
    (hA : IsForcingAntichain (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) A) : ¬κ ≤# A := by
  intro hκA
  have hne : ∀ x ∈ A, IsNonempty ((fun y : V ↦ y) x) := by
    intro x hx
    obtain ⟨p, hp⟩ := booleanConditions_nonempty (hA.1 x hx)
    exact ⟨p, hp⟩
  obtain ⟨f, hf, hdom, hval⟩ :=
    choice_for_definable_family hAC A (fun y : V ↦ y) (by definability) hne
  have := hf
  have hanti := levyBooleanAntichain_selector_antichain hA hdom hval
  have hArange : A ≤# range f := by
    refine cardLE_of_injective_map (fun x ↦ f ‘ x) (by definability) ?_ ?_
    · intro x hx
      exact mem_range_of_kpair_mem (kpair_value_mem (hdom ▸ hx))
    · intro x hx z hz heq
      by_contra hxz
      refine hA.2 x hx z hz hxz ((boolean_compatible_iff (hA.1 x hx) (hA.1 z hz)).mpr ?_)
      exact ⟨f ‘ x, mem_inter_iff.mpr ⟨hval x hx, heq ▸ hval z hz⟩⟩
  exact levyAntichain_not_cardLE hAC hU hc hω hκ hanti (hκA.trans hArange)

include hAC hU hc hω hκ in
/-- The `κ`-chain condition of a cone: every antichain of `B↾a` is an antichain of `B`, so it does
not have size `κ`. Stated the way `levyAntichain_not_cardLE` states the chain condition of the
collapse. -/
theorem levy_cone_chainCondition
    (ha : a ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hA : IsForcingAntichain
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) a)
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) a))
      A) : ¬κ ≤# A :=
  levyBooleanAntichain_not_cardLE hAC hU hc hω hκ
    (forcingCone_antichain (booleanOrder_poset _ _).1 ha hA)

end Levy

end ZFVP
