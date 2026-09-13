import ZFVP.ModelTheory.LevyConeAlgebraProperties
import ZFVP.SetTheory.MaximalAntichains
import ZFVP.SetTheory.RegularSetAlgebra
import ZFVP.SetTheory.WellOrderingChoice

/-! Partitions of the Boolean completion of the Levy collapse into cones of conditions.

Write `B` for `booleanConditions (levyCollapse κ) (levyOrder κ)` with the order
`booleanOrder (levyCollapse κ) (levyOrder κ)`.

Two results.

* `levy_exists_conePartition`: every nonzero `a` of `B` is the regular join of a disjoint family
  of regular cones of conditions of `Coll(ω, <κ)`, indexed by a nonempty set of size at most `κ`,
  and each piece carries an isomorphism of its cone in `B` onto all of `B`. The family is a
  maximal antichain of the cone of `a` taken inside the dense set of regular cones below `a`; the
  isomorphisms come from `levy_forcingCone_coneRegular_isomorphic`, chosen with
  `choice_for_definable_family`.

* `levy_exists_top_conePartition`: for an infinite `lam ∈ κ` the whole poset, the top of `B`,
  is the join of `lam` pairwise disjoint cones. The conditions are the one point functions
  sending the coordinate `⟨∅, lam⟩ₖ` to `β`, for `β ∈ lam`. Distinct `β` give incompatible
  conditions, and every condition is compatible with one of them, so the family is predense.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Two facts about regular joins in a general forcing preorder -/

section General

variable {P R X p q : V}

/-- A predense family of subsets joins to the whole poset: if below every condition there is a
condition lying in some member of `X`, then the regular join of `X` is `P`. -/
theorem regularJoin_eq_self_of_predense
    (hpre : ∀ q ∈ P, ∃ C, C ∈ X ∧ ∃ r, r ∈ C ∧ ⟨r, q⟩ₖ ∈ R) : regularJoin P R X = P := by
  apply SetTheory.subset_antisymm (regularJoin_subset_poset P R X)
  intro p hp
  refine (mem_regularJoin_iff _ _ _ _).mpr ⟨hp, fun q hq _ ↦ ?_⟩
  obtain ⟨C, hC, r, hrC, hrq⟩ := hpre q hq
  exact ⟨r, ⟨C, hC, hrC⟩, hrq⟩

/-- The regular cones of two incompatible conditions are disjoint. -/
theorem coneRegular_inter_eq_empty (hR : IsForcingPreorder P R)
    (h : ¬ForcingCompatible P R p q) : coneRegular P R p ∩ coneRegular P R q = (∅ : V) := by
  ext r
  simp only [mem_inter_iff, not_mem_empty, iff_false, not_and]
  intro hrp hrq
  obtain ⟨hrP, hh⟩ := mem_coneRegular_iff.mp hrp
  obtain ⟨s, hsP, hsp, hsr⟩ := hh r hrP (hR.2.1 r hrP)
  have hpP : p ∈ P := (kpair_mem_iff.mp (hR.1 _ hsp)).2
  have hsq : s ∈ coneRegular P R q := (coneRegular_regular hR q).2.1 r hrq s hsP hsr
  obtain ⟨-, hh2⟩ := mem_coneRegular_iff.mp hsq
  obtain ⟨t, htP, htq, hts⟩ := hh2 s hsP (hR.2.1 s hsP)
  exact h ⟨t, htP, hR.2.2 t htP s hsP p hpP hts hsp, htq⟩

end General

/-! ### The identity graph -/

section Identity

theorem repl_id_eq (X : V) : repl (fun x : V ↦ x) (by definability) X = X := by
  ext y
  rw [repl_spec]
  exact ⟨fun ⟨x, hx, he⟩ ↦ he ▸ hx, fun hy ↦ ⟨y, hy, rfl⟩⟩

theorem range_identityGraph (X : V) :
    range (definableGraph X (fun x : V ↦ x) (by definability)) = X := by
  rw [range_definableGraph]
  exact repl_id_eq X

end Identity

/-! ### Isomorphism witnesses for a cone -/

section Witnesses

/-- The cone of `b` in the Boolean completion of `Coll(ω, <κ)`. -/
noncomputable def levyBoolCone (κ b : V) : V :=
  forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
    (booleanOrder (levyCollapse κ) (levyOrder κ)) b

instance levyBoolCone_definable : ℒₛₑₜ-function₂[V] levyBoolCone := by
  unfold levyBoolCone
  definability

instance restrictedOrder_definable : ℒₛₑₜ-function₂[V] restrictedOrder := by
  unfold restrictedOrder
  definability

/-- The order of that cone. -/
noncomputable def levyBoolConeOrder (κ b : V) : V :=
  restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ)) (levyBoolCone κ b)

instance levyBoolConeOrder_definable : ℒₛₑₜ-function₂[V] levyBoolConeOrder := by
  unfold levyBoolConeOrder
  definability

/-- `G` is an isomorphism of the cone of `b` onto the whole Boolean completion. -/
def IsLevyConeIso (κ b G : V) : Prop :=
  IsForcingIsomorphism (levyBoolCone κ b) (levyBoolConeOrder κ b)
    (booleanConditions (levyCollapse κ) (levyOrder κ))
    (booleanOrder (levyCollapse κ) (levyOrder κ)) G

instance isLevyConeIso_definable : ℒₛₑₜ-relation₃[V] IsLevyConeIso := by
  unfold IsLevyConeIso
  definability

/-- The isomorphisms of the cone of `b` onto the whole completion, as a set. -/
noncomputable def levyConeIsoSet (κ b : V) : V :=
  {G ∈ ℘ (levyBoolCone κ b ×ˢ booleanConditions (levyCollapse κ) (levyOrder κ)) ;
    IsLevyConeIso κ b G}

theorem mem_levyConeIsoSet_iff (κ b G : V) :
    G ∈ levyConeIsoSet κ b ↔
      G ∈ ℘ (levyBoolCone κ b ×ˢ booleanConditions (levyCollapse κ) (levyOrder κ)) ∧
        IsLevyConeIso κ b G := mem_sep_iff

instance levyConeIsoSet_definable (κ : V) : ℒₛₑₜ-function₁[V] (levyConeIsoSet κ) := by
  have hd : ℒₛₑₜ-relation[V] (fun S b ↦ ∀ G, G ∈ S ↔
      G ∈ ℘ (levyBoolCone κ b ×ˢ booleanConditions (levyCollapse κ) (levyOrder κ)) ∧
        IsLevyConeIso κ b G) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = levyConeIsoSet κ (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [levyConeIsoSet, mem_sep_iff]

end Witnesses

/-! ### Every nonzero condition splits into cones -/

section Partition

variable {κ U a : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)

omit [IsOrdinal κ] in
/-- Inside the cone of `a`, two nonzero conditions below `a` are compatible exactly when they
meet. -/
theorem levy_cone_compatible_iff {b c : V}
    (ha : a ∈ booleanConditions (levyCollapse κ) (levyOrder κ))
    (hb : b ∈ forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) a)
    (hc' : c ∈ forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) a) :
    ForcingCompatible
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) a)
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) a))
      b c ↔ ∃ x, x ∈ b ∩ c := by
  obtain ⟨hbB, hba⟩ := (mem_forcingCone_booleanOrder_iff ha).mp hb
  obtain ⟨hcB, hca⟩ := (mem_forcingCone_booleanOrder_iff ha).mp hc'
  constructor
  · rintro ⟨d, hd, hdb, hdc⟩
    obtain ⟨hdB, -⟩ := (mem_forcingCone_booleanOrder_iff ha).mp hd
    obtain ⟨x, hx⟩ := booleanConditions_nonempty hdB
    obtain ⟨-, -, hdb'⟩ := (kpair_mem_coneOrder_iff ha).mp hdb
    obtain ⟨-, -, hdc'⟩ := (kpair_mem_coneOrder_iff ha).mp hdc
    exact ⟨x, mem_inter_iff.mpr ⟨hdb' x hx, hdc' x hx⟩⟩
  · rintro ⟨x, hx⟩
    have hbc : b ∩ c ∈ booleanConditions (levyCollapse κ) (levyOrder κ) :=
      inter_mem_booleanConditions hbB hcB hx
    have hbca : b ∩ c ⊆ a := fun z hz ↦ hba z (mem_inter_iff.mp hz).1
    refine ⟨b ∩ c, (mem_forcingCone_booleanOrder_iff ha).mpr ⟨hbc, hbca⟩, ?_, ?_⟩
    · exact (kpair_mem_coneOrder_iff ha).mpr
        ⟨⟨hbc, hbca⟩, ⟨hbB, hba⟩, fun z hz ↦ (mem_inter_iff.mp hz).1⟩
    · exact (kpair_mem_coneOrder_iff ha).mpr
        ⟨⟨hbc, hbca⟩, ⟨hcB, hca⟩, fun z hz ↦ (mem_inter_iff.mp hz).2⟩

include hAC hU hc hω hκ in
/-- Every nonzero condition `a` of the Boolean completion of `Coll(ω, <κ)` is the regular join of
a disjoint family of regular cones of conditions of the collapse, indexed by a nonempty set of
size at most `κ`, with an isomorphism of the cone of each piece onto the whole completion. -/
theorem levy_exists_conePartition
    (ha : a ∈ booleanConditions (levyCollapse κ) (levyOrder κ)) :
    ∃ I A F, I ≤# κ ∧ (∃ i : V, i ∈ I) ∧
      IsFunction A ∧ domain A = I ∧
      (∀ i, i ∈ I → A ‘ i ∈ booleanConditions (levyCollapse κ) (levyOrder κ)) ∧
      (∀ i, i ∈ I → A ‘ i ⊆ a) ∧
      (∀ i, i ∈ I → ∀ j, j ∈ I → i ≠ j → (A ‘ i) ∩ (A ‘ j) = (∅ : V)) ∧
      regularJoin (levyCollapse κ) (levyOrder κ) (range A) = a ∧
      IsFunction F ∧ domain F = I ∧
      (∀ i, i ∈ I → IsForcingIsomorphism
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ)) (A ‘ i))
        (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ)) (A ‘ i)))
        (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ)) (F ‘ i)) := by
  have hP := (levyCollapse_poset κ).1
  have hBpos := (booleanOrder_poset (levyCollapse κ) (levyOrder κ)).1
  have hareg : IsForcingRegular (levyCollapse κ) (levyOrder κ) a :=
    ((mem_booleanConditions_iff _ _ a).mp ha).1
  set Ca := forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
    (booleanOrder (levyCollapse κ) (levyOrder κ)) a with hCa
  set Ra := restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ)) Ca with hRa
  have hCaB : Ca ⊆ booleanConditions (levyCollapse κ) (levyOrder κ) := forcingCone_subset _ _ _
  have hRapre : IsForcingPreorder Ca Ra := restrictedOrder_preorder hBpos hCaB
  set D := coneRegularsBelow (levyCollapse κ) (levyOrder κ) a with hDdef
  have hDCa : D ⊆ Ca := (levy_cone_coneRegular_dense ha).1
  obtain ⟨I, hanti, hID, hmax⟩ :=
    exists_maximalAntichain hRapre hDCa (wellOrderable_of_internalChoice hAC D)
  -- the members of `I` are regular cones below `a`
  have hIcone : ∀ i, i ∈ I → ∃ p, p ∈ levyCollapse κ ∧
      i = coneRegular (levyCollapse κ) (levyOrder κ) p := by
    intro i hi
    exact ((mem_coneRegularsBelow_iff _ _ _ i).mp (hID i hi)).2.1
  have hIB : ∀ i, i ∈ I → i ∈ booleanConditions (levyCollapse κ) (levyOrder κ) := by
    intro i hi
    exact ((mem_coneRegularsBelow_iff _ _ _ i).mp (hID i hi)).1
  have hIa : ∀ i, i ∈ I → i ⊆ a := by
    intro i hi
    exact ((mem_coneRegularsBelow_iff _ _ _ i).mp (hID i hi)).2.2
  -- the identity function on `I`
  set A := definableGraph I (fun x : V ↦ x) (by definability) with hAdef
  have hAfun : IsFunction A := definableGraph_isFunction _ _ _
  have hAdom : domain A = I := domain_definableGraph _ _ _
  have hAval : ∀ i, i ∈ I → A ‘ i = i := by
    intro i hi
    exact value_definableGraph I (fun x : V ↦ x) (by definability) hi
  have hArange : range A = I := range_identityGraph I
  -- a nonzero condition below `a` whose regular cone sits in `D`
  have hDmem : ∀ q, q ∈ levyCollapse κ → q ∈ a →
      coneRegular (levyCollapse κ) (levyOrder κ) q ∈ D := by
    intro q hq hqa
    refine (mem_coneRegularsBelow_iff _ _ _ _).mpr
      ⟨coneRegular_mem_booleanConditions hP hq, ⟨q, hq, rfl⟩, ?_⟩
    exact coneRegular_subset_of_mem hP hareg hqa
  -- `I` is nonempty
  have hInonempty : ∃ i : V, i ∈ I := by
    obtain ⟨q, hq, hqa⟩ := exists_coneRegular_subset hP ha
    obtain ⟨i, hi, -⟩ := hmax _ (hDmem q hq (hqa q (self_mem_coneRegular hP hq)))
    exact ⟨i, hi⟩
  -- the pieces are pairwise disjoint
  have hdisj : ∀ i, i ∈ I → ∀ j, j ∈ I → i ≠ j → i ∩ j = (∅ : V) := by
    intro i hi j hj hij
    by_contra hne
    obtain ⟨x, hx⟩ : ∃ x : V, x ∈ i ∩ j := by
      by_contra hno
      exact hne (mem_ext (fun x ↦ ⟨fun hxi ↦ absurd ⟨x, hxi⟩ hno,
        fun hxe ↦ absurd hxe not_mem_empty⟩))
    exact hanti.2 i hi j hj hij
      ((levy_cone_compatible_iff ha (hDCa i (hID i hi)) (hDCa j (hID j hj))).mpr ⟨x, hx⟩)
  -- the join is `a`
  have hjoin : regularJoin (levyCollapse κ) (levyOrder κ) (range A) = a := by
    rw [hArange]
    apply SetTheory.subset_antisymm (regularJoin_subset hP hIa hareg)
    intro p hpa
    have hpP : p ∈ levyCollapse κ := hareg.1 p hpa
    refine (mem_regularJoin_iff _ _ _ _).mpr ⟨hpP, fun q hq hqp ↦ ?_⟩
    have hqa : q ∈ a := hareg.2.1 p hpa q hq hqp
    obtain ⟨b, hb, hcompat⟩ := hmax _ (hDmem q hq hqa)
    obtain ⟨x, hx⟩ :=
      (levy_cone_compatible_iff ha (hDCa b (hID b hb))
        (hDCa _ (hDmem q hq hqa))).mp hcompat
    obtain ⟨hxb, hxc⟩ := mem_inter_iff.mp hx
    have hxP : x ∈ levyCollapse κ :=
      ((mem_booleanConditions_iff _ _ b).mp (hIB b hb)).1.1 x hxb
    obtain ⟨s, hs, hsx⟩ := exists_forcingCone_below hxc hxP (hP.2.1 x hxP)
    obtain ⟨hsP, hsq⟩ := (mem_forcingCone_iff _ _ _ _).mp hs
    refine ⟨s, ⟨b, hb, ?_⟩, hsq⟩
    exact ((mem_booleanConditions_iff _ _ b).mp (hIB b hb)).1.2.1 x hxb s hsP hsx
  -- the index set has size at most `κ`
  have hIcard : I ≤# κ := by
    refine CardLE.trans ?_ (levyCollapse_cardLE_self hAC hU hc hω hκ)
    refine cardLE_of_separating_relation (wellOrderable_of_internalChoice hAC (levyCollapse κ))
      (fun b p ↦ b = coneRegular (levyCollapse κ) (levyOrder κ) p) (by definability) ?_ ?_
    · intro i hi
      obtain ⟨p, hp, hip⟩ := hIcone i hi
      exact ⟨p, hp, hip⟩
    · intro x _ z _ y _ hx hz
      exact hx.trans hz.symm
  -- choose the isomorphisms
  have hne : ∀ i ∈ I, IsNonempty (levyConeIsoSet κ i) := by
    intro i hi
    obtain ⟨p, hp, hip⟩ := hIcone i hi
    obtain ⟨G, hG⟩ := levy_forcingCone_coneRegular_isomorphic hp
    rw [← hip] at hG
    exact ⟨G, (mem_levyConeIsoSet_iff κ i G).mpr
      ⟨mem_power_iff.mpr (subset_prod_of_mem_function hG.1), hG⟩⟩
  obtain ⟨F, hFfun, hFdom, hFval⟩ :=
    choice_for_definable_family hAC I (levyConeIsoSet κ) (levyConeIsoSet_definable κ) hne
  refine ⟨I, A, F, hIcard, hInonempty, hAfun, hAdom, ?_, ?_, ?_, hjoin, hFfun, hFdom, ?_⟩
  · intro i hi
    rw [hAval i hi]
    exact hIB i hi
  · intro i hi
    rw [hAval i hi]
    exact hIa i hi
  · intro i hi j hj hij
    rw [hAval i hi, hAval j hj]
    exact hdisj i hi j hj hij
  · intro i hi
    rw [hAval i hi]
    exact ((mem_levyConeIsoSet_iff κ i (F ‘ i)).mp (hFval i hi)).2

end Partition

/-! ### The top splits into `lam` cones -/

section TopPartition

variable {κ lam : V} [IsOrdinal κ]

/-- The one point condition sending the coordinate `⟨∅, lam⟩ₖ` to `β`. -/
noncomputable def levyTopPiece (lam β : V) : V := ({⟨⟨(∅ : V), lam⟩ₖ, β⟩ₖ} : V)

theorem levyTopPiece_mem (hlam : lam ∈ κ) {β : V} (hβ : β ∈ lam) :
    levyTopPiece lam β ∈ levyCollapse κ := by
  have hβκ : β ∈ κ := IsOrdinal.toIsTransitive.transitive lam hlam β hβ
  have hzD : (⟨(∅ : V), lam⟩ₖ : V) ∈ (ω : V) ×ˢ κ := kpair_mem_iff.mpr ⟨empty_mem_ω, hlam⟩
  have hfresh : (⟨(∅ : V), lam⟩ₖ : V) ∉ domain (∅ : V) := by
    intro h
    obtain ⟨y, hy⟩ := mem_domain_iff.mp h
    exact not_mem_empty hy
  have hins := finitePartialFunction_insert
    (empty_mem_finitePartialFunctions ((ω : V) ×ˢ κ) κ) hzD hβκ hfresh
  rw [SetTheory.insert_empty_eq] at hins
  unfold levyTopPiece
  refine (mem_levyCollapse_iff κ _).mpr ⟨hins, fun n α β' h ↦ ?_⟩
  rw [mem_singleton_iff] at h
  obtain ⟨h1, h2⟩ := kpair_inj h
  obtain ⟨-, h3⟩ := kpair_inj h1
  rw [h2, h3]
  exact hβ

theorem levyTopPiece_incompatible (hlam : lam ∈ κ) {β γ : V} (hβ : β ∈ lam) (hγ : γ ∈ lam)
    (hne : β ≠ γ) :
    ¬ForcingCompatible (levyCollapse κ) (levyOrder κ) (levyTopPiece lam β)
      (levyTopPiece lam γ) := by
  intro hcompat
  have h := (levyCollapse_compatible_iff (levyTopPiece_mem hlam hβ)
    (levyTopPiece_mem hlam hγ)).mp hcompat
  exact hne (h (⟨(∅ : V), lam⟩ₖ) β γ (by unfold levyTopPiece; rw [mem_singleton_iff])
    (by unfold levyTopPiece; rw [mem_singleton_iff]))

/-- Every condition of the collapse has an extension lying in the cone of one of the pieces. -/
theorem levyTopPiece_predense (hlam : lam ∈ κ) (hω : (ω : V) ⊆ lam) {q : V}
    (hq : q ∈ levyCollapse κ) :
    ∃ β, β ∈ lam ∧ ∃ r, r ∈ levyCollapse κ ∧ ⟨r, levyTopPiece lam β⟩ₖ ∈ levyOrder κ ∧
      ⟨r, q⟩ₖ ∈ levyOrder κ := by
  classical
  have hqf : IsFunction q :=
    ((mem_finitePartialFunctions _ _ q).mp (levyCollapse_finitePartialFunction hq)).2.1
  by_cases hz : (⟨(∅ : V), lam⟩ₖ : V) ∈ domain q
  · set γ := q ‘ (⟨(∅ : V), lam⟩ₖ : V) with hγdef
    have hmem : (⟨(⟨(∅ : V), lam⟩ₖ : V), γ⟩ₖ : V) ∈ q := kpair_value_mem hz
    have hγ : γ ∈ lam := levyCollapse_value hq hmem
    refine ⟨γ, hγ, q, hq, ?_, (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hq, hq, subset_refl _⟩⟩
    refine (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hq, levyTopPiece_mem hlam hγ, ?_⟩
    unfold levyTopPiece
    exact singleton_subset_iff_mem.mpr hmem
  · have hβ : (∅ : V) ∈ lam := hω _ empty_mem_ω
    have hzD : (⟨(∅ : V), lam⟩ₖ : V) ∈ (ω : V) ×ˢ κ := kpair_mem_iff.mpr ⟨empty_mem_ω, hlam⟩
    have hβκ : (∅ : V) ∈ κ := IsOrdinal.toIsTransitive.transitive lam hlam _ hβ
    have hins := finitePartialFunction_insert (levyCollapse_finitePartialFunction hq)
      hzD hβκ hz
    have hr : insert (⟨(⟨(∅ : V), lam⟩ₖ : V), (∅ : V)⟩ₖ : V) q ∈ levyCollapse κ := by
      refine (mem_levyCollapse_iff κ _).mpr ⟨hins, fun n α β' h ↦ ?_⟩
      rcases mem_insert.mp h with h | h
      · obtain ⟨h1, h2⟩ := kpair_inj h
        obtain ⟨-, h3⟩ := kpair_inj h1
        rw [h2, h3]
        exact hβ
      · exact levyCollapse_value hq h
    refine ⟨(∅ : V), hβ, _, hr, ?_, ?_⟩
    · refine (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hr, levyTopPiece_mem hlam hβ, ?_⟩
      unfold levyTopPiece
      exact singleton_subset_iff_mem.mpr (mem_insert.mpr (Or.inl rfl))
    · exact (pair_mem_reverseInclusionOrder _ _ _).mpr
        ⟨hr, hq, fun z hz' ↦ mem_insert.mpr (Or.inr hz')⟩

/-- For an infinite `lam ∈ κ` the whole collapse, the top of the Boolean completion, is the join
of `lam` pairwise disjoint regular cones of conditions. -/
theorem levy_exists_top_conePartition (hlam : lam ∈ κ) (hω : (ω : V) ⊆ lam) :
    ∃ A, IsFunction A ∧ domain A = lam ∧
      (∀ i, i ∈ lam → A ‘ i ∈ booleanConditions (levyCollapse κ) (levyOrder κ)) ∧
      (∀ i, i ∈ lam → ∀ j, j ∈ lam → i ≠ j → (A ‘ i) ∩ (A ‘ j) = (∅ : V)) ∧
      regularJoin (levyCollapse κ) (levyOrder κ) (range A) = levyCollapse κ ∧
      (∀ i, i ∈ lam → ∃ p, p ∈ levyCollapse κ ∧
        A ‘ i = coneRegular (levyCollapse κ) (levyOrder κ) p) := by
  have hP := (levyCollapse_poset κ).1
  set G : V → V := fun β ↦ coneRegular (levyCollapse κ) (levyOrder κ) (levyTopPiece lam β)
    with hGdef
  have hGdefinable : ℒₛₑₜ-function₁[V] G := by
    unfold G levyTopPiece
    definability
  set A := definableGraph lam G hGdefinable with hAdef
  have hAval : ∀ i, i ∈ lam → A ‘ i = G i := fun i hi ↦ value_definableGraph lam G hGdefinable hi
  refine ⟨A, definableGraph_isFunction _ _ _, domain_definableGraph _ _ _, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hAval i hi]
    exact coneRegular_mem_booleanConditions hP (levyTopPiece_mem hlam hi)
  · intro i hi j hj hij
    rw [hAval i hi, hAval j hj]
    exact coneRegular_inter_eq_empty hP (levyTopPiece_incompatible hlam hi hj hij)
  · refine regularJoin_eq_self_of_predense (fun q hq ↦ ?_)
    obtain ⟨β, hβ, r, hr, hrβ, hrq⟩ := levyTopPiece_predense hlam hω hq
    refine ⟨G β, ?_, r, ?_, hrq⟩
    · rw [hAdef, range_definableGraph]
      exact (repl_spec hGdefinable).mpr ⟨β, hβ, rfl⟩
    · exact forcingCone_subset_coneRegular hP (levyTopPiece_mem hlam hβ) r
        ((mem_forcingCone_iff _ _ _ _).mpr ⟨hr, hrβ⟩)
  · intro i hi
    exact ⟨levyTopPiece lam i, levyTopPiece_mem hlam hi, hAval i hi⟩

end TopPartition

end ZFVP
