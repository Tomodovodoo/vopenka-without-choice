import ZFVP.SetTheory.LevyCollapseUpper
import ZFVP.ModelTheory.QuotientEquivalence

/-! The product lemma for the Levy collapse: the upper part `G ∩ Coll(ω,[β,κ))` of the generic is
generic over `V[G_β]` for the upper collapse, and `V[G] ≃ V[G_β][G ∩ Coll(ω,[β,κ))]` over the
ground model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The upper part of the generic. -/
def levyUpperGeneric (κ β : V) (G : Set V) : Set V := {p | p ∈ G ∧ p ∈ levyCollapseAbove κ β}

theorem levyCut_definable_one (β : V) : ℒₛₑₜ-function₁[V] (levyCut β) := by
  unfold levyCut
  definability

theorem levyUpper_definable_one (β : V) : ℒₛₑₜ-function₁[V] (levyUpper β) := by
  unfold levyUpper
  have := levyCut_definable_one β
  definability

/-- The lower-part map as a set function on the collapse. -/
noncomputable def levyCutFunction (κ β : V) : V :=
  definableGraph (levyCollapse κ) (levyCut β) (levyCut_definable_one β)

/-- The upper-part map as a set function on the collapse. -/
noncomputable def levyUpperFunction (κ β : V) : V :=
  definableGraph (levyCollapse κ) (levyUpper β) (levyUpper_definable_one β)

theorem levyCutFunction_value {κ β p : V} (hp : p ∈ levyCollapse κ) :
    (levyCutFunction κ β) ‘ p = levyCut β p := value_definableGraph _ _ _ hp

theorem levyUpperFunction_value {κ β p : V} (hp : p ∈ levyCollapse κ) :
    (levyUpperFunction κ β) ‘ p = levyUpper β p := value_definableGraph _ _ _ hp

instance levyCutFunction_isFunction (κ β : V) : IsFunction (levyCutFunction κ β) :=
  IsFunction.of_mem (definableGraph_mem_function _ _ _)

instance levyUpperFunction_isFunction (κ β : V) : IsFunction (levyUpperFunction κ β) :=
  IsFunction.of_mem (definableGraph_mem_function _ _ _)

theorem levyCutFunction_domain (κ β : V) : domain (levyCutFunction κ β) = levyCollapse κ :=
  domain_eq_of_mem_function (definableGraph_mem_function _ _ _)

theorem levyUpperFunction_domain (κ β : V) : domain (levyUpperFunction κ β) = levyCollapse κ :=
  domain_eq_of_mem_function (definableGraph_mem_function _ _ _)

section

variable {κ : V} (β : V) [IsOrdinal β] (hβ : β ⊆ κ) {G : Set V}
  (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

/-- The upper collapse inside `V[G_β]`. -/
noncomputable def levyProductConditions : (levySubContext β hβ hG).Model :=
  (levySubContext β hβ hG).check (levyCollapseAbove κ β)

/-- The order of the upper collapse inside `V[G_β]`. -/
noncomputable def levyProductOrder : (levySubContext β hβ hG).Model :=
  restrictedOrder ((levySubContext β hβ hG).check (levyOrder κ)) (levyProductConditions β hβ hG)

/-- The upper generic inside `V[G_β]`. -/
def levyProductGeneric : Set (levySubContext β hβ hG).Model :=
  {x | ∃ p ∈ levyUpperGeneric κ β G, x = (levySubContext β hβ hG).check p}

theorem levyProductConditions_subset :
    levyProductConditions β hβ hG ⊆ (levySubContext β hβ hG).check (levyCollapse κ) :=
  ((levySubContext β hβ hG).checkEmbedding.subset_iff _ _).mpr (levyCollapseAbove_subset κ β)

theorem check_mem_levyProductConditions_iff (p : V) :
    (levySubContext β hβ hG).check p ∈ levyProductConditions β hβ hG ↔ p ∈ levyCollapseAbove κ β :=
  (levySubContext β hβ hG).check_mem_iff p _

theorem check_kpair_mem_levyProductOrder_iff (p q : V) :
    ⟨(levySubContext β hβ hG).check p, (levySubContext β hβ hG).check q⟩ₖ ∈ levyProductOrder β hβ hG ↔
      ⟨p, q⟩ₖ ∈ levyOrder κ ∧ p ∈ levyCollapseAbove κ β ∧ q ∈ levyCollapseAbove κ β := by
  unfold levyProductOrder
  rw [kpair_mem_restrictedOrder_iff, ← (levySubContext β hβ hG).check_kpair,
    (levySubContext β hβ hG).check_mem_iff, check_mem_levyProductConditions_iff,
    check_mem_levyProductConditions_iff]

theorem check_mem_levyProductGeneric_iff (p : V) :
    (levySubContext β hβ hG).check p ∈ levyProductGeneric β hβ hG ↔ p ∈ levyUpperGeneric κ β G := by
  constructor
  · rintro ⟨q, hq, he⟩
    rw [(levySubContext β hβ hG).check_eq_iff] at he
    rw [he]
    exact hq
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem levyProductOrder_preorder :
    IsForcingPreorder (levyProductConditions β hβ hG) (levyProductOrder β hβ hG) :=
  restrictedOrder_preorder
    ((levySubContext β hβ hG).checkEmbedding.map_forcingPreorder (levyCollapse_poset κ).1)
    (levyProductConditions_subset β hβ hG)

theorem levyProductTop : IsForcingTop (levyProductConditions β hβ hG) (levyProductOrder β hβ hG)
    ((levySubContext β hβ hG).check ∅) := by
  refine ⟨(check_mem_levyProductConditions_iff β hβ hG ∅).mpr (empty_mem_levyCollapseAbove κ β),
    fun x hx ↦ ?_⟩
  obtain ⟨p, hp, rfl⟩ := ((levySubContext β hβ hG).mem_check_iff _ _).mp hx
  exact (check_kpair_mem_levyProductOrder_iff β hβ hG p ∅).mpr
    ⟨(pair_mem_reverseInclusionOrder _ _ _).mpr ⟨levyCollapseAbove_subset κ β p hp,
      empty_mem_levyCollapse κ, fun z hz ↦ absurd hz not_mem_empty⟩, hp, empty_mem_levyCollapseAbove κ β⟩

theorem levyProductGeneric_filter : IsExternalForcingFilter (levyProductConditions β hβ hG)
    (levyProductOrder β hβ hG) (levyProductGeneric β hβ hG) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x ⟨p, hp, rfl⟩
    exact (check_mem_levyProductConditions_iff β hβ hG p).mpr hp.2
  · obtain ⟨p, hp⟩ := hG.1.2.1
    have h0 : (∅ : V) ∈ G := hG.1.2.2.1 p hp ∅ (empty_mem_levyCollapse κ)
      ((pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hG.1.1 p hp, empty_mem_levyCollapse κ,
        fun z hz ↦ absurd hz not_mem_empty⟩)
    exact ⟨_, ∅, ⟨h0, empty_mem_levyCollapseAbove κ β⟩, rfl⟩
  · rintro x ⟨p, hp, rfl⟩ y hy hxy
    obtain ⟨q, hq, rfl⟩ := ((levySubContext β hβ hG).mem_check_iff _ _).mp hy
    obtain ⟨hpq, _, hqA⟩ := (check_kpair_mem_levyProductOrder_iff β hβ hG p q).mp hxy
    exact ⟨q, ⟨hG.1.2.2.1 p hp.1 q (levyCollapseAbove_subset κ β q hqA) hpq, hqA⟩, rfl⟩
  · rintro x ⟨p, hp, rfl⟩ y ⟨q, hq, rfl⟩
    obtain ⟨r, hr, hrp, hrq⟩ := hG.1.2.2.2 p hp.1 q hq.1
    have hrA := levyUpper_mem_above (β := β) (hG.1.1 r hr)
    have hrG := levyUpper_mem_of_mem (β := β) hG hr
    have hpr : p ⊆ r := ((pair_mem_reverseInclusionOrder _ _ _).mp hrp).2.2
    have hqr : q ⊆ r := ((pair_mem_reverseInclusionOrder _ _ _).mp hrq).2.2
    refine ⟨_, ⟨levyUpper β r, ⟨hrG, hrA⟩, rfl⟩, ?_, ?_⟩
    · exact (check_kpair_mem_levyProductOrder_iff β hβ hG _ _).mpr
        ⟨(pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hG.1.1 _ hrG, hG.1.1 p hp.1,
          above_subset_levyUpper hp.2 hpr⟩, hrA, hp.2⟩
    · exact (check_kpair_mem_levyProductOrder_iff β hβ hG _ _).mpr
        ⟨(pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hG.1.1 _ hrG, hG.1.1 q hq.1,
          above_subset_levyUpper hq.2 hqr⟩, hrA, hq.2⟩

/-- Conditions whose lower part forces their upper part into a given name. -/
noncomputable def levyProductWitnessSet (κ β Dn : V) : V :=
  sep (levyCollapse κ) (fun p ↦ levyCut β p ∈ atomicMembership (levyCollapse β) (levyOrder β)
    (checkName ∅ (levyUpper β p)) Dn)
    (by
      have := atomicMembership_definable (levyCollapse β) (levyOrder β)
      have := levyCut_definable_one β
      have := levyUpper_definable_one β
      definability)

theorem mem_levyProductWitnessSet_iff (κ β Dn p : V) :
    p ∈ levyProductWitnessSet κ β Dn ↔ p ∈ levyCollapse κ ∧ levyCut β p ∈
      atomicMembership (levyCollapse β) (levyOrder β) (checkName ∅ (levyUpper β p)) Dn :=
  mem_sep_iff

noncomputable def levyProductDenseSet (κ β Dn : V) : V :=
  levyProductWitnessSet κ β Dn ∪
    sep (levyCollapse κ) (fun p ↦ ∀ p' ∈ levyProductWitnessSet κ β Dn, ¬ (p ⊆ p')) (by definability)

theorem mem_levyProductDenseSet_iff (κ β Dn p : V) :
    p ∈ levyProductDenseSet κ β Dn ↔ p ∈ levyProductWitnessSet κ β Dn ∨
      (p ∈ levyCollapse κ ∧ ∀ p' ∈ levyProductWitnessSet κ β Dn, ¬ (p ⊆ p')) := by
  unfold levyProductDenseSet
  rw [mem_union_iff, mem_sep_iff]

/-- The product lemma: the upper generic meets every dense subset of the upper collapse lying
in `V[G_β]`. -/
theorem levyProductGeneric_meets (D' : (levySubContext β hβ hG).Model)
    (hD' : ForcingDense (levyProductConditions β hβ hG) (levyProductOrder β hβ hG) D') :
    ∃ x ∈ levyProductGeneric β hβ hG, x ∈ D' := by
  let C := levySubContext β hβ hG
  have hgen : IsExternalForcingGeneric (levyCollapse β) (levyOrder β) (levySubGeneric β G) :=
    levySubGeneric_generic hβ hG
  obtain ⟨Dn, rfl⟩ := C.ofName_surjective D'
  have hmem_of_forced : ∀ u ∈ levyCollapseAbove κ β, ∀ q ∈ levySubGeneric β G,
      q ∈ atomicMembership (levyCollapse β) (levyOrder β) (checkName ∅ u) Dn.val →
      C.check u ∈ C.ofName Dn := by
    intro u _ q hq hqM
    exact (forcingQuotientMk_mem_iff C.P C.R C.G C.order C.generic.1
      ⟨checkName C.one u, checkName_isName C.top.1 u⟩ Dn).mpr ⟨q, hq, hqM⟩
  have hW : levyProductWitnessSet κ β Dn.val ⊆ levyCollapse κ :=
    fun p hp ↦ ((mem_levyProductWitnessSet_iff _ _ _ _).mp hp).1
  have hF : ForcingDense (levyCollapse κ) (levyOrder κ) (levyProductDenseSet κ β Dn.val) := by
    refine ⟨fun p hp ↦ ((mem_levyProductDenseSet_iff _ _ _ _).mp hp).elim (hW p) (fun h ↦ h.1),
      fun p hp ↦ ?_⟩
    by_cases hex : ∃ p' ∈ levyProductWitnessSet κ β Dn.val, p ⊆ p'
    · obtain ⟨p', hp', hpp'⟩ := hex
      exact ⟨p', (mem_levyProductDenseSet_iff _ _ _ _).mpr (Or.inl hp'),
        (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hW p' hp', hp, hpp'⟩⟩
    · push Not at hex
      exact ⟨p, (mem_levyProductDenseSet_iff _ _ _ _).mpr (Or.inr ⟨hp, hex⟩),
        (levyCollapse_poset κ).1.2.1 p hp⟩
  obtain ⟨p₀, hp₀G, hp₀F⟩ := hG.2 _ hF
  have hp₀ := hG.1.1 p₀ hp₀G
  have hcutG : levyCut β p₀ ∈ levySubGeneric β G := ⟨levyCut_mem_of_mem hG hp₀G, levyCut_mem hp₀⟩
  have hupG : levyUpper β p₀ ∈ levyUpperGeneric κ β G :=
    ⟨levyUpper_mem_of_mem hG hp₀G, levyUpper_mem_above hp₀⟩
  rcases (mem_levyProductDenseSet_iff _ _ _ _).mp hp₀F with hE | hN
  · obtain ⟨_, hM⟩ := (mem_levyProductWitnessSet_iff _ _ _ _).mp hE
    exact ⟨C.check (levyUpper β p₀), ⟨_, hupG, rfl⟩,
      hmem_of_forced _ hupG.2 _ hcutG hM⟩
  · exfalso
    obtain ⟨_, hnone⟩ := hN
    have hq : C.check (levyUpper β p₀) ∈ levyProductConditions β hβ hG :=
      (check_mem_levyProductConditions_iff β hβ hG _).mpr hupG.2
    obtain ⟨u', hu'D, hu'q⟩ := hD'.2 _ hq
    obtain ⟨u₁, hu₁, rfl⟩ := (C.mem_check_iff (levyCollapseAbove κ β) _).mp (hD'.1 _ hu'D)
    obtain ⟨hord, _, _⟩ := (check_kpair_mem_levyProductOrder_iff β hβ hG _ _).mp hu'q
    have hsub : levyUpper β p₀ ⊆ u₁ := ((pair_mem_reverseInclusionOrder _ _ _).mp hord).2.2
    obtain ⟨q, hqG, hqM⟩ := (forcingQuotientMk_mem_iff C.P C.R C.G C.order C.generic.1
      ⟨checkName C.one u₁, checkName_isName C.top.1 u₁⟩ Dn).mp hu'D
    obtain ⟨q', hq'G, hq'q, hq'c⟩ := hgen.1.2.2.2 q hqG _ hcutG
    have hq'β : q' ∈ levyCollapse β := hgen.1.1 q' hq'G
    have hqq' : q ⊆ q' := ((pair_mem_reverseInclusionOrder _ _ _).mp hq'q).2.2
    have hcq' : levyCut β p₀ ⊆ q' := ((pair_mem_reverseInclusionOrder _ _ _).mp hq'c).2.2
    have hq'M : q' ∈ atomicMembership (levyCollapse β) (levyOrder β) (checkName ∅ u₁) Dn.val :=
      atomicMembership_mono (levyCollapse_poset β).1 hqM hq'β hq'q
    have hp'C : q' ∪ u₁ ∈ levyCollapse κ := levyCollapse_union_above hβ hq'β hu₁
    have hp'W : q' ∪ u₁ ∈ levyProductWitnessSet κ β Dn.val := by
      refine (mem_levyProductWitnessSet_iff _ _ _ _).mpr ⟨hp'C, ?_⟩
      rw [levyCut_union_above hq'β hu₁, levyUpper_union_above hq'β hu₁]
      exact hq'M
    apply hnone _ hp'W
    intro z hz
    rw [← levyCut_union_levyUpper β p₀] at hz
    rcases mem_union_iff.mp hz with h | h
    · exact mem_union_iff.mpr (Or.inl (hcq' z h))
    · exact mem_union_iff.mpr (Or.inr (hsub z h))

/-- The upper collapse over `V[G_β]` with the upper generic. -/
noncomputable def levyProductContext : ForcingContext (levySubContext β hβ hG).Model where
  P := levyProductConditions β hβ hG
  R := levyProductOrder β hβ hG
  one := (levySubContext β hβ hG).check ∅
  G := levyProductGeneric β hβ hG
  order := levyProductOrder_preorder β hβ hG
  top := levyProductTop β hβ hG
  generic := ⟨levyProductGeneric_filter β hβ hG, levyProductGeneric_meets β hβ hG⟩

end

end ZFVP
