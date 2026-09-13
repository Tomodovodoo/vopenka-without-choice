import ZFVP.ModelTheory.LevySwapComplementSupport
import ZFVP.ModelTheory.LevyGaloisStep

/-! Support clauses for the two cone isomorphisms of the Levy collapse, from determinacy
below `ξ`.

`levy_complement_cone_isomorphism_support_of_agree` in `LevySwapComplementSupport` builds both
cone isomorphisms of the value swap `levySwapAutomorphism κ r r'` together with their support
clauses, but asks that every base support value be the regular closure of a set of conditions
with domains inside `ω × ξ`. That hypothesis is stronger than needed. The proof only uses that
the swap fixes the base support values, and that follows from the localization predicate the rest
of the development works with, `IsLevyDeterminedBelow κ ξ`.

* `levyCut_levySwapCondition`: if `r` and `r'` agree at every coordinate of `ω × ξ` where both
  are defined, the swap does not change the part of a condition below `ξ`.

* `levySwap_imageAction_eq_self_of_determined`: hence the swap fixes every set of conditions
  determined below `ξ`, the same way the row permutations above `ξ` do
  (`levyPermutation_imageAction_eq_self_of_determined`).

* `levy_complement_cone_isomorphism_support_of_determined`: both isomorphisms with their support
  clauses, from the assumption that every base support value of `E` is determined below `ξ`.

* `levy_swap_complement_trace_of_determined`: the same data satisfies the two trace conditions
  in the antecedent of `ForcingContext.ComplementConeAligned`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### The swap below `ξ` -/

/-- At a coordinate of `ω × ξ` the value swap of two conditions that agree there is the
identity. Both swap clauses give the value back: they replace a value of `r` by the value of `r'`
at the same coordinate, or the other way round, and the two values are equal. -/
theorem levySwapValue_eq_self_of_agree {ξ r r' z γ : V} (hrf : IsFunction r)
    (hr'f : IsFunction r')
    (hagree : ∀ z ∈ domain r, z ∈ domain r' → z ∈ (ω : V) ×ˢ ξ → r ‘ z = r' ‘ z)
    (hz : z ∈ (ω : V) ×ˢ ξ) : levySwapValue r r' z γ = γ := by
  have := hrf
  have := hr'f
  by_cases h1 : ⟨z, γ⟩ₖ ∈ r ∧ z ∈ domain r'
  · rw [levySwapValue_left h1.1 h1.2, ← hagree z (mem_domain_of_kpair_mem h1.1) h1.2 hz]
    exact value_eq_of_kpair_mem h1.1
  · by_cases h2 : ⟨z, γ⟩ₖ ∈ r' ∧ z ∈ domain r
    · have hnp : ⟨z, γ⟩ₖ ∉ r := fun h ↦ h1 ⟨h, mem_domain_of_kpair_mem h2.1⟩
      rw [levySwapValue_right h2.1 h2.2 hnp,
        hagree z h2.2 (mem_domain_of_kpair_mem h2.1) hz]
      exact value_eq_of_kpair_mem h2.1
    · exact levySwapValue_fixed (by rintro (h | h); exacts [h1 h, h2 h])

/-- The value swap of two conditions that agree at every coordinate of `ω × ξ` where both are
defined leaves the part below `ξ` of every condition unchanged. -/
theorem levyCut_levySwapCondition {κ ξ r r' p : V} (hr : r ∈ levyCollapse κ)
    (hr' : r' ∈ levyCollapse κ)
    (hagree : ∀ z ∈ domain r, z ∈ domain r' → z ∈ (ω : V) ×ˢ ξ → r ‘ z = r' ‘ z)
    (hp : p ∈ levyCollapse κ) :
    levyCut ξ (levySwapCondition r r' p) = levyCut ξ p := by
  have hrf := levyCollapse_isFunction hr
  have hr'f := levyCollapse_isFunction hr'
  have := levyCollapse_isFunction hp
  apply mem_ext
  intro z
  simp only [levyCut, mem_restrict_iff]
  constructor
  · rintro ⟨hzs, x, hx, y, rfl⟩
    obtain ⟨hxd, hy⟩ := (kpair_mem_levySwapCondition_iff _ _ _ _ _).mp hzs
    rw [levySwapValue_eq_self_of_agree hrf hr'f hagree hx] at hy
    subst hy
    exact ⟨kpair_value_mem hxd, x, hx, p ‘ x, rfl⟩
  · rintro ⟨hzp, x, hx, y, rfl⟩
    refine ⟨(kpair_mem_levySwapCondition_iff _ _ _ _ _).mpr
      ⟨mem_domain_of_kpair_mem hzp, ?_⟩, x, hx, y, rfl⟩
    rw [levySwapValue_eq_self_of_agree hrf hr'f hagree hx]
    exact (value_eq_of_kpair_mem hzp).symm

/-- A set of conditions determined below `ξ` is fixed by the value swap of two conditions that
agree at every coordinate of `ω × ξ` where both are defined. -/
theorem levySwap_imageAction_eq_self_of_determined {κ ξ r r' d : V} (hr : r ∈ levyCollapse κ)
    (hr' : r' ∈ levyCollapse κ)
    (hagree : ∀ z ∈ domain r, z ∈ domain r' → z ∈ (ω : V) ×ˢ ξ → r ‘ z = r' ‘ z)
    (hd : d ⊆ levyCollapse κ) (hdet : IsLevyDeterminedBelow κ ξ d) :
    imageAction (levySwapAutomorphism κ r r') d = d := by
  have hπ := levySwapAutomorphism_isForcingAutomorphism hr hr'
  refine imageAction_eq_of_iff hπ hd hd (fun q hq ↦ ?_)
  have hswap : levySwapCondition r r' q ∈ levyCollapse κ := levySwapCondition_mem hr hr' hq
  rw [levySwapAutomorphism_value hq, hdet _ hswap,
    levyCut_levySwapCondition hr hr' hagree hq, ← hdet q hq]

/-! ### Both cone isomorphisms with their support clauses -/

/-- Both cone isomorphisms with their support clauses, for two conditions of equal domain that
agree at every coordinate of `ω × ξ` where both are defined, under the assumption that every base
support value of `E` is determined below `ξ`. This is the same conclusion as
`levy_complement_cone_isomorphism_support_of_agree` from a weaker hypothesis on `E`. -/
theorem levy_complement_cone_isomorphism_support_of_determined {κ ξ r r' E : V}
    (hr : r ∈ levyCollapse κ) (hr' : r' ∈ levyCollapse κ) (hdom : domain r = domain r')
    (hagree : ∀ z ∈ domain r, z ∈ domain r' → z ∈ (ω : V) ×ˢ ξ → r ‘ z = r' ‘ z)
    (hdet : ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
        ((ω : V) ×ˢ (ω : V)) E,
      IsLevyDeterminedBelow κ ξ a) :
    (∃ g, IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingNegation (levyCollapse κ) (levyOrder κ)
          (coneRegular (levyCollapse κ) (levyOrder κ) r)))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingNegation (levyCollapse κ) (levyOrder κ)
            (coneRegular (levyCollapse κ) (levyOrder κ) r))))
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingNegation (levyCollapse κ) (levyOrder κ)
          (coneRegular (levyCollapse κ) (levyOrder κ) r')))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingNegation (levyCollapse κ) (levyOrder κ)
            (coneRegular (levyCollapse κ) (levyOrder κ) r')))) g ∧
      ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
          ((ω : V) ×ˢ (ω : V)) E,
        coneImage (levyCollapse κ) (levyOrder κ)
            (forcingNegation (levyCollapse κ) (levyOrder κ)
              (coneRegular (levyCollapse κ) (levyOrder κ) r)) g
            (a ∩ forcingNegation (levyCollapse κ) (levyOrder κ)
              (coneRegular (levyCollapse κ) (levyOrder κ) r)) =
          a ∩ forcingNegation (levyCollapse κ) (levyOrder κ)
            (coneRegular (levyCollapse κ) (levyOrder κ) r')) ∧
    (∃ f, IsForcingIsomorphism
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (coneRegular (levyCollapse κ) (levyOrder κ) r))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (coneRegular (levyCollapse κ) (levyOrder κ) r)))
      (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
        (booleanOrder (levyCollapse κ) (levyOrder κ))
        (coneRegular (levyCollapse κ) (levyOrder κ) r'))
      (restrictedOrder (booleanOrder (levyCollapse κ) (levyOrder κ))
        (forcingCone (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (coneRegular (levyCollapse κ) (levyOrder κ) r'))) f ∧
      ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
          ((ω : V) ×ˢ (ω : V)) E,
        coneImage (levyCollapse κ) (levyOrder κ)
            (coneRegular (levyCollapse κ) (levyOrder κ) r) f
            (a ∩ coneRegular (levyCollapse κ) (levyOrder κ) r) =
          a ∩ coneRegular (levyCollapse κ) (levyOrder κ) r') := by
  have hfix : ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
      ((ω : V) ×ˢ (ω : V)) E, imageAction (levySwapAutomorphism κ r r') a = a := by
    intro a ha
    have hreg : IsForcingRegular (levyCollapse κ) (levyOrder κ) a :=
      (mem_regularSets_iff _ _ _).mp
        (supportValuesBase_subset_regularSets (levyCollapse_poset κ).1 _ _ _ a ha)
    exact levySwap_imageAction_eq_self_of_determined hr hr' hagree hreg.1 (hdet a ha)
  exact ⟨levy_complement_cone_isomorphism_support_of_fixed hr hr' hdom hfix,
    levy_cone_isomorphism_support_of_fixed hr hr' hdom hfix⟩

/-! ### The two trace conditions -/

/-- The image of a set of conditions under an automorphism is empty exactly when the set is. -/
theorem imageAction_eq_empty_iff (π A : V) :
    imageAction π A = (∅ : V) ↔ A = (∅ : V) := by
  rw [eq_empty_iff_not_exists_mem, eq_empty_iff_not_exists_mem]
  constructor
  · rintro h ⟨z, hz⟩
    exact h ⟨π ‘ z, (mem_imageAction_iff _ _ _).mpr ⟨z, hz, rfl⟩⟩
  · rintro h ⟨z, hz⟩
    obtain ⟨p, hp, -⟩ := (mem_imageAction_iff _ _ _).mp hz
    exact h ⟨p, hp⟩

/-- The two trace conditions in the antecedent of `ForcingContext.ComplementConeAligned` hold for
the pair of cones of `r` and `r'`: the complement of one cone is empty exactly when the other one
is, and every base support value determined below `ξ` misses one complement exactly when it
misses the other. Both come from the value swap carrying the complement of the cone of `r` to the
complement of the cone of `r'` while fixing the support values. -/
theorem levy_swap_complement_trace_of_determined {κ ξ r r' E : V} (hr : r ∈ levyCollapse κ)
    (hr' : r' ∈ levyCollapse κ) (hdom : domain r = domain r')
    (hagree : ∀ z ∈ domain r, z ∈ domain r' → z ∈ (ω : V) ×ˢ ξ → r ‘ z = r' ‘ z)
    (hdet : ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
        ((ω : V) ×ˢ (ω : V)) E,
      IsLevyDeterminedBelow κ ξ a) :
    (forcingNegation (levyCollapse κ) (levyOrder κ)
        (coneRegular (levyCollapse κ) (levyOrder κ) r) = (∅ : V) ↔
      forcingNegation (levyCollapse κ) (levyOrder κ)
        (coneRegular (levyCollapse κ) (levyOrder κ) r') = (∅ : V)) ∧
    ∀ a ∈ supportValuesBase (levyCollapse κ) (levyOrder κ) (levyCollapse κ)
        ((ω : V) ×ˢ (ω : V)) E,
      (a ∩ forcingNegation (levyCollapse κ) (levyOrder κ)
          (coneRegular (levyCollapse κ) (levyOrder κ) r) = (∅ : V) ↔
        a ∩ forcingNegation (levyCollapse κ) (levyOrder κ)
          (coneRegular (levyCollapse κ) (levyOrder κ) r') = (∅ : V)) := by
  have hπ := levySwapAutomorphism_isForcingAutomorphism hr hr'
  have hb0sub : coneRegular (levyCollapse κ) (levyOrder κ) r ⊆ levyCollapse κ :=
    fun _ hx ↦ (mem_coneRegular_iff.mp hx).1
  have hval : (levySwapAutomorphism κ r r') ‘ r = r' := by
    rw [levySwapAutomorphism_value hr]
    exact levySwapCondition_self (levyCollapse_isFunction hr) (levyCollapse_isFunction hr') hdom
  have himg : imageAction (levySwapAutomorphism κ r r')
      (forcingNegation (levyCollapse κ) (levyOrder κ)
        (coneRegular (levyCollapse κ) (levyOrder κ) r)) =
      forcingNegation (levyCollapse κ) (levyOrder κ)
        (coneRegular (levyCollapse κ) (levyOrder κ) r') := by
    rw [forcingNegation_image hπ hb0sub, imageAction_coneRegular hπ hr, hval]
  refine ⟨by rw [← himg, imageAction_eq_empty_iff], fun a ha ↦ ?_⟩
  have hreg : IsForcingRegular (levyCollapse κ) (levyOrder κ) a :=
    (mem_regularSets_iff _ _ _).mp
      (supportValuesBase_subset_regularSets (levyCollapse_poset κ).1 _ _ _ a ha)
  have hfixa : imageAction (levySwapAutomorphism κ r r') a = a :=
    levySwap_imageAction_eq_self_of_determined hr hr' hagree hreg.1 (hdet a ha)
  have hinter : imageAction (levySwapAutomorphism κ r r')
      (a ∩ forcingNegation (levyCollapse κ) (levyOrder κ)
        (coneRegular (levyCollapse κ) (levyOrder κ) r)) =
      a ∩ forcingNegation (levyCollapse κ) (levyOrder κ)
        (coneRegular (levyCollapse κ) (levyOrder κ) r') := by
    refine imageAction_eq_of_iff hπ (fun x hx ↦ hreg.1 _ (mem_inter_iff.mp hx).1)
      (fun x hx ↦ hreg.1 _ (mem_inter_iff.mp hx).1) (fun q hq ↦ ?_)
    have h1 := value_mem_imageAction_iff hπ hreg.1 hq
    rw [hfixa] at h1
    have h2 := value_mem_imageAction_iff hπ
      (forcingNegation_subset (levyCollapse κ) (levyOrder κ)
        (coneRegular (levyCollapse κ) (levyOrder κ) r)) hq
    rw [himg] at h2
    rw [mem_inter_iff, mem_inter_iff, h1, h2]
  rw [← hinter, imageAction_eq_empty_iff]

end ZFVP
