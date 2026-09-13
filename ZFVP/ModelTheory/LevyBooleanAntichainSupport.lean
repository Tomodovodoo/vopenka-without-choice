import ZFVP.ModelTheory.BooleanAntichains
import ZFVP.SetTheory.LevyCollapseAntichainSupport

/-! Antichains of the Boolean completion of the Levy collapse are localized below an ordinal
`ξ < κ`: choosing one condition in each element of the antichain gives an antichain of
conditions, whose supports are bounded below `κ` by `levyAntichain_supports_bounded`, so every
element of the Boolean antichain already meets the subcollapse `levyCollapse ξ`. This is
step (a) of the Galois argument for Karagila-Schilhan Lemma 9.3. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)

omit [IsOrdinal κ] in
/-- A selector picking one condition out of each element of a Boolean antichain has an
antichain of conditions as its range. -/
theorem levyBooleanAntichain_selector_antichain {A f : V} [IsFunction f]
    (hA : IsForcingAntichain (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) A)
    (hdom : domain f = A) (hval : ∀ a ∈ A, f ‘ a ∈ a) :
    IsForcingAntichain (levyCollapse κ) (levyOrder κ) (range f) := by
  have hmem : ∀ q ∈ range f, ∃ a ∈ A, q = f ‘ a := by
    intro q hq
    obtain ⟨x, hx⟩ := mem_range_iff.mp hq
    exact ⟨x, hdom ▸ mem_domain_of_kpair_mem hx, (value_eq_of_kpair_mem hx).symm⟩
  refine ⟨fun q hq ↦ ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := hmem q hq
    exact (booleanConditions_regular (hA.1 a ha)).1 _ (hval a ha)
  · rintro p hp q hq hpq ⟨r, hr, hrp, hrq⟩
    obtain ⟨a, ha, rfl⟩ := hmem p hp
    obtain ⟨b, hb, rfl⟩ := hmem q hq
    have hab : a ≠ b := fun h ↦ hpq (by rw [h])
    have hra : r ∈ a := (booleanConditions_regular (hA.1 a ha)).2.1 _ (hval a ha) r hr hrp
    have hrb : r ∈ b := (booleanConditions_regular (hA.1 b hb)).2.1 _ (hval b hb) r hr hrq
    exact hA.2 a ha b hb hab
      ((boolean_compatible_iff (hA.1 a ha) (hA.1 b hb)).mpr ⟨r, mem_inter_iff.mpr ⟨hra, hrb⟩⟩)

include hAC hU hc hω hκ in
/-- An antichain of the Boolean completion of the Levy collapse admits a selector of conditions
whose supports are all bounded by one ordinal below `κ`. -/
theorem levyBooleanAntichain_selector_bounded {A : V}
    (hA : IsForcingAntichain (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) A) :
    ∃ ξ ∈ κ, ∃ f, IsFunction f ∧ domain f = A ∧ (∀ a ∈ A, f ‘ a ∈ a) ∧
      ∀ a ∈ A, ordinalSupport (f ‘ a) ⊆ ξ := by
  have hne : ∀ a ∈ A, IsNonempty ((fun x : V ↦ x) a) := by
    intro a ha
    obtain ⟨p, hp⟩ := booleanConditions_nonempty (hA.1 a ha)
    exact ⟨p, hp⟩
  obtain ⟨f, hf, hdom, hval⟩ :=
    choice_for_definable_family hAC A (fun x : V ↦ x) (by definability) hne
  have := hf
  obtain ⟨ξ, hξ, hbound⟩ := levyAntichain_supports_bounded hAC hU hc hω hκ
    (levyBooleanAntichain_selector_antichain hA hdom hval)
  refine ⟨ξ, hξ, f, hf, hdom, hval, fun a ha ↦ ?_⟩
  exact hbound _ (mem_range_of_kpair_mem (kpair_value_mem (hdom ▸ ha)))

include hAC hU hc hω hκ in
/-- Every element of a Boolean antichain of the Levy collapse contains a condition of the
subcollapse below some fixed `ξ < κ`. -/
theorem levyBooleanAntichain_meets_subcollapse {A : V}
    (hA : IsForcingAntichain (booleanConditions (levyCollapse κ) (levyOrder κ))
      (booleanOrder (levyCollapse κ) (levyOrder κ)) A) :
    ∃ ξ ∈ κ, ∀ a ∈ A, ∃ p ∈ a, p ∈ levyCollapse ξ := by
  obtain ⟨ξ, hξ, f, hf, hdom, hval, hsupp⟩ :=
    levyBooleanAntichain_selector_bounded hAC hU hc hω hκ hA
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  refine ⟨ξ, hξ, fun a ha ↦ ⟨f ‘ a, hval a ha, ?_⟩⟩
  have hpP : f ‘ a ∈ levyCollapse κ := (booleanConditions_regular (hA.1 a ha)).1 _ (hval a ha)
  rw [← levyCut_eq_of_support hpP (hsupp a ha)]
  exact levyCut_mem hpP

include hAC hU hc hω hκ in
/-- A regular set of the Levy collapse is decided by a maximal antichain of the completion all
of whose elements meet one subcollapse `levyCollapse ξ` with `ξ < κ`. -/
theorem levy_regular_localized {d : V} (hd : IsForcingRegular (levyCollapse κ) (levyOrder κ) d) :
    ∃ ξ ∈ κ, ∃ A ∈ boolMaximalAntichains (levyCollapse κ) (levyOrder κ),
      (∀ a ∈ A, a ⊆ d ∨ a ⊆ forcingNegation (levyCollapse κ) (levyOrder κ) d) ∧
        ∀ a ∈ A, ∃ p ∈ a, p ∈ levyCollapse ξ := by
  obtain ⟨A, hAmem, hdec⟩ := exists_deciding_antichain hAC (levyCollapse_poset κ).1 hd
  obtain ⟨-, hanti, -⟩ := (mem_boolMaximalAntichains_iff _ _ _).mp hAmem
  obtain ⟨ξ, hξ, hmeet⟩ := levyBooleanAntichain_meets_subcollapse hAC hU hc hω hκ hanti
  exact ⟨ξ, hξ, A, hAmem, hdec, hmeet⟩

include hAC hU hc hω hκ in
/-- A family of regular sets of the Levy collapse is refined, together with the complement of
its join, by a maximal antichain of the completion all of whose elements meet one subcollapse
`levyCollapse ξ` with `ξ < κ`. -/
theorem levy_regularFamily_localized {Y : V}
    (hY : ∀ y ∈ Y, IsForcingRegular (levyCollapse κ) (levyOrder κ) y) :
    ∃ ξ ∈ κ, ∃ A ∈ boolMaximalAntichains (levyCollapse κ) (levyOrder κ),
      (∀ a ∈ A, (∃ y ∈ Y, a ⊆ y) ∨
          a ⊆ forcingNegation (levyCollapse κ) (levyOrder κ)
            (regularJoin (levyCollapse κ) (levyOrder κ) Y)) ∧
        ∀ a ∈ A, ∃ p ∈ a, p ∈ levyCollapse ξ := by
  obtain ⟨A, hAmem, hdec⟩ := exists_refining_antichain hAC (levyCollapse_poset κ).1 hY
  obtain ⟨-, hanti, -⟩ := (mem_boolMaximalAntichains_iff _ _ _).mp hAmem
  obtain ⟨ξ, hξ, hmeet⟩ := levyBooleanAntichain_meets_subcollapse hAC hU hc hω hκ hanti
  exact ⟨ξ, hξ, A, hAmem, hdec, hmeet⟩

end

end ZFVP
