import ZFVP.ModelTheory.LevyOrdinalLocalization
import ZFVP.ModelTheory.LebesgueGroundChange
import ZFVP.ModelTheory.PerfectSetGroundChange
import ZFVP.ModelTheory.LevyRealsInjection

/-! The Levy-collapse regularity results stated for the weaker hypothesis "definable from
parameters that are already localized", instead of "definable from ground sets, reals and
ordinals". Every parameter of the latter kind is localized, so the new statements cover the old
ones; the proofs are the old ones with the localization step of the parameters dropped. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

/-- `x` is definable in `V[G]` from parameters each of which lies in a bounded stage
`V[G_ξ]`, `ξ < κ`. -/
def IsLocallyDefinable (x : (levyContext κ hG).Model) : Prop :=
  ∃ (n : ℕ) (φ : SetTheorySemisentence (n + 1)) (v : Fin n → (levyContext κ hG).Model),
    (∀ i, IsLocalized hG (v i)) ∧ ∀ b, b ∈ x ↔ φ.Evalb (b :> v)

include hAC hU hc hω hκ in
/-- Definability from ground sets, reals and ordinals implies definability from localized
parameters. -/
theorem locallyDefinable_of_groundRealDefinable {x : (levyContext κ hG).Model}
    (hx : (levyContext κ hG).IsGroundRealDefinable x) : IsLocallyDefinable hG x := by
  obtain ⟨n, φ, v, hv, hmem⟩ := hx
  exact ⟨n, φ, v, fun i ↦ isLocalized_parameter hAC hU hc hω hκ hG (hv i), hmem⟩

include hAC hU hc hω in
/-- A subset of a checked set definable from localized parameters lies in a bounded stage. -/
theorem locallyDefinable_localized {x : (levyContext κ hG).Model} {θ : V}
    (hx : x ⊆ (levyContext κ hG).check θ) (hdef : IsLocallyDefinable hG x) :
    IsLocalized hG x := by
  obtain ⟨n, φ, v, hv, hmem⟩ := hdef
  exact localized_subset_check_of_definable hAC hU hc hω hG hx φ v hv hmem

include hAC hU hc hω in
/-- Every set of reals of `V[G]` definable from localized parameters is Lebesgue measurable. -/
theorem lebesgueMeasurable_of_locallyDefinable {X : (levyContext κ hG).Model}
    (hXc : X ⊆ cantorSpace (levyContext κ hG).Model)
    (hX : IsLocallyDefinable hG X) : IsLebesgueMeasurable X := by
  obtain ⟨n, φ, v, hv, hdef⟩ := hX
  obtain ⟨ξ, hξ, hall⟩ := isLocalized_tuple hG hω v hv
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  choose y hy using hall
  refine lebesgueMeasurable_of_stage_definable hAC hU hc hω hG ξ hξ φ y ?_
  intro x
  have hvy : (fun i ↦ (levySubRealization ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).value (y i)) = v :=
    funext hy
  rw [hvy]
  constructor
  · intro hx
    exact ⟨hXc x hx, (hdef x).mp hx⟩
  · rintro ⟨_, h⟩
    exact (hdef x).mpr h

include hAC hU hc hω in
/-- Every set of reals of `V[G]` definable from localized parameters has the Baire property. -/
theorem baireProperty_of_locallyDefinable {X : (levyContext κ hG).Model}
    (hXc : X ⊆ cantorSpace (levyContext κ hG).Model)
    (hX : IsLocallyDefinable hG X) : BaireProperty X := by
  obtain ⟨n, φ, v, hv, hdef⟩ := hX
  obtain ⟨ξ, hξ, hall⟩ := isLocalized_tuple hG hω v hv
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  choose y hy using hall
  refine baireProperty_of_stage_definable hAC hU hc hω hG ξ hξ φ y ?_
  intro x
  have hvy : (fun i ↦ (levySubRealization ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).value (y i)) = v :=
    funext hy
  rw [hvy]
  constructor
  · intro hx
    exact ⟨hXc x hx, (hdef x).mp hx⟩
  · rintro ⟨_, h⟩
    exact (hdef x).mpr h

include hAC hU hc hω in
/-- Over an arbitrary ground, every set of reals of `V[G]` definable from localized parameters has
the perfect set property. -/
theorem perfectSetProperty_of_locallyDefinable {X : (levyContext κ hG).Model}
    (hXc : X ⊆ cantorSpace (levyContext κ hG).Model)
    (hX : IsLocallyDefinable hG X) : PerfectSetProperty X := by
  obtain ⟨n, φ, v, hv, hdef⟩ := hX
  obtain ⟨ξ, hξ, hall⟩ := isLocalized_tuple hG hω v hv
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  choose y hy using hall
  refine perfectSetProperty_of_stage_definable hAC hU hc hω hG ξ hξ φ y ?_
  intro x
  have hvy : (fun i ↦ (levySubRealization ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).value (y i)) = v :=
    funext hy
  rw [hvy]
  constructor
  · intro hx
    exact ⟨hXc x hx, (hdef x).mp hx⟩
  · rintro ⟨_, h⟩
    exact (hdef x).mpr h

include hAC hU hc hω hκ in
/-- No injection of `κ̌` into the reals has a code definable from localized parameters. -/
theorem no_locallyDefinable_injection {f : (levyContext κ hG).Model}
    (hf : f ∈ (cantorSpace (levyContext κ hG).Model) ^ (levyContext κ hG).check κ) (hinj : Injective f)
    (hdef : IsLocallyDefinable hG
      (realsCode ((levyContext κ hG).check (κ ×ˢ ((ω : V) ×ˢ ((2 : ℕ) : V)))) f)) : False :=
  no_injection_of_localized_code hAC hU hc hω hκ hG hf hinj
    (locallyDefinable_localized hAC hU hc hω hG (realsCode_subset hG f) hdef)

end

end ZFVP
