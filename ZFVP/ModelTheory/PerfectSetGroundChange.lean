import ZFVP.ModelTheory.PerfectSetDecision
import ZFVP.ModelTheory.LevyGroundChange

/-! The perfect set property for all sets of reals of the Levy extension definable from ground
sets, reals and ordinals, over an arbitrary ground model: change the ground to a bounded stage,
which is again a model with `κ` measurable, and apply the ground-definable case. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Forcing extensions of countable models are countable. -/
instance ForcingContext.countable_model [Countable V] (S : ForcingContext V) : Countable S.Model :=
  inferInstanceAs (Countable (Quotient (forcingNameSetoid S.P S.R S.G S.order S.generic.1)))

section

variable {M M' : Type*} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  [SetStructure M'] [Nonempty M'] [M'↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (e : M ≃ M') (he : ∀ x y, e x ∈ e y ↔ x ∈ y)

include he in
theorem perfectSetProperty_memEquiv (X : M) : PerfectSetProperty (e X) ↔ PerfectSetProperty X := by
  have h1 : perfectSetPropertyFormula.Evalb ![X] ↔ PerfectSetProperty X :=
    (perfectSetPropertyFormula_defined (V := M)).iff ![X]
  have h2 : perfectSetPropertyFormula.Evalb ![e X] ↔ PerfectSetProperty (e X) :=
    (perfectSetPropertyFormula_defined (V := M')).iff ![e X]
  have h3 : (fun i ↦ e (![X] i)) = ![e X] := by
    funext i
    exact Fin.cases rfl (fun j ↦ j.elim0) i
  rw [← h1, ← h2, evalb_of_memEquiv e he, h3]

end

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω in
/-- Sets of reals definable from parameters of a bounded stage have the perfect set property. -/
theorem perfectSetProperty_of_stage_definable (ξ : V) [IsOrdinal ξ] (hξ : ξ ∈ κ)
    {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (y : Fin n → (levySubContext ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).Model)
    {X : (levyContext κ hG).Model}
    (hX : ∀ x, x ∈ X ↔ x ∈ cantorSpace (levyContext κ hG).Model ∧
      φ.Evalb (x :> fun i ↦ (levySubRealization ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).value (y i))) :
    PerfectSetProperty X := by
  have hξ' : ξ ⊆ κ := IsOrdinal.toIsTransitive.transitive ξ hξ
  obtain ⟨G', hG', g, hgmem, hgval⟩ := exists_ground_change hAC hU hc hω hG ξ hξ
  let N := levySubContext ξ hξ' hG
  have hACN : InternalChoice N.Model := N.internalChoice_of_ground hAC
  obtain ⟨ν, hν, hsmall⟩ := levyCollapse_cardLE_small hAC hU hc hω hξ
  have hNP : N.P ≤# ν := hsmall
  obtain ⟨hU', hc'⟩ := N.derivedFilter_ultrafilter hAC hU hc hν hNP
  have : IsOrdinal (N.check κ) := (N.check_ordinal_iff κ).mpr inferInstance
  have hωN : (ω : N.Model) ∈ N.check κ := by
    rw [← N.check_omega_eq]
    exact (N.check_mem_iff _ _).mpr hω
  have hκN : IsInitialOrdinal (N.check κ) := initial_of_measurable hU' hc'
  rw [← perfectSetProperty_memEquiv g hgmem X]
  apply perfectSetProperty_of_ground_definable hACN hU' hc' hωN hκN hG' φ y
  intro x'
  obtain ⟨x, rfl⟩ := g.surjective x'
  rw [hgmem, hX x, ← cantorSpace_memEquiv g hgmem, hgmem, evalb_of_memEquiv g hgmem φ]
  apply and_congr_right
  intro _
  have hfun : (fun i ↦ g ((x :> fun i ↦ (levySubRealization ξ hξ' hG).value (y i)) i)) =
      (g x :> fun i ↦ (levyContext (N.check κ) hG').check (y i)) := by
    funext i
    refine Fin.cases rfl (fun j ↦ ?_) i
    simp only [Matrix.cons_val_succ]
    exact hgval (y j)
  rw [hfun]

include hAC hU hc hω hκ in
/-- Over an arbitrary ground, every set of reals of `V[G]` definable from ground sets, reals and
ordinals has the perfect set property. -/
theorem perfectSetProperty_of_groundRealDefinable {X : (levyContext κ hG).Model}
    (hXc : X ⊆ cantorSpace (levyContext κ hG).Model)
    (hX : (levyContext κ hG).IsGroundRealDefinable X) : PerfectSetProperty X := by
  obtain ⟨n, φ, v, hv, hdef⟩ := hX
  obtain ⟨ξ, hξ, hall⟩ := isLocalized_tuple hG hω v (fun i ↦ isLocalized_parameter hAC hU hc hω hκ hG (hv i))
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

end

end ZFVP
