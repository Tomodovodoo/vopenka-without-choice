import ZFVP.ModelTheory.LevyAbsorptionFull
import ZFVP.ModelTheory.HomogeneousTruth
import ZFVP.ModelTheory.ForcingSmallUltrafilter
import ZFVP.ModelTheory.CohenBridgeLemmas
import ZFVP.ModelTheory.CohenDecision
import ZFVP.ModelTheory.SolovayLocalization
import ZFVP.SetTheory.UltrafilterFibers

/-! Change of ground: the Levy extension `V[G]` is a Levy extension of every bounded stage
`V[G_ξ]`, in which `κ` is still measurable. Hence sets of reals definable from parameters of a
bounded stage, in particular from ground sets, reals and ordinals, have the Baire property. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A measurable ordinal is an initial ordinal. -/
theorem initial_of_measurable {κ U : V} [IsOrdinal κ] (hU : IsNonprincipalSetUltrafilter κ U)
    (hc : IsOrdinalComplete κ U) : IsInitialOrdinal κ :=
  ⟨inferInstance, fun α hα h ↦ measurable_not_cardLE_power hU hc hα (h.trans (cardLT_power α).1)⟩

section

variable {M M' : Type*} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  [SetStructure M'] [Nonempty M'] [M'↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (e : M ≃ M') (he : ∀ x y, e x ∈ e y ↔ x ∈ y)

include he in
theorem baireProperty_memEquiv (X : M) : BaireProperty (e X) ↔ BaireProperty X := by
  have h1 : bairePropertyFormula.Evalb ![X] ↔ BaireProperty X := (bairePropertyFormula_defined (V := M)).iff ![X]
  have h2 : bairePropertyFormula.Evalb ![e X] ↔ BaireProperty (e X) :=
    (bairePropertyFormula_defined (V := M')).iff ![e X]
  have h3 : (fun i ↦ e (![X] i)) = ![e X] := by
    funext i
    exact Fin.cases rfl (fun j ↦ j.elim0) i
  rw [← h1, ← h2, evalb_of_memEquiv e he, h3]

include he in
theorem cantorSpace_memEquiv : e (cantorSpace M) = cantorSpace M' := by
  have h1 : cantorSpaceFormula.Evalb ![cantorSpace M] ↔ cantorSpace M = cantorSpace M :=
    (cantorSpaceFormula_defined (V := M)).iff ![cantorSpace M]
  have h2 : cantorSpaceFormula.Evalb ![e (cantorSpace M)] ↔ e (cantorSpace M) = cantorSpace M' :=
    (cantorSpaceFormula_defined (V := M')).iff ![e (cantorSpace M)]
  have h3 : (fun i ↦ e (![cantorSpace M] i)) = ![e (cantorSpace M)] := by
    funext i
    exact Fin.cases rfl (fun j ↦ j.elim0) i
  rw [← h2, ← h3]
  exact (evalb_of_memEquiv e he cantorSpaceFormula ![cantorSpace M]).mp (h1.mpr rfl)

end

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)
  (ξ : V) [IsOrdinal ξ] (hξ : ξ ∈ κ)

include hAC hU hc hω in
/-- `V[G]` is a Levy extension of the stage `V[G_ξ]`. -/
theorem exists_ground_change :
    ∃ (G' : Set (levySubContext ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).Model)
      (hG' : IsExternalForcingGeneric
        (levyCollapse ((levySubContext ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).check κ))
        (levyOrder ((levySubContext ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).check κ)) G')
      (g : (levyContext κ hG).Model ≃
        (levyContext ((levySubContext ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).check κ) hG').Model),
      (∀ x y, g x ∈ g y ↔ x ∈ y) ∧
      ∀ y : (levySubContext ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).Model,
        g ((levySubRealization ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).value y) =
          (levyContext ((levySubContext ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).check κ) hG').check y := by
  have hξ' : ξ ⊆ κ := IsOrdinal.toIsTransitive.transitive ξ hξ
  let N := levySubContext ξ hξ' hG
  let Qup := levyProductContext ξ hξ' hG
  have hACN : InternalChoice N.Model := N.internalChoice_of_ground hAC
  have : IsOrdinal (N.check κ) := (N.check_ordinal_iff κ).mpr inferInstance
  have : IsOrdinal (N.check ξ) := (N.check_ordinal_iff ξ).mpr inferInstance
  have hξN : N.check ξ ∈ N.check κ := (N.check_mem_iff _ _).mpr hξ
  have hωN : (ω : N.Model) ∈ N.check κ := by
    rw [← N.check_omega_eq]
    exact (N.check_mem_iff _ _).mpr hω
  obtain ⟨ν, hν, hsmall⟩ := levyCollapse_cardLE_small hAC hU hc hω hξ
  have hνN : N.check ν ∈ N.check κ := (N.check_mem_iff _ _).mpr hν
  have hcoll : N.check (levyCollapse ξ) = levyCollapse (N.check ξ) := N.checkEmbedding.map_levyCollapse ξ
  have hsmallN : levyCollapse (N.check ξ) ≤# N.check ν := by
    rw [← hcoll]
    exact N.checkEmbedding.map_cardLE hsmall
  obtain ⟨Z', hZ'P, hZ'R, hZ'one, g₁, hg₁mem, hg₁check⟩ :=
    exists_full_collapse_context hACN hξN hωN hνN hsmallN Qup (levyProductConditions_eq ξ hξ' hG)
      (levyProductOrder_eq ξ hξ' hG)
  have hG' : IsExternalForcingGeneric (levyCollapse (N.check κ)) (levyOrder (N.check κ)) Z'.G := by
    have h := Z'.generic
    rwa [hZ'P, hZ'R] at h
  have hctx : Z' = levyContext (N.check κ) hG' :=
    ForcingContext.ext hZ'P hZ'R hZ'one rfl
  refine ⟨Z'.G, hG', (levyProductEquiv ξ hξ' hG).trans (g₁.trans (ForcingContext.modelCast hctx)), ?_, ?_⟩
  · intro x y
    simp only [Equiv.trans_apply]
    rw [ForcingContext.modelCast_mem_iff, hg₁mem, levyProductEquiv_mem_iff]
  · intro y
    simp only [Equiv.trans_apply]
    rw [levyProductEquiv_value, hg₁check, ForcingContext.modelCast_check]

include hAC hU hc hω in
/-- Sets of reals definable from parameters of a bounded stage have the Baire property. -/
theorem baireProperty_of_stage_definable {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (y : Fin n → (levySubContext ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).Model)
    {X : (levyContext κ hG).Model}
    (hX : ∀ x, x ∈ X ↔ x ∈ cantorSpace (levyContext κ hG).Model ∧
      φ.Evalb (x :> fun i ↦ (levySubRealization ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).value (y i))) :
    BaireProperty X := by
  have hξ' : ξ ⊆ κ := IsOrdinal.toIsTransitive.transitive ξ hξ
  obtain ⟨G', hG', g, hgmem, hgval⟩ := exists_ground_change hAC hU hc hω hG ξ hξ
  let N := levySubContext ξ hξ' hG
  let W' := levyContext (N.check κ) hG'
  -- measurability of `κ` in the stage
  have hACN : InternalChoice N.Model := N.internalChoice_of_ground hAC
  obtain ⟨ν, hν, hsmall⟩ := levyCollapse_cardLE_small hAC hU hc hω hξ
  have hNP : N.P ≤# ν := hsmall
  obtain ⟨hU', hc'⟩ := N.derivedFilter_ultrafilter hAC hU hc hν hNP
  have : IsOrdinal (N.check κ) := (N.check_ordinal_iff κ).mpr inferInstance
  have hωN : (ω : N.Model) ∈ N.check κ := by
    rw [← N.check_omega_eq]
    exact (N.check_mem_iff _ _).mpr hω
  have hκN : IsInitialOrdinal (N.check κ) := initial_of_measurable hU' hc'
  -- transport the set
  rw [← baireProperty_memEquiv g hgmem X]
  apply baireProperty_of_ground_definable hACN hU' hc' hωN hκN hG' φ y
  intro x'
  obtain ⟨x, rfl⟩ := g.surjective x'
  rw [hgmem, hX x, ← cantorSpace_memEquiv g hgmem, hgmem, evalb_of_memEquiv g hgmem φ]
  apply and_congr_right
  intro _
  have hfun : (fun i ↦ g ((x :> fun i ↦ (levySubRealization ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).value (y i)) i)) =
      (g x :> fun i ↦ (levyContext (N.check κ) hG').check (y i)) := by
    funext i
    refine Fin.cases rfl (fun j ↦ ?_) i
    simp only [Matrix.cons_val_succ]
    exact hgval (y j)
  rw [hfun]

end

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
/-- Sets of reals of `V[G]` definable from ground sets, reals and ordinals have the Baire
property. -/
theorem baireProperty_of_groundRealDefinable {X : (levyContext κ hG).Model}
    (hXc : X ⊆ cantorSpace (levyContext κ hG).Model)
    (hX : (levyContext κ hG).IsGroundRealDefinable X) : BaireProperty X := by
  obtain ⟨n, φ, v, hv, hdef⟩ := hX
  obtain ⟨ξ, hξ, hall⟩ := isLocalized_tuple hG hω v (fun i ↦ isLocalized_parameter hAC hU hc hω hκ hG (hv i))
  haveI : IsOrdinal ξ := IsOrdinal.of_mem hξ
  choose y hy using hall
  refine baireProperty_of_stage_definable hAC hU hc hω hG ξ hξ φ y ?_
  intro x
  constructor
  · intro hx
    refine ⟨hXc x hx, ?_⟩
    have h := (hdef x).mp hx
    have hvy : (fun i ↦ (levySubRealization ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).value (y i)) = v :=
      funext hy
    rw [hvy]
    exact h
  · rintro ⟨_, h⟩
    have hvy : (fun i ↦ (levySubRealization ξ (IsOrdinal.toIsTransitive.transitive ξ hξ) hG).value (y i)) = v :=
      funext hy
    rw [hvy] at h
    exact (hdef x).mpr h

end

end ZFVP
