import ZFVP.ModelTheory.CohenStage
import ZFVP.ModelTheory.GenericFilterModel
import ZFVP.ModelTheory.SolovayFactorLemma
import ZFVP.ModelTheory.LevyAbsorptionFull
import ZFVP.ModelTheory.CohenRealName
import ZFVP.SetTheory.SequenceCollapseAbsorption
import ZFVP.SetTheory.LevyCollapseFull

/-! The Levy extension as a product extension over a Cohen real: for a real `x` of `V[G]` that is
Cohen over `V`, the extension `V[G]` is isomorphic to the extension by the product
`2^{<ω} × Coll(ω, <κ)` whose first factor generic is the filter of initial segments of `x`; the
isomorphism maps `x` to the value of the lifted Cohen real name and ground checks to checks. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
/-- The product presentation of `V[G]` over a Cohen real. -/
theorem exists_cohen_product_presentation {x : (levyContext κ hG).Model}
    (hx : (levyContext κ hG).IsCohenOver x) :
    ∃ (X : ForcingContext V) (g : (levyContext κ hG).Model ≃ X.Model) (ρ : ForcingName X.P),
      X.P = binarySequences V ×ˢ levyCollapse κ ∧
      X.R = productOrder (binarySequences V) (sequenceOrder ((2 : ℕ) : V)) (levyCollapse κ) (levyOrder κ) ∧
      X.one = ⟨∅, ∅⟩ₖ ∧
      (∀ y z, g y ∈ g z ↔ y ∈ z) ∧ (∀ a : V, g ((levyContext κ hG).check a) = X.check a) ∧
      ρ.val = nameAction (leftEmbedding (binarySequences V) ∅) (binarySequenceRealName V) ∧
      g x = X.ofName ρ ∧
      ∀ s : V, s ∈ firstProjectionGeneric X.G ↔ s ∈ binarySequences V ∧ (levyContext κ hG).check s ⊆ x := by
  -- the stage of `x`
  obtain ⟨ξ, hξ, y, hyval, hyc⟩ := exists_real_stage hAC hU hc hω hκ hG hx.1
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  have hξ' : ξ ⊆ κ := IsOrdinal.toIsTransitive.transitive ξ hξ
  let A := levySubContext ξ hξ' hG
  let L := levySubRealization ξ hξ' hG
  have hLground : ∀ a : V, L.ground a = (levyContext κ hG).check a := levySubRealization_ground ξ hξ' hG
  -- the filter of initial segments and the intermediate model
  have hQ : IsForcingPreorder (binarySequences V) (sequenceOrder ((2 : ℕ) : V)) := (sequenceOrder_poset _).1
  have htop : IsForcingTop (binarySequences V) (sequenceOrder ((2 : ℕ) : V)) ∅ := sequence_top _
  have hHQ := A.initialSegments_subset y
  have hfilter := A.initialSegments_filter hyc
  have hgen := A.initialSegments_generic L hLground hyval hx
  obtain ⟨D, hD, eH, hemem, hecheck, hegen⟩ := A.exists_intermediate_equiv hQ htop hHQ hfilter hgen hAC
  let CH := A.filterContext hQ htop hHQ hfilter hgen
  let N := A.subalgebraContext hD
  have hCHP : CH.P = binarySequences V := rfl
  have hCHone : CH.one = ∅ := rfl
  -- the factor lemma
  obtain ⟨Z, hZP, hZR, hZone, f, hfmem, hfcheck, hfval⟩ := solovay_factor hAC hU hc hω hκ hG ξ hξ hD
  -- absorption into the full collapse over the intermediate model
  have hACN : InternalChoice N.Model := N.internalChoice_of_ground hAC
  haveI : IsOrdinal (N.check κ) := (N.check_ordinal_iff κ).mpr inferInstance
  haveI : IsOrdinal (N.check ξ) := (N.check_ordinal_iff ξ).mpr inferInstance
  have hξN : N.check ξ ∈ N.check κ := (N.check_mem_iff _ _).mpr hξ
  have hωN : (ω : N.Model) ∈ N.check κ := by
    rw [← N.check_omega_eq]
    exact (N.check_mem_iff _ _).mpr hω
  obtain ⟨ν, hν, hsmall⟩ := levyCollapse_cardLE_small hAC hU hc hω hξ
  have hνN : N.check ν ∈ N.check κ := (N.check_mem_iff _ _).mpr hν
  have hcoll : N.check (levyCollapse ξ) = levyCollapse (N.check ξ) := N.checkEmbedding.map_levyCollapse ξ
  have hcollκ : N.check (levyCollapse κ) = levyCollapse (N.check κ) := N.checkEmbedding.map_levyCollapse κ
  have hordκ : N.check (levyOrder κ) = levyOrder (N.check κ) := N.checkEmbedding.map_levyOrder κ
  have habove : N.check (levyCollapseAbove κ ξ) = levyCollapseAbove (N.check κ) (N.check ξ) :=
    N.checkEmbedding.map_levyCollapseAbove κ ξ
  have hrestr : N.check (restrictedOrder (levyOrder κ) (levyCollapseAbove κ ξ)) =
      restrictedOrder (N.check (levyOrder κ)) (N.check (levyCollapseAbove κ ξ)) :=
    N.checkEmbedding.map_restrictedOrder _ _
  have hsmallN : levyCollapse (N.check ξ) ≤# N.check ν := by
    rw [← hcoll]
    exact N.checkEmbedding.map_cardLE hsmall
  have hZP' : Z.P = levyCollapseAbove (N.check κ) (N.check ξ) := hZP.trans habove
  have hZR' : Z.R = restrictedOrder (levyOrder (N.check κ)) (levyCollapseAbove (N.check κ) (N.check ξ)) := by
    rw [hZR, hrestr, hordκ, habove]
  obtain ⟨Z', hZ'P, hZ'R, hZ'one, g₁, hg₁mem, hg₁check⟩ :=
    exists_full_collapse_context hACN hξN hωN hνN hsmallN Z hZP' hZR'
  have hZ'P' : Z'.P = N.check (levyCollapse κ) := hZ'P.trans hcollκ.symm
  have hZ'R' : Z'.R = N.check (levyOrder κ) := hZ'R.trans hordκ.symm
  have hZ'one' : Z'.one = N.check ∅ := hZ'one.trans N.check_empty.symm
  -- base change to the Cohen extension
  have he' : ∀ a b : N.Model, eH.symm a ∈ eH.symm b ↔ a ∈ b := by
    intro a b
    rw [← hemem (eH.symm a) (eH.symm b), Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hsymcheck : ∀ a : V, eH.symm (N.check a) = CH.check a := by
    intro a
    rw [← hecheck a, Equiv.symm_apply_apply]
  let Z₃ := Z'.baseChange eH.symm he'
  let g₂ := Z'.baseChangeEquiv eH.symm he'
  have hZ₃P : Z₃.P = CH.check (levyCollapse κ) := by
    change eH.symm Z'.P = _
    rw [hZ'P', hsymcheck]
  have hZ₃R : Z₃.R = CH.check (levyOrder κ) := by
    change eH.symm Z'.R = _
    rw [hZ'R', hsymcheck]
  have hZ₃one : Z₃.one = CH.check ∅ := by
    change eH.symm Z'.one = _
    rw [hZ'one', hsymcheck]
  -- the product context
  have h₂ : IsForcingPreorder (levyCollapse κ) (levyOrder κ) := (levyCollapse_poset κ).1
  have t₂ : IsForcingTop (levyCollapse κ) (levyOrder κ) ∅ := levyCollapse_top κ
  let X := productContext CH.order CH.top h₂ t₂ (combinedGeneric_generic CH Z₃ hZ₃P hZ₃R)
  let g₃ := twoStepEquiv CH h₂ t₂ Z₃ hZ₃P hZ₃R hZ₃one
  let ρ₀ : ForcingName CH.P := ⟨binarySequenceRealName V, binarySequenceRealName_isName⟩
  refine ⟨X, ((f.trans g₁).trans g₂).trans g₃.symm,
    productNameLift CH.order CH.top h₂ t₂ (combinedGeneric_generic CH Z₃ hZ₃P hZ₃R) ρ₀, rfl, rfl, rfl,
    ?_, ?_, rfl, ?_, ?_⟩
  · intro a b
    simp only [Equiv.trans_apply]
    rw [← twoStepEquiv_mem_iff CH h₂ t₂ Z₃ hZ₃P hZ₃R hZ₃one, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, Z'.baseChangeEquiv_mem_iff, hg₁mem, hfmem]
  · intro a
    simp only [Equiv.trans_apply]
    rw [hfcheck, hg₁check]
    have h := Z'.baseChangeEquiv_check eH.symm he' (N.check a)
    change g₂ (Z'.check (N.check a)) = _ at h
    rw [h, hsymcheck]
    apply g₃.injective
    rw [Equiv.apply_symm_apply]
    exact (twoStepEquiv_check CH h₂ t₂ Z₃ hZ₃P hZ₃R hZ₃one a).symm
  · -- the image of `x`
    simp only [Equiv.trans_apply]
    -- the copy of `x` in the Cohen extension and in the intermediate model
    let xC : CH.Model := CH.ofName ρ₀
    have hxC : xC = ⋃ˢ CH.genericSet := by
      apply mem_ext
      intro z
      rw [mem_sUnion_iff]
      constructor
      · intro hz
        obtain ⟨s, hs, w, hw, rfl⟩ := (CH.mem_ofName_binarySequenceRealName hCHP hCHone z).mp hz
        exact ⟨CH.check s, (CH.mem_genericSet_iff _).mpr ⟨s, hs, rfl⟩, (CH.check_mem_iff _ _).mpr hw⟩
      · rintro ⟨t, ht, hzt⟩
        obtain ⟨s, hs, rfl⟩ := (CH.mem_genericSet_iff t).mp ht
        obtain ⟨w, hw, rfl⟩ := (CH.mem_check_iff _ _).mp hzt
        exact (CH.mem_ofName_binarySequenceRealName hCHP hCHone _).mpr ⟨s, hs, w, hw, rfl⟩
    let xN : N.Model := eH xC
    have hjH := MembershipEndExtension.ofEquiv eH hemem
    have hxN : (A.subalgebraRealization hD).value xN = A.booleanEquiv y := by
      have h1 : eH xC = ⋃ˢ (eH CH.genericSet) := by
        rw [hxC]
        exact (MembershipEndExtension.ofEquiv eH hemem).map_sUnion CH.genericSet
      have h2 : (A.subalgebraRealization hD).value (⋃ˢ (eH CH.genericSet)) =
          ⋃ˢ ((A.subalgebraRealization hD).value (eH CH.genericSet)) :=
        (A.subalgebraRealization hD).embedding.map_sUnion _
      have h3 : A.booleanEquiv (⋃ˢ (A.initialSegments y)) = ⋃ˢ (A.booleanEquiv (A.initialSegments y)) :=
        A.recoveredRealization.embedding.map_sUnion _
      change (A.subalgebraRealization hD).value (eH xC) = _
      rw [h1, h2, hegen, ← h3, A.sUnion_initialSegments_eq hyc]
    have hxN' : (A.quotientContext hD).check xN = (A.booleanEquiv.trans (A.quotientEquiv hD)) y := by
      rw [← A.quotientEquiv_value hD xN, hxN]
      rfl
    have hxι : x = (levyProductEquiv ξ hξ' hG).symm ((levyProductContext ξ hξ' hG).check
        ((A.booleanEquiv.trans (A.quotientEquiv hD)).symm ((A.quotientContext hD).check xN))) := by
      rw [hxN', Equiv.symm_apply_apply, ← hyval, ← levyProductEquiv_value ξ hξ' hG y, Equiv.symm_apply_apply]
    rw [hxι, hfval xN, hg₁check]
    have h := Z'.baseChangeEquiv_check eH.symm he' xN
    change g₂ (Z'.check xN) = _ at h
    rw [h]
    have hx3 : eH.symm xN = xC := Equiv.symm_apply_apply eH xC
    rw [hx3]
    apply g₃.injective
    rw [Equiv.apply_symm_apply]
    exact (twoStepEquiv_lift CH h₂ t₂ Z₃ hZ₃P hZ₃R hZ₃one ρ₀).symm
  · intro s
    change s ∈ firstProjectionGeneric (combinedGeneric CH Z₃) ↔ _
    rw [firstProjection_combinedGeneric CH Z₃ hZ₃P hZ₃R, A.mem_filterContext_G]
    exact A.check_mem_initialSegments_iff_of_value L hLground hyval s

end

end ZFVP
