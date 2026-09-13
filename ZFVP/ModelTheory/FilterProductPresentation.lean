import ZFVP.ModelTheory.CohenProductPresentation
import ZFVP.ModelTheory.SolovayLocalization

/-! The Levy extension as a product extension over a generic filter: for a ground poset `Q` and a
filter `H` of `V[G]` on `Q̌` meeting every ground dense set and lying in a bounded stage, `V[G]` is
isomorphic to the extension by the product `Q × Coll(ω, <κ)` whose first factor generic is `H`;
ground checks go to checks, and the internal value at `H` of a checked ground `Q`-name goes to
the value of the lifted name. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC hU hc hω hκ in
/-- The product presentation of `V[G]` over a generic filter on a ground poset. -/
theorem exists_filter_product_presentation {Q S one : V} (hQ : IsForcingPreorder Q S)
    (htop : IsForcingTop Q S one) {H : (levyContext κ hG).Model}
    (hHQ : H ⊆ (levyContext κ hG).check Q)
    (hfilter : IsForcingFilter ((levyContext κ hG).check Q) ((levyContext κ hG).check S) H)
    (hgen : ∀ D : V, ForcingDense Q S D → ∃ q ∈ D, (levyContext κ hG).check q ∈ H)
    (hloc : IsLocalized hG H) :
    ∃ (X : ForcingContext V) (g : (levyContext κ hG).Model ≃ X.Model),
      X.P = Q ×ˢ levyCollapse κ ∧ X.R = productOrder Q S (levyCollapse κ) (levyOrder κ) ∧
      X.one = ⟨one, ∅⟩ₖ ∧
      (∀ y z, g y ∈ g z ↔ y ∈ z) ∧ (∀ a : V, g ((levyContext κ hG).check a) = X.check a) ∧
      (∀ τ : V, IsForcingName Q τ → ∃ ρ : ForcingName X.P,
        ρ.val = nameAction (leftEmbedding Q ∅) τ ∧
        g (nameValue H ((levyContext κ hG).check τ)) = X.ofName ρ) ∧
      (∀ τ z : V, IsForcingName Q τ →
        ((levyContext κ hG).check z ∈ nameValue H ((levyContext κ hG).check τ) ↔
          ∃ q, (levyContext κ hG).check q ∈ H ∧ ForcesCheckedMember Q S one τ q z)) ∧
      ∀ q : V, q ∈ firstProjectionGeneric X.G ↔ (levyContext κ hG).check q ∈ H := by
  obtain ⟨ξ, hξ, Hξ, hHval⟩ := hloc
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  have hξ' : ξ ⊆ κ := IsOrdinal.toIsTransitive.transitive ξ hξ
  let A := levySubContext ξ hξ' hG
  let L := levySubRealization ξ hξ' hG
  have hLground : ∀ a : V, L.ground a = (levyContext κ hG).check a := levySubRealization_ground ξ hξ' hG
  have hvc : ∀ a : V, L.value (A.check a) = (levyContext κ hG).check a :=
    fun a ↦ (L.value_check a).trans (hLground a)
  have hmem : ∀ a b : A.Model, L.value a ∈ L.value b ↔ a ∈ b := fun a b ↦ L.value_mem_iff a b
  have hk : ∀ a b : A.Model, L.value ⟨a, b⟩ₖ = ⟨L.value a, L.value b⟩ₖ := fun a b ↦ L.embedding.map_kpair a b
  have hHval' : L.value Hξ = H := hHval
  -- the filter in the stage
  have hHQ' : Hξ ⊆ A.check Q := by
    have h : L.value Hξ ⊆ L.value (A.check Q) := by
      rw [hHval', hvc]
      exact hHQ
    exact (L.embedding.subset_iff _ _).mp h
  have hfilter' : IsForcingFilter (A.check Q) (A.check S) Hξ := by
    refine ⟨hHQ', ?_, ?_, ?_⟩
    · obtain ⟨p, hp⟩ := hfilter.2.1
      rw [← hHval'] at hp
      obtain ⟨p₀, hp₀, _⟩ := L.embedding.endExtension Hξ p hp
      exact ⟨p₀, hp₀⟩
    · intro s hs t ht hst
      have h1 : L.value s ∈ H := by rw [← hHval']; exact (hmem _ _).mpr hs
      have h2 : L.value t ∈ (levyContext κ hG).check Q := by rw [← hvc]; exact (hmem _ _).mpr ht
      have h3 : ⟨L.value s, L.value t⟩ₖ ∈ (levyContext κ hG).check S := by
        rw [← hk, ← hvc]
        exact (hmem _ _).mpr hst
      have := hfilter.2.2.1 _ h1 _ h2 h3
      rw [← hHval'] at this
      exact (hmem _ _).mp this
    · intro s hs t ht
      have h1 : L.value s ∈ H := by rw [← hHval']; exact (hmem _ _).mpr hs
      have h2 : L.value t ∈ H := by rw [← hHval']; exact (hmem _ _).mpr ht
      obtain ⟨r, hr, hrs, hrt⟩ := hfilter.2.2.2 _ h1 _ h2
      rw [← hHval'] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := L.embedding.endExtension Hξ r hr
      refine ⟨r₀, hr₀, ?_, ?_⟩
      · have := hrs
        change ⟨L.value r₀, L.value s⟩ₖ ∈ (levyContext κ hG).check S at this
        rw [← hk, ← hvc] at this
        exact (hmem _ _).mp this
      · have := hrt
        change ⟨L.value r₀, L.value t⟩ₖ ∈ (levyContext κ hG).check S at this
        rw [← hk, ← hvc] at this
        exact (hmem _ _).mp this
  have hgen' : ∀ D : V, ForcingDense Q S D → ∃ q ∈ D, A.check q ∈ Hξ := by
    intro D hD
    obtain ⟨q, hq, hqH⟩ := hgen D hD
    refine ⟨q, hq, ?_⟩
    rw [← hHval', ← hvc] at hqH
    exact (hmem _ _).mp hqH
  obtain ⟨D, hD, eH, hemem, hecheck, hegen⟩ := A.exists_intermediate_equiv hQ htop hHQ' hfilter' hgen' hAC
  let CH := A.filterContext hQ htop hHQ' hfilter' hgen'
  let N := A.subalgebraContext hD
  -- the factor lemma
  obtain ⟨Z, hZP, hZR, hZone, f, hfmem, hfcheck, hfval⟩ := solovay_factor hAC hU hc hω hκ hG ξ hξ hD
  -- absorption into the full collapse over the intermediate model
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
  -- base change to the `Q`-extension
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
  -- membership in the value of a ground name
  have hvalue : ∀ τ z : V, IsForcingName Q τ →
      ((levyContext κ hG).check z ∈ nameValue H ((levyContext κ hG).check τ) ↔
        ∃ q, (levyContext κ hG).check q ∈ H ∧ ForcesCheckedMember Q S one τ q z) := by
    intro τ z hτ
    let τ' : ForcingName CH.P := ⟨τ, hτ⟩
    have hy : L.value (nameValue Hξ (A.check τ)) = nameValue H ((levyContext κ hG).check τ) := by
      have h := L.embedding.map_nameValue Hξ (A.check τ)
      change L.value (nameValue Hξ (A.check τ)) = nameValue (L.value Hξ) (L.value (A.check τ)) at h
      rw [h, hHval', hvc]
    have hxN : (A.subalgebraRealization hD).value (eH (CH.ofName τ')) =
        A.booleanEquiv (nameValue Hξ (A.check τ)) := by
      have h1 : eH (CH.ofName τ') = nameValue (eH CH.genericSet) (N.check τ) := by
        have h := (MembershipEndExtension.ofEquiv eH hemem).map_nameValue CH.genericSet (CH.check τ)
        change eH (nameValue CH.genericSet (CH.check τ)) = nameValue (eH CH.genericSet) (eH (CH.check τ)) at h
        rw [← CH.nameValue_genericSet_check τ', h, hecheck]
      have h2 : (A.subalgebraRealization hD).value (nameValue (eH CH.genericSet) (N.check τ)) =
          nameValue ((A.subalgebraRealization hD).value (eH CH.genericSet))
            ((A.subalgebraRealization hD).value (N.check τ)) :=
        (A.subalgebraRealization hD).embedding.map_nameValue _ _
      have h3 : (A.subalgebraRealization hD).value (N.check τ) = A.booleanContext.check τ :=
        (A.subalgebraRealization hD).value_check τ
      have h4 : A.booleanEquiv (nameValue Hξ (A.check τ)) =
          nameValue (A.booleanEquiv Hξ) (A.booleanEquiv (A.check τ)) :=
        A.recoveredRealization.embedding.map_nameValue _ _
      rw [h1, h2, hegen, h3, h4, A.booleanEquiv_check]
    have hz : (A.subalgebraRealization hD).value (eH (CH.check z)) = A.booleanEquiv (A.check z) := by
      rw [hecheck, (A.subalgebraRealization hD).value_check, A.booleanEquiv_check]
      rfl
    rw [← hy, ← hvc, hmem, ← A.booleanEquiv_mem_iff, ← hz, ← hxN,
      (A.subalgebraRealization hD).value_mem_iff, hemem, CH.checkedMember_truth τ' z]
    constructor
    · rintro ⟨q, hq, hforce⟩
      refine ⟨q, ?_, hforce⟩
      rw [← hHval', ← hvc]
      exact (hmem _ _).mpr ((A.mem_filterContext_G _ _ _ _ _ q).mp hq)
    · rintro ⟨q, hq, hforce⟩
      refine ⟨q, ?_, hforce⟩
      rw [← hHval', ← hvc] at hq
      exact (A.mem_filterContext_G _ _ _ _ _ q).mpr ((hmem _ _).mp hq)
  refine ⟨X, ((f.trans g₁).trans g₂).trans g₃.symm, rfl, rfl, rfl, ?_, ?_, ?_, hvalue, ?_⟩
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
  · -- the values of ground names
    intro τ hτ
    let τ' : ForcingName CH.P := ⟨τ, hτ⟩
    refine ⟨productNameLift CH.order CH.top h₂ t₂ (combinedGeneric_generic CH Z₃ hZ₃P hZ₃R) τ', rfl, ?_⟩
    simp only [Equiv.trans_apply]
    -- the copies of the value in the `Q`-extension and in the intermediate model
    let xC : CH.Model := CH.ofName τ'
    let xN : N.Model := eH xC
    let y : A.Model := nameValue Hξ (A.check τ)
    have hxC : xC = nameValue CH.genericSet (CH.check τ) := (CH.nameValue_genericSet_check τ').symm
    have hxN : (A.subalgebraRealization hD).value xN = A.booleanEquiv y := by
      have h1 : eH xC = nameValue (eH CH.genericSet) (N.check τ) := by
        have h := (MembershipEndExtension.ofEquiv eH hemem).map_nameValue CH.genericSet (CH.check τ)
        change eH (nameValue CH.genericSet (CH.check τ)) = nameValue (eH CH.genericSet) (eH (CH.check τ)) at h
        rw [hxC, h, hecheck]
      have h2 : (A.subalgebraRealization hD).value (nameValue (eH CH.genericSet) (N.check τ)) =
          nameValue ((A.subalgebraRealization hD).value (eH CH.genericSet))
            ((A.subalgebraRealization hD).value (N.check τ)) :=
        (A.subalgebraRealization hD).embedding.map_nameValue _ _
      have h3 : (A.subalgebraRealization hD).value (N.check τ) = A.booleanContext.check τ :=
        (A.subalgebraRealization hD).value_check τ
      have h4 : A.booleanEquiv (nameValue Hξ (A.check τ)) =
          nameValue (A.booleanEquiv Hξ) (A.booleanEquiv (A.check τ)) :=
        A.recoveredRealization.embedding.map_nameValue _ _
      change (A.subalgebraRealization hD).value (eH xC) = _
      rw [h1, h2, hegen, h3, h4, A.booleanEquiv_check]
    have hxN' : (A.quotientContext hD).check xN = (A.booleanEquiv.trans (A.quotientEquiv hD)) y := by
      rw [← A.quotientEquiv_value hD xN, hxN]
      rfl
    have hy : L.value y = nameValue H ((levyContext κ hG).check τ) := by
      have h := L.embedding.map_nameValue Hξ (A.check τ)
      change L.value (nameValue Hξ (A.check τ)) = nameValue (L.value Hξ) (L.value (A.check τ)) at h
      change L.value (nameValue Hξ (A.check τ)) = _
      rw [h, hHval', hvc]
    have hxι : nameValue H ((levyContext κ hG).check τ) =
        (levyProductEquiv ξ hξ' hG).symm ((levyProductContext ξ hξ' hG).check
          ((A.booleanEquiv.trans (A.quotientEquiv hD)).symm ((A.quotientContext hD).check xN))) := by
      rw [hxN', Equiv.symm_apply_apply, ← hy, ← levyProductEquiv_value ξ hξ' hG y, Equiv.symm_apply_apply]
    rw [hxι, hfval xN, hg₁check]
    have h := Z'.baseChangeEquiv_check eH.symm he' xN
    change g₂ (Z'.check xN) = _ at h
    rw [h]
    have hx3 : eH.symm xN = xC := Equiv.symm_apply_apply eH xC
    rw [hx3]
    apply g₃.injective
    rw [Equiv.apply_symm_apply]
    exact (twoStepEquiv_lift CH h₂ t₂ Z₃ hZ₃P hZ₃R hZ₃one τ').symm
  · intro q
    change q ∈ firstProjectionGeneric (combinedGeneric CH Z₃) ↔ _
    rw [firstProjection_combinedGeneric CH Z₃ hZ₃P hZ₃R, A.mem_filterContext_G, ← hHval', ← hvc]
    exact (hmem _ _).symm

end

end ZFVP
