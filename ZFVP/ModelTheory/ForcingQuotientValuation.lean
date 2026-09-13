import ZFVP.ModelTheory.ForcingQuotientZF
import ZFVP.ModelTheory.TransitiveZFForcingOrders
import ZFVP.ModelTheory.GroundAtomicTruth
import ZFVP.ModelTheory.ForcingExtensionDomain
import ZFVP.SetTheory.MembershipIso

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem genericMeets_val_iff (G : V) (A : SetDomain U) :
    GenericMeets {p : SetDomain U | p.val ∈ G} A ↔ ∃ p ∈ G, p ∈ A.val := by
  constructor
  · rintro ⟨p, hpG, hpA⟩
    exact ⟨p.val, hpG, hpA⟩
  · rintro ⟨p, hpG, hpA⟩
    exact ⟨⟨p, (inferInstance : IsTransitive U).mem_trans hpA A.property⟩, hpG, hpA⟩

theorem nameValue_eq_genericMeets (P R : SetDomain U) {G : V}
    (hR : IsForcingPreorder P R) (hG : IsGroundForcingGeneric U P.val R.val G)
    (σ τ : ForcingName P) :
    nameValue G σ.val.val = nameValue G τ.val.val ↔
      GenericMeets {p : SetDomain U | p.val ∈ G} (atomicEquality P R σ.val τ.val) := by
  rw [genericMeets_val_iff U, atomicEquality_val U]
  exact ground_atomicEquality_iff U P R σ.val τ.val ((forcingPreorder_iff U P R).mp hR) hG

theorem nameValue_mem_genericMeets (P R : SetDomain U) {G : V}
    (hR : IsForcingPreorder P R) (hG : IsGroundForcingGeneric U P.val R.val G)
    (σ τ : ForcingName P) :
    nameValue G σ.val.val ∈ nameValue G τ.val.val ↔
      GenericMeets {p : SetDomain U | p.val ∈ G} (atomicMembership P R σ.val τ.val) := by
  rw [genericMeets_val_iff U, atomicMembership_val U]
  exact ground_atomicMembership_iff U P R σ.val τ.val ((forcingPreorder_iff U P R).mp hR) hG

noncomputable def groundNameValue (P : SetDomain U) (G : V) (σ : ForcingName P) :
    SetDomain (forcingExtensionDomain U P.val G) :=
  ⟨nameValue G σ.val.val, (mem_forcingExtensionDomain_iff _ _ _ _).mpr
    ⟨σ.val.val, σ.val.property, (forcingName_iff U P σ.val).mp σ.property, rfl⟩⟩

noncomputable def forcingQuotientValue (P R : SetDomain U) (G : V)
    (hR : IsForcingPreorder P R) (hG : IsGroundForcingGeneric U P.val R.val G) :
    ForcingQuotient P R {p : SetDomain U | p.val ∈ G} hR
      ((groundForcingGeneric_iff_external U P R G hG.1.1).mp hG).1 →
        SetDomain (forcingExtensionDomain U P.val G) :=
  Quotient.lift (groundNameValue U P G) (by
    intro σ τ he
    exact Subtype.ext ((nameValue_eq_genericMeets U P R hR hG σ τ).mpr he))

theorem forcingQuotientValue_mk (P R : SetDomain U) (G : V)
    (hR : IsForcingPreorder P R) (hG : IsGroundForcingGeneric U P.val R.val G) (σ : ForcingName P) :
    forcingQuotientValue U P R G hR hG (forcingQuotientMk P R _ hR _ σ) = groundNameValue U P G σ := rfl

theorem forcingQuotientValue_bijective (P R : SetDomain U) (G : V)
    (hR : IsForcingPreorder P R) (hG : IsGroundForcingGeneric U P.val R.val G) :
    Function.Bijective (forcingQuotientValue U P R G hR hG) := by
  constructor
  · intro x y he
    obtain ⟨σ, rfl⟩ := forcingQuotientMk_surjective P R _ hR _ x
    obtain ⟨τ, rfl⟩ := forcingQuotientMk_surjective P R _ hR _ y
    apply (forcingQuotientMk_eq_iff P R _ hR _ _ _).mpr
    exact (nameValue_eq_genericMeets U P R hR hG σ τ).mp (congrArg Subtype.val he)
  · intro x
    obtain ⟨τ, hτU, hτN, he⟩ := (mem_forcingExtensionDomain_iff _ _ _ _).mp x.property
    let τ' : SetDomain U := ⟨τ, hτU⟩
    let σ : ForcingName P := ⟨τ', (forcingName_iff U P τ').mpr hτN⟩
    exact ⟨forcingQuotientMk P R _ hR _ σ, Subtype.ext he.symm⟩

theorem forcingQuotientValue_mem_iff (P R : SetDomain U) (G : V)
    (hR : IsForcingPreorder P R) (hG : IsGroundForcingGeneric U P.val R.val G)
    (x y : ForcingQuotient P R {p : SetDomain U | p.val ∈ G} hR
      ((groundForcingGeneric_iff_external U P R G hG.1.1).mp hG).1) :
    forcingQuotientValue U P R G hR hG x ∈ forcingQuotientValue U P R G hR hG y ↔ x ∈ y := by
  obtain ⟨σ, rfl⟩ := forcingQuotientMk_surjective P R _ hR _ x
  obtain ⟨τ, rfl⟩ := forcingQuotientMk_surjective P R _ hR _ y
  exact nameValue_mem_genericMeets U P R hR hG σ τ

noncomputable def forcingQuotientEquiv (P R : SetDomain U) (G : V)
    (hR : IsForcingPreorder P R) (hG : IsGroundForcingGeneric U P.val R.val G) :
    ForcingQuotient P R {p : SetDomain U | p.val ∈ G} hR
      ((groundForcingGeneric_iff_external U P R G hG.1.1).mp hG).1 ≃
        SetDomain (forcingExtensionDomain U P.val G) :=
  Equiv.ofBijective (forcingQuotientValue U P R G hR hG) (forcingQuotientValue_bijective U P R G hR hG)

theorem forcingQuotientEquiv_mem_iff (P R : SetDomain U) (G : V)
    (hR : IsForcingPreorder P R) (hG : IsGroundForcingGeneric U P.val R.val G)
    (x y : ForcingQuotient P R {p : SetDomain U | p.val ∈ G} hR
      ((groundForcingGeneric_iff_external U P R G hG.1.1).mp hG).1) :
    forcingQuotientEquiv U P R G hR hG x ∈ forcingQuotientEquiv U P R G hR hG y ↔ x ∈ y :=
  forcingQuotientValue_mem_iff U P R G hR hG x y

end TransitiveZF
end ZFVP
