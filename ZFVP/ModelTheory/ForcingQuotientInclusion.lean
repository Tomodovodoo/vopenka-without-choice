import ZFVP.ModelTheory.ExternalGenericRestriction
import ZFVP.SetTheory.MembershipEndExtension

/-! The forcing quotient of a transitive ground submodel includes in the ambient quotient. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (P R : SetDomain U) (G : Set V) (hR : IsForcingPreorder P.val R.val)
variable (hG : IsExternalForcingGeneric P.val R.val G)

abbrev RestrictedForcingQuotient := ForcingQuotient P R {p : SetDomain U | p.val ∈ G}
  ((forcingPreorder_iff U P R).mpr hR) (externalForcingGeneric_restrict U P R hG).1

def ambientForcingName (σ : ForcingName P) : ForcingName P.val :=
  ⟨σ.val.val, (forcingName_iff U P σ.val).mp σ.property⟩

noncomputable def forcingQuotientInclusion :
    RestrictedForcingQuotient U P R G hR hG → ForcingQuotient P.val R.val G hR hG.1 :=
  Quotient.lift (fun σ ↦ forcingQuotientMk P.val R.val G hR hG.1 (ambientForcingName U P σ))
    (fun σ τ he ↦ (forcingQuotientMk_eq_iff P.val R.val G hR hG.1 _ _).mpr
      ((genericMeets_atomicEquality_restrict_iff U P R σ.val τ.val G).mp he))

theorem forcingQuotientInclusion_mk (σ : ForcingName P) :
    forcingQuotientInclusion U P R G hR hG (forcingQuotientMk P R _ _ _ σ) =
      forcingQuotientMk P.val R.val G hR hG.1 (ambientForcingName U P σ) := rfl

theorem forcingQuotientInclusion_injective :
    Function.Injective (forcingQuotientInclusion U P R G hR hG) := by
  intro x y he
  obtain ⟨σ, rfl⟩ := forcingQuotientMk_surjective P R _ _ _ x
  obtain ⟨τ, rfl⟩ := forcingQuotientMk_surjective P R _ _ _ y
  have hh := (forcingQuotientMk_eq_iff P.val R.val G hR hG.1 _ _).mp he
  exact (forcingQuotientMk_eq_iff P R _ _ _ _ _).mpr
    ((genericMeets_atomicEquality_restrict_iff U P R σ.val τ.val G).mpr hh)

theorem forcingQuotientInclusion_mem_iff (x y : RestrictedForcingQuotient U P R G hR hG) :
    forcingQuotientInclusion U P R G hR hG x ∈ forcingQuotientInclusion U P R G hR hG y ↔ x ∈ y := by
  obtain ⟨σ, rfl⟩ := forcingQuotientMk_surjective P R _ _ _ x
  obtain ⟨τ, rfl⟩ := forcingQuotientMk_surjective P R _ _ _ y
  exact (genericMeets_atomicMembership_restrict_iff U P R σ.val τ.val G).symm

theorem forcingQuotientInclusion_endExtension (x : RestrictedForcingQuotient U P R G hR hG)
    (y : ForcingQuotient P.val R.val G hR hG.1)
    (hy : y ∈ forcingQuotientInclusion U P R G hR hG x) :
    ∃ z, z ∈ x ∧ y = forcingQuotientInclusion U P R G hR hG z := by
  obtain ⟨τ, rfl⟩ := forcingQuotientMk_surjective P R _ _ _ x
  obtain ⟨σ, rfl⟩ := forcingQuotientMk_surjective P.val R.val G hR hG.1 y
  obtain ⟨ν, p, _, hp, he⟩ := (forcingQuotientMk_mem_subname_iff P.val R.val G hR hG _ _).mp hy
  have hpairU := (inferInstance : IsTransitive U).mem_trans hp τ.val.property
  have hνU := (kpair_components_mem_transitive hpairU).1
  let ν' : SetDomain U := ⟨ν.val, hνU⟩
  let νN : ForcingName P := ⟨ν', (forcingName_iff U P ν').mpr ν.property⟩
  let z : RestrictedForcingQuotient U P R G hR hG := forcingQuotientMk P R _ _ _ νN
  have hz : forcingQuotientMk P.val R.val G hR hG.1 σ = forcingQuotientInclusion U P R G hR hG z := he
  refine ⟨z, ?_, hz⟩
  apply (forcingQuotientInclusion_mem_iff U P R G hR hG z _).mp
  exact hz ▸ hy

noncomputable def forcingQuotientEndExtension : MembershipEndExtension
    (RestrictedForcingQuotient U P R G hR hG) (ForcingQuotient P.val R.val G hR hG.1) where
  toFun := forcingQuotientInclusion U P R G hR hG
  injective := forcingQuotientInclusion_injective U P R G hR hG
  mem_iff := forcingQuotientInclusion_mem_iff U P R G hR hG
  endExtension := forcingQuotientInclusion_endExtension U P R G hR hG

end TransitiveZF
end ZFVP
