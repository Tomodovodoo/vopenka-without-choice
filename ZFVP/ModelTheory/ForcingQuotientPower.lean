import ZFVP.ModelTheory.ForcingQuotientBoundedNames
import ZFVP.SetTheory.ForcingPowerName

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingPower {P : V} (R : V) (τ : ForcingName P) : ForcingName P :=
  ⟨forcingPowerName P R τ.val, forcingPowerName_isName P R τ.val⟩

theorem forcingSubsetConditions_quotient_truth (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (ρ τ : ForcingName P) :
    GenericMeets G (forcingSubsetConditions P R ρ.val τ.val) ↔
      ∀ x : ForcingQuotient P R G hR hG.1,
        x ∈ forcingQuotientMk P R G hR hG.1 ρ → x ∈ forcingQuotientMk P R G hR hG.1 τ := by
  unfold IsExternalForcingGeneric at hG
  have hh := (forcingFormula_quotient_truth P R G hR hG isSubsetOf ![ρ, τ]).symm
  have ht : (fun i ↦ (![ρ, τ] i).val) = ![ρ.val, τ.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  rw [ht] at hh
  simpa [forcingSubsetConditions, isSubsetOf, Semiformula.Evalb, forcingQuotientAssignment] using hh

theorem forcingQuotient_powerName (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (τ : ForcingName P)
    (x : ForcingQuotient P R G hR hG.1) :
    x ∈ forcingQuotientMk P R G hR hG.1 (forcingPower R τ) ↔
      ∀ z, z ∈ x → z ∈ forcingQuotientMk P R G hR hG.1 τ := by
  unfold IsExternalForcingGeneric at hG
  constructor
  · intro hx
    obtain ⟨ξ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 x
    obtain ⟨ρ, p, hpG, hp, he⟩ := (forcingQuotientMk_mem_subname_iff P R G hR hG _ _).mp hx
    obtain ⟨_, _, _, hpF⟩ := (mem_forcingPowerName_iff _ _ _ _ _).mp hp
    rw [he]
    exact (forcingSubsetConditions_quotient_truth P R G hR hG ρ τ).mp ⟨p, hpG, hpF⟩
  · intro hx
    obtain ⟨ρ, hρ, rfl⟩ := forcingQuotient_boundedRepresentative P R G hR hG τ x hx
    obtain ⟨p, hpG, hpF⟩ := (forcingSubsetConditions_quotient_truth P R G hR hG ρ τ).mpr hx
    exact (forcingQuotientMk_mem_subname_iff P R G hR hG _ _).mpr
      ⟨ρ, p, hpG, (mem_forcingPowerName_iff _ _ _ _ _).mpr
        ⟨hρ, hG.1.1 p hpG, ρ.property, hpF⟩, rfl⟩

theorem forcingQuotient_power (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (a : ForcingQuotient P R G hR hG.1) :
    ∃ b : ForcingQuotient P R G hR hG.1, ∀ x, x ∈ b ↔ ∀ z, z ∈ x → z ∈ a := by
  unfold IsExternalForcingGeneric at hG
  obtain ⟨τ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 a
  exact ⟨forcingQuotientMk P R G hR hG.1 (forcingPower R τ),
    forcingQuotient_powerName P R G hR hG τ⟩

end ZFVP
