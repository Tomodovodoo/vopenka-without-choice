import ZFVP.SetTheory.FunctionClosureClub
import ZFVP.ModelTheory.SchmerlInternalCodedChainUnion

/-! The actual internal club on which a continuous countable carrier chain
agrees with its ordinal labels. -/

set_option autoImplicit false

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem hartogsOmega_countable_sUnion_mem (hAC : InternalChoice V) {A : V}
    (hA : IsInternallyCountable A) (hsub : A ⊆ hartogsNumber (ω : V)) :
    ⋃ˢ A ∈ hartogsNumber (ω : V) := by
  let g := definableGraph A (fun x : V ↦ x) (by definability)
  have hsmall : ∀ x ∈ A, g ‘ x ≤# (ω : V) := by
    intro x hx
    rw [value_definableGraph _ _ _ hx]
    exact countable_of_mem_hartogs_omega (hsub x hx)
  have hr : range g = A := by
    rw [range_definableGraph]
    ext x
    simp only [repl_spec]
    exact ⟨fun ⟨y, hy, he⟩ ↦ he ▸ hy, fun hx ↦ ⟨x, hx, rfl⟩⟩
  have hc : IsInternallyCountable (⋃ˢ A) := by
    have hh := (sUnion_range_cardLE_prod hAC (domain_definableGraph _ _ _) hsmall).trans
      ((prod_cardLE_prod hA internallyCountable_omega).trans omega_prod_cardLE_omega)
    change ⋃ˢ range g ≤# (ω : V) at hh
    rwa [hr] at hh
  let : IsOrdinal (⋃ˢ A) := IsOrdinal.sUnion (fun x hx ↦ IsOrdinal.of_mem (hsub x hx))
  exact ordinal_cardLE_iff_mem_hartogsNumber.mp hc

theorem hartogsOmega_countable_strict_bound (hAC : InternalChoice V) {A : V}
    (hA : IsInternallyCountable A) (hsub : A ⊆ hartogsNumber (ω : V)) :
    succ (⋃ˢ A) ∈ hartogsNumber (ω : V) ∧ ∀ x ∈ A, x ∈ succ (⋃ˢ A) := by
  have hu := hartogsOmega_countable_sUnion_mem hAC hA hsub
  refine ⟨hartogsNumber_succ_mem (CardLE.refl _) hu, ?_⟩
  intro x hx
  let : IsOrdinal x := IsOrdinal.of_mem (hsub x hx)
  let : IsOrdinal (⋃ˢ A) := IsOrdinal.of_mem hu
  exact mem_succ_iff.mpr (IsOrdinal.subset_iff.mp (subset_sUnion_of_mem hx))

namespace Schmerl

theorem exists_codedCarrierAgreementClub (hAC : InternalChoice V) {C : V}
    (hcount : ∀ β ∈ hartogsNumber (ω : V), IsInternallyCountable (structureDomain (C ‘ β)))
    (hsub : ∀ β ∈ hartogsNumber (ω : V), structureDomain (C ‘ β) ⊆ hartogsNumber (ω : V))
    (hinc : ∀ β ∈ hartogsNumber (ω : V), ∀ γ ∈ hartogsNumber (ω : V), β ⊆ γ →
      structureDomain (C ‘ β) ⊆ structureDomain (C ‘ γ))
    (hcont : ∀ α ∈ hartogsNumber (ω : V), IsLimitOrdinal α → ∀ x,
      x ∈ structureDomain (C ‘ α) ↔ ∃ β ∈ α, x ∈ structureDomain (C ‘ β))
    (hcover : ∀ β ∈ hartogsNumber (ω : V), β ∈ structureDomain (C ‘ (succ β))) :
    ∃ E : V, IsClubIn E (hartogsNumber (ω : V)) ∧
      ∀ α ∈ E, IsLimitOrdinal α ∧ structureDomain (C ‘ α) = α := by
  let κ := hartogsNumber (ω : V)
  let f := definableGraph κ (fun β ↦ succ (⋃ˢ structureDomain (C ‘ β))) (by definability)
  have hf : f ∈ κ ^ κ := definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun β hβ ↦ (hartogsOmega_countable_strict_bound hAC (hcount β hβ) (hsub β hβ)).1)
  have hbound (β : V) (hβ : β ∈ κ) : ∀ x ∈ structureDomain (C ‘ β), x ∈ f ‘ β := by
    rw [show f ‘ β = succ (⋃ˢ structureDomain (C ‘ β)) from value_definableGraph _ _ _ hβ]
    exact (hartogsOmega_countable_strict_bound hAC (hcount β hβ) (hsub β hβ)).2
  refine ⟨functionClosureClub κ f, hartogsOmega_functionClosureClub hAC hf, ?_⟩
  intro α hαE
  obtain ⟨hακ, hαlim, hclosed⟩ := (mem_functionClosureClub _ _ _).mp hαE
  let : IsOrdinal α := hαlim.1
  have hsucc (β : V) (hβα : β ∈ α) : succ β ∈ α := by
    let : IsOrdinal β := IsOrdinal.of_mem hβα
    rcases IsOrdinal.mem_trichotomy (succ β) α with hs | he | hs
    · exact hs
    · exact False.elim (hαlim.2.2 ⟨β, he.symm⟩)
    · rcases mem_succ_iff.mp hs with he | hs
      · exact False.elim (mem_irrefl α (he ▸ hβα))
      · exact False.elim (mem_asymm hβα hs)
  refine ⟨hαlim, SetTheory.subset_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨β, hβα, hxβ⟩ := (hcont α hακ hαlim x).mp hx
    have hβκ : β ∈ κ := IsOrdinal.toIsTransitive.mem_trans hβα hακ
    exact IsOrdinal.toIsTransitive.mem_trans (hbound β hβκ x hxβ) (hclosed β hβα)
  · intro β hβα
    have hβκ : β ∈ κ := IsOrdinal.toIsTransitive.mem_trans hβα hακ
    have hsβα := hsucc β hβα
    have hsβκ : succ β ∈ κ := IsOrdinal.toIsTransitive.mem_trans hsβα hακ
    exact hinc (succ β) hsβκ α hακ (IsOrdinal.toIsTransitive.transitive _ hsβα) β (hcover β hβκ)

end Schmerl
end ZFVP
