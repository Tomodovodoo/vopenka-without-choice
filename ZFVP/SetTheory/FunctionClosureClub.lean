import ZFVP.SetTheory.DiagonalClubs
import ZFVP.SetTheory.HartogsRegularChoice
import ZFVP.SetTheory.CountableSets
import ZFVP.SetTheory.TransfiniteIteration

/-! Actual internal clubs of nonzero limit ordinals closed under an internal
function, including the first uncountable ordinal under internal choice. -/

set_option autoImplicit false

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem functionClosureCondition_definable (f : V) :
    ℒₛₑₜ-predicate[V] (fun α ↦ IsLimitOrdinal α ∧ ∀ β ∈ α, f ‘ β ∈ α) := by
  unfold IsLimitOrdinal
  definability

noncomputable def functionClosureClub (κ f : V) : V :=
  sep κ (fun α ↦ IsLimitOrdinal α ∧ ∀ β ∈ α, f ‘ β ∈ α) (functionClosureCondition_definable f)

theorem mem_functionClosureClub (κ f α : V) : α ∈ functionClosureClub κ f ↔
    α ∈ κ ∧ IsLimitOrdinal α ∧ ∀ β ∈ α, f ‘ β ∈ α := mem_sep_iff

instance functionClosureClub_definable : ℒₛₑₜ-function₂[V] functionClosureClub := by
  have hh : ℒₛₑₜ-relation₃[V] (fun E κ f ↦ ∀ α,
      α ∈ E ↔ α ∈ κ ∧ IsLimitOrdinal α ∧ ∀ β ∈ α, f ‘ β ∈ α) := by
    unfold IsLimitOrdinal
    definability
  apply Language.Definable.of_iff hh
  intro v
  rw [mem_ext_iff]
  simp only [mem_functionClosureClub]
  rfl

theorem functionClosureClub_club {κ f : V} (hκ : IsRegularCardinal κ)
    (hω : (ω : V) ∈ κ) (hf : f ∈ κ ^ κ) : IsClubIn (functionClosureClub κ f) κ := by
  let : IsOrdinal κ := hκ.1.1
  have hsub : functionClosureClub κ f ⊆ κ := fun _ hx ↦ (mem_functionClosureClub _ _ _).mp hx |>.1
  refine ⟨⟨hsub, ?_⟩, ⟨hsub, ?_⟩⟩
  · intro δ hδ hne hcof
    let : IsOrdinal δ := IsOrdinal.of_mem hδ
    have hlim : IsLimitOrdinal δ := by
      refine ⟨inferInstance, hne, ?_⟩
      rintro ⟨ξ, hδξ⟩
      have hξδ : ξ ∈ δ := hδξ.symm ▸ mem_succ_self ξ
      obtain ⟨η, _, hηδ, hξη⟩ := hcof ξ hξδ
      rw [hδξ] at hηδ
      rcases mem_succ_iff.mp hηδ with rfl | hηξ
      · exact mem_irrefl _ hξη
      · exact mem_asymm hξη hηξ
    refine (mem_functionClosureClub _ _ _).mpr ⟨hδ, hlim, ?_⟩
    intro β hβ
    obtain ⟨η, hη, hηδ, hβη⟩ := hcof β hβ
    exact IsOrdinal.toIsTransitive.mem_trans (((mem_functionClosureClub _ _ _).mp hη).2.2 β hβη) hηδ
  · let Q : V → V := fun β ↦ ordinalTail κ (f ‘ β ∪ succ β)
    have hQ : ℒₛₑₜ-function₁ Q := by
      have hh : ℒₛₑₜ-relation[V] (fun S β ↦ ∀ α, α ∈ S ↔ α ∈ κ ∧ f ‘ β ∪ succ β ∈ α) := by definability
      apply Language.Definable.of_iff hh
      intro v
      rw [mem_ext_iff]
      simp only [Q, ordinalTail, mem_sep_iff]
      rfl
    let C := definableGraph κ Q hQ
    have hC : ∀ β ∈ κ, IsClubIn (C ‘ β) κ := by
      intro β hβ
      rw [value_definableGraph _ _ _ hβ]
      exact ordinalTail_club hκ (ordinal_union_mem (function_value_mem hf hβ) (regularCardinal_succ_closed hκ hβ))
    have hdiag := diagonalClubIntersection_club hκ hω hC
    intro ξ hξ
    obtain ⟨α, hαdiag, hξα⟩ := hdiag.2.2 ξ hξ
    obtain ⟨hα, hαC⟩ := mem_sep_iff.mp hαdiag
    let : IsOrdinal α := IsOrdinal.of_mem hα
    have hclosed (β : V) (hβα : β ∈ α) : f ‘ β ∈ α ∧ succ β ∈ α := by
      have hβκ := IsOrdinal.toIsTransitive.mem_trans hβα hα
      have hαQ := hαC β hβα
      rw [show C ‘ β = Q β from value_definableGraph _ _ _ hβκ] at hαQ
      have hbound := (mem_sep_iff.mp hαQ).2
      let : IsOrdinal β := IsOrdinal.of_mem hβκ
      let : IsOrdinal (f ‘ β) := IsOrdinal.of_mem (function_value_mem hf hβκ)
      let : IsOrdinal (succ β) := inferInstance
      let : IsOrdinal (f ‘ β ∪ succ β) := IsOrdinal.of_mem
        (ordinal_union_mem (function_value_mem hf hβκ) (regularCardinal_succ_closed hκ hβκ))
      exact ⟨ordinal_mem_of_subset_mem (subset_union_left _ _) hbound,
        ordinal_mem_of_subset_mem (subset_union_right _ _) hbound⟩
    have hlim : IsLimitOrdinal α := by
      refine ⟨inferInstance, fun he ↦ not_mem_empty (he ▸ hξα), ?_⟩
      rintro ⟨β, he⟩
      have hb : β ∈ α := he.symm ▸ mem_succ_self β
      exact mem_irrefl α (he.symm ▸ (hclosed β hb).2)
    exact ⟨α, (mem_functionClosureClub _ _ _).mpr ⟨hα, hlim, fun β hβ ↦ (hclosed β hβ).1⟩, hξα⟩

theorem hartogsOmega_functionClosureClub (hAC : InternalChoice V) {f : V}
    (hf : f ∈ hartogsNumber (ω : V) ^ hartogsNumber (ω : V)) :
    IsClubIn (functionClosureClub (hartogsNumber (ω : V)) f) (hartogsNumber (ω : V)) :=
  functionClosureClub_club (hartogsNumber_regular hAC (CardLE.refl _)) omega_mem_hartogs_omega hf

end ZFVP
