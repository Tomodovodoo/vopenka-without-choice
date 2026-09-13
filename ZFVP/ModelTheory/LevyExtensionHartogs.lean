import ZFVP.ModelTheory.LevyGroundStages
import ZFVP.ModelTheory.GroundCoverGeneral
import ZFVP.ModelTheory.ForcingChoice
import ZFVP.ModelTheory.ForcingModelRank
import ZFVP.SetTheory.HartogsRegularChoice

/-! The Levy collapse of a measurable `κ` keeps the successor of `κ`. In the extension the Hartogs
number of `κ̌` is the check of the Hartogs number of `κ`, and that ordinal is a regular cardinal
of the extension above its `ω`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)
  {G : Set V} (hG : IsExternalForcingGeneric (levyCollapse κ) (levyOrder κ) G)

include hAC in
/-- Choice in the ground model gives choice in the Levy extension. -/
theorem levy_model_internalChoice : InternalChoice (levyContext κ hG).Model :=
  (levyContext κ hG).internalChoice_of_ground hAC

include hAC hU hc hω hκ in
/-- The Hartogs number of `κ̌` in the extension is the check of the Hartogs number of `κ`. Ordinals
of the extension are checks of ground ordinals, and the collapse has size at most `κ`, so it moves
no cardinality of the form `α ≤# κ`. -/
theorem levy_hartogs_check :
    hartogsNumber ((levyContext κ hG).check κ) = (levyContext κ hG).check (hartogsNumber κ) := by
  have hωκ : (ω : V) ⊆ κ := IsOrdinal.toIsTransitive.transitive _ hω
  have hP : (levyContext κ hG).P ≤# κ := levyCollapse_cardLE_self hAC hU hc hω hκ
  apply mem_ext
  intro z
  constructor
  · intro hz
    have hzord : IsOrdinal z := IsOrdinal.of_mem hz
    obtain ⟨α, hα, rfl⟩ := (levyContext κ hG).ordinal_eq_check z
    have hle : (levyContext κ hG).check α ≤# (levyContext κ hG).check κ :=
      cardLE_of_mem_hartogsNumber hz
    have hακ : α ≤# κ :=
      (levyContext κ hG).check_cardLE_of_cardLE_infinite hAC inferInstance hωκ hP hle
    exact ((levyContext κ hG).check_mem_iff α (hartogsNumber κ)).mpr
      (ordinal_cardLE_iff_mem_hartogsNumber.mp hακ)
  · intro hz
    obtain ⟨α, hα, rfl⟩ := ((levyContext κ hG).mem_check_iff _ _).mp hz
    have hαord : IsOrdinal α := IsOrdinal.of_mem hα
    have : IsOrdinal ((levyContext κ hG).check α) :=
      ((levyContext κ hG).check_ordinal_iff α).mpr hαord
    exact ordinal_cardLE_iff_mem_hartogsNumber.mp
      ((levyContext κ hG).checkEmbedding.map_cardLE (cardLE_of_mem_hartogsNumber hα))

include hAC hU hc hω hκ in
/-- `(κ⁺)ˇ` is a regular cardinal of the Levy extension. -/
theorem levy_check_hartogs_regular :
    IsRegularCardinal ((levyContext κ hG).check (hartogsNumber κ)) := by
  have hωκ : (ω : V) ⊆ κ := IsOrdinal.toIsTransitive.transitive _ hω
  have hωle : (ω : (levyContext κ hG).Model) ≤# (levyContext κ hG).check κ := by
    rw [← (levyContext κ hG).checkEmbedding.map_omega]
    exact (levyContext κ hG).checkEmbedding.map_cardLE (cardLE_of_subset hωκ)
  have h := hartogsNumber_regular (levy_model_internalChoice hAC hG) hωle
  rwa [levy_hartogs_check hAC hU hc hω hκ hG] at h

include hω in
/-- The extension's `ω` lies below `(κ⁺)ˇ`. -/
theorem levy_omega_mem_check_hartogs :
    (ω : (levyContext κ hG).Model) ∈ (levyContext κ hG).check (hartogsNumber κ) := by
  have hωκ : (ω : V) ⊆ κ := IsOrdinal.toIsTransitive.transitive _ hω
  rw [← (levyContext κ hG).checkEmbedding.map_omega]
  exact ((levyContext κ hG).check_mem_iff (ω : V) (hartogsNumber κ)).mpr
    (ordinal_cardLE_iff_mem_hartogsNumber.mp (cardLE_of_subset hωκ))

end

end ZFVP
