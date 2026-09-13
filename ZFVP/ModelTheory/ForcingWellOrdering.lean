import ZFVP.ModelTheory.ForcingFunctionValues
import ZFVP.ModelTheory.ForcingModelRank
import ZFVP.SetTheory.WellOrderedSelection
import ZFVP.SetTheory.EndExtensionFinite

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem wellOrderable_of_check (S : ForcingContext V) (hP : IsWellOrderable S.P)
    {X : V} (hX : IsWellOrderable (S.check X)) : IsWellOrderable X := by
  obtain ⟨κ, hκ, g, hg, hginj⟩ := (wellOrderable_iff_cardLE_ordinal (S.check X)).mp hX
  have : IsOrdinal κ := hκ
  obtain ⟨α, hα, rfl⟩ := S.ordinal_eq_check κ
  have : IsOrdinal α := hα
  let f := converseGraph g
  have hfun : IsFunction f := IsFunction.of_mem (converseGraph_mem_function hg hginj)
  obtain ⟨τ, hτ⟩ := S.ofName_surjective f
  let Q : V → V → Prop := fun x z ↦
    ForcesCheckedFunctionValue S.P S.R S.one τ.val (kpair.π₁ z) (kpair.π₂ z) x
  have hQ : ℒₛₑₜ-relation Q := by unfold Q; definability
  apply wellOrderable_of_separating_relation (wellOrderable_prod hP (ordinal_wellOrderable α)) Q hQ
  · intro x hx
    have hx' : S.check x ∈ S.check X := (S.check_mem_iff _ _).mpr hx
    obtain ⟨a, ha, he⟩ := (S.mem_check_iff α (g ‘ (S.check x))).mp (function_value_mem hg hx')
    have hv : f ‘ (S.check a) = S.check x := by
      rw [← he]
      exact converseGraph_value_value hg hginj hx'
    have hh : IsFunction (S.ofName τ) ∧ (S.ofName τ) ‘ (S.check a) = S.check x := by
      rw [hτ]
      exact ⟨hfun, hv⟩
    obtain ⟨p, hpG, hp⟩ := (S.checkedFunctionValue_truth τ a x).mpr hh
    refine ⟨⟨p, a⟩ₖ, kpair_mem_iff.mpr ⟨S.generic.1.1 p hpG, ha⟩, ?_⟩
    simpa only [Q, kpair.π₁_kpair, kpair.π₂_kpair] using hp
  · intro x _ y _ z _ hx hy
    exact forcesCheckedFunctionValue_unique S.order S.top τ.property hx hy

theorem check_wellOrderable (S : ForcingContext V) {X : V} (hX : IsWellOrderable X) :
    IsWellOrderable (S.check X) := by
  obtain ⟨α, hα, hxα⟩ := (wellOrderable_iff_cardLE_ordinal X).mp hX
  exact (wellOrderable_iff_cardLE_ordinal (S.check X)).mpr
    ⟨S.check α, (S.check_ordinal_iff α).mpr hα, S.checkEmbedding.map_cardLE hxα⟩

theorem check_wellOrderable_iff (S : ForcingContext V) (hP : IsWellOrderable S.P) (X : V) :
    IsWellOrderable (S.check X) ↔ IsWellOrderable X :=
  ⟨S.wellOrderable_of_check hP, S.check_wellOrderable⟩

theorem internalChoice_of_model (S : ForcingContext V) (hP : IsWellOrderable S.P)
    (hAC : InternalChoice S.Model) : InternalChoice V := by
  apply internalChoice_of_all_wellOrderable
  intro X
  exact S.wellOrderable_of_check hP (wellOrderable_of_internalChoice hAC (S.check X))

theorem not_internalChoice_model (S : ForcingContext V) (hP : IsWellOrderable S.P)
    (hAC : ¬InternalChoice V) : ¬InternalChoice S.Model :=
  fun h ↦ hAC (S.internalChoice_of_model hP h)

theorem not_models_ac (S : ForcingContext V) (hP : IsWellOrderable S.P)
    (hAC : ¬V↓[ℒₛₑₜ] ⊧* 𝗔𝗖) : ¬S.Model↓[ℒₛₑₜ] ⊧* 𝗔𝗖 := by
  intro h
  exact hAC (models_ac_of_internalChoice
    (S.internalChoice_of_model hP (internalChoice_iff_models_ac.mpr h)))

end ForcingContext
end ZFVP
