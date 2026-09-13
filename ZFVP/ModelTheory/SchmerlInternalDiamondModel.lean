import ZFVP.ModelTheory.SchmerlInternalDiamondGuesses
import ZFVP.ModelTheory.ForcingQuotientGeneric
import ZFVP.SetTheory.EndExtensionWellOrdering

/-! The actual quotient's generic union of diamond approximations. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def diamondContext (κ : V) (hzero : (∅ : V) ∈ κ) (G : Set V)
    (hG : IsExternalForcingGeneric (diamondConditions κ) (diamondOrder κ) G) : ForcingContext V :=
  ⟨diamondConditions κ, diamondOrder κ, ∅, G, (diamond_poset κ).1, diamond_top hzero, hG⟩

namespace DiamondModel

variable {κ : V} (hzero : (∅ : V) ∈ κ) {G : Set V}
  (hG : IsExternalForcingGeneric (diamondConditions κ) (diamondOrder κ) G)

noncomputable def genericSet : (diamondContext κ hzero G hG).Model :=
  forcingGenericSet _ _ G (diamond_poset κ).1 hG.1 ∅ (diamond_top hzero)

theorem mem_genericSet (x : (diamondContext κ hzero G hG).Model) :
    x ∈ genericSet hzero hG ↔ ∃ p ∈ G, x = (diamondContext κ hzero G hG).check p :=
  forcingGenericSet_mem_iff _ _ G (diamond_poset κ).1 hG ∅ (diamond_top hzero) x

noncomputable def genericSequence : (diamondContext κ hzero G hG).Model := ⋃ˢ genericSet hzero hG

theorem mem_genericSequence (x : (diamondContext κ hzero G hG).Model) :
    x ∈ genericSequence hzero hG ↔ ∃ p ∈ G, x ∈ (diamondContext κ hzero G hG).check p := by
  simp only [genericSequence, mem_sUnion_iff, mem_genericSet]
  constructor
  · rintro ⟨y, ⟨p, hp, rfl⟩, hx⟩
    exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨_, ⟨p, hp, rfl⟩, hx⟩

instance genericSequence_isFunction : IsFunction (genericSequence hzero hG) := by
  let F := diamondContext κ hzero G hG
  have hfun (p : V) (hp : p ∈ G) : IsFunction (F.check p) := by
    let : IsFunction p := diamondCondition_function (hG.1.1 p hp)
    exact F.check_isFunction p
  apply isFunction_sUnion
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := (mem_genericSet hzero hG p).mp hp
    exact hfun q hq
  · intro p hp q hq x y z hxy hxz
    obtain ⟨r, hr, rfl⟩ := (mem_genericSet hzero hG p).mp hp
    obtain ⟨s, hs, rfl⟩ := (mem_genericSet hzero hG q).mp hq
    obtain ⟨t, ht, htr, hts⟩ := hG.1.2.2.2 r hr s hs
    let : IsFunction (F.check t) := hfun t ht
    exact IsFunction.unique (f := F.check t)
      ((F.checkEmbedding.subset_iff r t).mpr ((pair_mem_reverseInclusionOrder _ _ _).mp htr).2.2 _ hxy)
      ((F.checkEmbedding.subset_iff s t).mpr ((pair_mem_reverseInclusionOrder _ _ _).mp hts).2.2 _ hxz)

theorem genericSequence_value {p i : V} (hp : p ∈ G) (hi : i ∈ domain p) :
    (genericSequence hzero hG) ‘ ((diamondContext κ hzero G hG).check i) =
      (diamondContext κ hzero G hG).check (p ‘ i) := by
  let F := diamondContext κ hzero G hG
  let : IsFunction p := diamondCondition_function (hG.1.1 p hp)
  apply value_eq_of_kpair_mem
  apply (mem_genericSequence hzero hG _).mpr
  refine ⟨p, hp, ?_⟩
  rw [← F.check_kpair, F.check_mem_iff]
  exact kpair_value_mem hi

theorem genericSequence_mem_function (hκ : IsRegularCardinal κ) (hω : (ω : V) ∈ κ) :
    genericSequence hzero hG ∈ (diamondContext κ hzero G hG).check (℘ κ) ^
      (diamondContext κ hzero G hG).check κ := by
  let F := diamondContext κ hzero G hG
  let : IsOrdinal κ := hκ.1.1
  apply mem_function.intro
  · intro z hz
    obtain ⟨p, hp, hzp⟩ := (mem_genericSequence hzero hG z).mp hz
    have hd := (mem_diamondConditions κ p).mp (hG.1.1 p hp)
    have hsub : p ⊆ κ ×ˢ ℘ κ := by
      intro u hu
      let : IsFunction p := diamondCondition_function (hG.1.1 p hp)
      obtain ⟨i, x, rfl⟩ := IsFunction.mem_eq_kpair hu
      exact kpair_mem_iff.mpr
        ⟨IsOrdinal.toIsTransitive.mem_trans (mem_domain_of_kpair_mem hu) hd.1,
          range_subset_of_mem_function hd.2.1 _ (mem_range_of_kpair_mem hu)⟩
    have hh := (F.checkEmbedding.subset_iff p (κ ×ˢ ℘ κ)).mpr hsub z hzp
    change z ∈ F.check (κ ×ˢ ℘ κ) at hh
    rwa [show F.check (κ ×ˢ ℘ κ) = F.check κ ×ˢ F.check (℘ κ) from F.checkEmbedding.map_prod _ _] at hh
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := (F.mem_check_iff κ x).mp hx
    obtain ⟨p, hpG, hpD⟩ := hG.2 _ (diamond_domain_dense hκ hω hi)
    have hip := (mem_sep_iff.mp hpD).2
    let : IsFunction p := diamondCondition_function (hG.1.1 p hpG)
    have hpair : ⟨F.check i, F.check (p ‘ i)⟩ₖ ∈ genericSequence hzero hG := by
      apply (mem_genericSequence hzero hG _).mpr
      refine ⟨p, hpG, ?_⟩
      rw [← F.check_kpair, F.check_mem_iff]
      exact kpair_value_mem hip
    exact ⟨F.check (p ‘ i), hpair, fun _ h ↦ IsFunction.unique h hpair⟩

theorem genericSequence_subset (hκ : IsRegularCardinal κ) (hω : (ω : V) ∈ κ)
    {α : (diamondContext κ hzero G hG).Model} (hα : α ∈ (diamondContext κ hzero G hG).check κ) :
    ((genericSequence hzero hG) ‘ α) ⊆ α := by
  let F := diamondContext κ hzero G hG
  obtain ⟨i, hi, rfl⟩ := (F.mem_check_iff κ α).mp hα
  obtain ⟨p, hpG, hpD⟩ := hG.2 _ (diamond_domain_dense hκ hω hi)
  have hip := (mem_sep_iff.mp hpD).2
  rw [genericSequence_value hzero hG hpG hip]
  exact (F.checkEmbedding.subset_iff _ _).mpr
    (((mem_diamondConditions κ p).mp (hG.1.1 p hpG)).2.2 i hip)

end DiamondModel
end ZFVP.Schmerl
