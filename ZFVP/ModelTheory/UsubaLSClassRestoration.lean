import ZFVP.ModelTheory.UsubaLSEventualEnumeration
import ZFVP.ModelTheory.ClassForcingProgressivePretameness
import ZFVP.ModelTheory.ClassForcingTowerChoice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)

theorem usubaForcingTower_isPretame_of_ls [Countable V]
    (hLS : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ) :
    (T).IsPretame := by
  apply (T).isPretame_of_enumerations_and_closure
    (fun G hG ↦ usubaStageSetsHaveDCEnumerations_of_ls hLS hG)
  intro G hG i K hi hK hiK α hα hDC
  exact usubaQuotient_closedThrough hiK ((T).stageFilter_generic hG i) hDC

/-- The actual Usuba class-forcing extension satisfies ZFC from an
unbounded class of LS cardinals in the ground model. -/
theorem usubaClassModel_models_zfc_of_ls [Countable V]
    (hLS : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ)
    {G : Set V} (hG : IsGenericForDefinableDenseClasses (T).Condition (T).LE G) :
    ((T).ClassModel hG)↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖 := by
  apply (T).classModel_models_zfc_of_enumerations hG (usubaForcingTower_isPretame_of_ls hLS)
    (usubaStageSetsHaveDCEnumerations_of_ls hLS hG)
  intro j k hj hk hjk α hα hDC
  exact usubaQuotient_closedThrough hjk ((T).stageFilter_generic hG j) hDC

theorem exists_usuba_zfc_class_extension_of_ls [Countable V]
    (hLS : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ)
    {p : V} (hp : (T).Condition p) :
    ∃ G : Set V, ∃ hG : IsGenericForDefinableDenseClasses (T).Condition (T).LE G,
      p ∈ G ∧ ((T).ClassModel hG)↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖 := by
  obtain ⟨G, hG, hpG⟩ := (T).exists_generic hp
  exact ⟨G, hG, hpG, usubaClassModel_models_zfc_of_ls hLS hG⟩

end ZFVP
