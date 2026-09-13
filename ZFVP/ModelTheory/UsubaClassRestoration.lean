import ZFVP.ModelTheory.UsubaEventualEnumeration
import ZFVP.ModelTheory.ClassForcingTowerChoice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)

theorem usubaClassModel_models_zfc_of_pretame [Countable V]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (hT : (T).IsPretame) {G : Set V}
    (hG : IsGenericForDefinableDenseClasses (T).Condition (T).LE G) :
    ((T).ClassModel hG)↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖 := by
  apply (T).classModel_models_zfc_of_enumerations hG hT (usubaStageSetsHaveDCEnumerations hVP hG)
  intro j k hj hk hjk α hα hDC
  exact usubaQuotient_closedThrough hjk ((T).stageFilter_generic hG j) hDC

end ZFVP
