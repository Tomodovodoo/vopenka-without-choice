import ZFVP.ModelTheory.ClassForcingProgressivePretameness
import ZFVP.ModelTheory.UsubaClassRestoration

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)

theorem usubaForcingTower_isPretame [Countable V]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ) :
    (T).IsPretame := by
  apply (T).isPretame_of_enumerations_and_closure
    (fun G hG ↦ usubaStageSetsHaveDCEnumerations hVP hG)
  intro G hG i K hi hK hiK α hα hDC
  exact usubaQuotient_closedThrough hiK ((T).stageFilter_generic hG i) hDC

/-- The actual Usuba class extension satisfies ZFC. Pretameness, quotient
closure, and eventual subset stabilization are all proved for this tower. -/
theorem usubaClassModel_models_zfc [Countable V]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    {G : Set V} (hG : IsGenericForDefinableDenseClasses (T).Condition (T).LE G) :
    ((T).ClassModel hG)↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖 :=
  usubaClassModel_models_zfc_of_pretame hVP (usubaForcingTower_isPretame hVP) hG

end ZFVP
