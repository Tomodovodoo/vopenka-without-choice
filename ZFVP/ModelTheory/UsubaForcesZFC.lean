import ZFVP.ModelTheory.UsubaPretameness
import ZFVP.ModelTheory.UsubaLSClassRestoration
import ZFVP.ModelTheory.ClassForcingTowerForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable V]

namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

/-- A sentence true in every actual generic extension is forced by every
condition, using the already constructed definable forcing relation. -/
theorem towerSentence_of_all_generic_models (φ : Sentence ℒₛₑₜ)
    (hφ : ∀ (G : Set V) (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G),
      (T.ClassModel hG)↓[ℒₛₑₜ] ⊧ φ) {p : V} (hp : T.Condition p) :
    T.towerFormula φ (standardTuple (Fin.elim0 : Fin 0 → V)) p := by
  apply (T.towerFormula_iff_all_generics φ (Fin.elim0 : Fin 0 → T.Name) hp).mpr
  intro G hG _
  have h := hφ G hG
  have he : T.classAssignment hG (Fin.elim0 : Fin 0 → T.Name) = ![] := Subsingleton.elim _ _
  rw [he]
  simpa [models_iff, Semiformula.Realize, Semiformula.Evalb] using h

end DefinableForcingTower

/-- Every ZFC axiom is forced by every condition of the actual Usuba tower.
This is a theorem about the definable forcing relation over a countable ground;
a uniform ground-theory derivability statement is a separate obligation. -/
theorem usubaForcesZFC
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    (φ : Sentence ℒₛₑₜ) (hφ : φ ∈ 𝗭𝗙𝗖) {p : V}
    (hp : (usubaForcingTower (V := V)).Condition p) :
    (usubaForcingTower (V := V)).towerFormula φ
      (standardTuple (Fin.elim0 : Fin 0 → V)) p := by
  apply (usubaForcingTower (V := V)).towerSentence_of_all_generic_models φ ?_ hp
  intro G hG
  let := usubaClassModel_models_zfc hVP hG
  exact Theory.models ((usubaForcingTower (V := V)).ClassModel hG) 𝗭𝗙𝗖 hφ

/-- The same forcing assertion uses only unbounded LS cardinals in the ground. -/
theorem usubaForcesZFC_of_ls
    (hLS : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ)
    (φ : Sentence ℒₛₑₜ) (hφ : φ ∈ 𝗭𝗙𝗖) {p : V}
    (hp : (usubaForcingTower (V := V)).Condition p) :
    (usubaForcingTower (V := V)).towerFormula φ
      (standardTuple (Fin.elim0 : Fin 0 → V)) p := by
  apply (usubaForcingTower (V := V)).towerSentence_of_all_generic_models φ ?_ hp
  intro G hG
  let := usubaClassModel_models_zfc_of_ls hLS hG
  exact Theory.models ((usubaForcingTower (V := V)).ClassModel hG) 𝗭𝗙𝗖 hφ

end ZFVP
