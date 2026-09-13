import ZFVP.ModelTheory.UsubaIterationUniform
import ZFVP.ModelTheory.UsubaForcesZFC
import ZFVP.ModelTheory.CountableZFTransfer
import ZFVP.SetTheory.LowenheimSkolemDictionary

/-! Ground-theory derivability for the actual Usuba class forcing.

Each standard ZFC axiom has one fixed forcing sentence. Its correctness
in countable grounds transfers to arbitrary grounds through a countable
elementary submodel, and first-order completeness gives a proof in ZF.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def properClassLSSentence : SetTheorySentence :=
  “∀ α, !IsOrdinal.dfn α → ∃ κ, α ∈ κ ∧ !lsCardinalFormula κ”

def usubaForcingSentence (φ : SetTheorySentence) : SetTheorySentence :=
  f“∀ p, !(usubaTowerDictionary.condition) p →
    !(usubaTowerDictionary.formulaDictionary.compile φ) (!isEmpty) p”

def usubaLSForcingSentence (φ : SetTheorySentence) : SetTheorySentence :=
  properClassLSSentence 🡒 usubaForcingSentence φ

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem eval_properClassLSSentence (v : Fin 0 → V) :
    properClassLSSentence.Evalb v ↔
      ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ := by
  simp [properClassLSSentence]

@[simp] theorem eval_usubaForcingSentence (φ : SetTheorySentence) (v : Fin 0 → V) :
    (usubaForcingSentence φ).Evalb v ↔
      ∀ p : V, (usubaForcingTower (V := V)).Condition p →
        (usubaForcingTower (V := V)).towerFormula φ
          (standardTuple (Fin.elim0 : Fin 0 → V)) p := by
  let := ClassForcingTowerDictionary.condition_defined (usubaTowerDictionary_defines (V := V))
  let := usubaForcingFormula_defined (V := V) φ
  simp [usubaForcingSentence, standardTuple]

theorem eval_usubaLSForcingSentence (φ : SetTheorySentence) (v : Fin 0 → V) :
    (usubaLSForcingSentence φ).Evalb v ↔
      ((∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ) →
        ∀ p : V, (usubaForcingTower (V := V)).Condition p →
          (usubaForcingTower (V := V)).towerFormula φ
            (standardTuple (Fin.elim0 : Fin 0 → V)) p) := by
  simp [usubaLSForcingSentence]

theorem usubaLSForcingSentence_valid (φ : SetTheorySentence) (hφ : φ ∈ 𝗭𝗙𝗖)
    (v : Fin 0 → V) : (usubaLSForcingSentence φ).Evalb v := by
  apply eval_of_countable_zf (usubaLSForcingSentence φ)
  intro W _ _ _ _ w
  apply (eval_usubaLSForcingSentence φ w).mpr
  intro hLS p hp
  exact usubaForcesZFC_of_ls hLS φ hφ hp

/-- Countability is absent: every condition of the actual tower forces every
standard ZFC axiom in any ZF ground with a proper class of LS cardinals. -/
theorem usubaForcesZFC_of_ls_unrestricted
    (hLS : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ)
    (φ : SetTheorySentence) (hφ : φ ∈ 𝗭𝗙𝗖) {p : V}
    (hp : (usubaForcingTower (V := V)).Condition p) :
    (usubaForcingTower (V := V)).towerFormula φ
      (standardTuple (Fin.elim0 : Fin 0 → V)) p :=
  (eval_usubaLSForcingSentence φ (![] : Fin 0 → V)).mp
    (usubaLSForcingSentence_valid φ hφ _) hLS p hp

theorem usubaForcesZFC_unrestricted
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    (φ : SetTheorySentence) (hφ : φ ∈ 𝗭𝗙𝗖) {p : V}
    (hp : (usubaForcingTower (V := V)).Condition p) :
    (usubaForcingTower (V := V)).towerFormula φ
      (standardTuple (Fin.elim0 : Fin 0 → V)) p := by
  apply usubaForcesZFC_of_ls_unrestricted ?_ φ hφ hp
  intro α hα
  let := hα
  exact vopenka_lsCardinal_unbounded hVP α

theorem models_usubaLSForcingSentence (φ : SetTheorySentence) (hφ : φ ∈ 𝗭𝗙𝗖) :
    V↓[ℒₛₑₜ] ⊧ usubaLSForcingSentence φ := by
  simpa only [models_iff, Semiformula.Realize, Semiformula.Evalb] using
    usubaLSForcingSentence_valid (V := V) φ hφ ![]

/-- ZF proves that the proper-class LS hypothesis implies the fixed forcing
translation of each standard ZFC axiom. -/
theorem zf_proves_usubaForcesZFC_of_ls (φ : SetTheorySentence) (hφ : φ ∈ 𝗭𝗙𝗖) :
    𝗭𝗙 ⊢ usubaLSForcingSentence φ :=
  provable_of_models 𝗭𝗙 (usubaLSForcingSentence φ)
    (fun (M : Type) _ _ _ ↦ models_usubaLSForcingSentence (V := M) φ hφ)

end ZFVP
