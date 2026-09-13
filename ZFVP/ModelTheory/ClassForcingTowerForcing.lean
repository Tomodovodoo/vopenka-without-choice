import ZFVP.ModelTheory.ClassForcingTowerTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable V]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

/-- The definable forcing relation agrees with truth in every class generic
extension containing the specified condition. -/
theorem towerFormula_iff_all_generics {n : ℕ} (φ : SetTheorySemisentence n)
    (v : Fin n → T.Name) {p : V} (hp : T.Condition p) :
    T.towerFormula φ (standardTuple (fun i ↦ (v i).val)) p ↔
      ∀ (G : Set V) (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G),
        p ∈ G → φ.Evalb (T.classAssignment hG v) := by
  constructor
  · intro h G hG hpG
    exact (T.towerFormula_truth hG φ v).mpr ⟨p, hpG, h⟩
  · intro h
    by_contra hn
    obtain ⟨q, hq, hqp⟩ := T.classNegation_exists_of_not (T.towerFormula_regular φ v) hp hn
    obtain ⟨G, hG, hqG⟩ := T.exists_generic hq.1
    have hpG := hG.1.2.2.1 q hqG p hp hqp
    have ht := (T.towerFormula_truth hG φ v).mp (h G hG hpG)
    exact (T.classMeets_negation hG _ (by definability)
      (T.towerFormula_regular φ v).1 (T.towerFormula_regular φ v).2.1).mp ⟨q, hqG, hq⟩ ht

end DefinableForcingTower
end ZFVP
