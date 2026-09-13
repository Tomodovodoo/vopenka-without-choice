import ZFVP.SetTheory.SourceQuantifierBound
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
@[simp] theorem sourceQuantifierCount_allItr {n} (k : ℕ) (φ : SetTheorySemisentence (n + k)) :
    sourceQuantifierCount (∀¹^[k] φ) = sourceQuantifierCount φ + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [allItr_succ, ih]
    change sourceQuantifierCount φ + 1 + k = sourceQuantifierCount φ + (k + 1)
    omega
@[simp] theorem sourceQuantifierCount_subst {n m} (φ : SetTheorySemisentence n)
    (ts : Fin n → SetTheorySemiterm Empty m) :
    sourceQuantifierCount (φ.subst ts) = sourceQuantifierCount φ := sourceQuantifierCount_rew φ _
theorem sourceQuantifierCount_le_nestFormulae {n m} (φ : SetTheorySemisentence n)
    (ψ : Fin n → SetTheorySemisentence (m + 1)) :
    sourceQuantifierCount φ ≤ sourceQuantifierCount (φ.nestFormulae ψ) := by
  rw [Semiformula.nestFormulae, sourceQuantifierCount_allItr]
  simp only [Semiformula.imp_eq, sourceQuantifierCount, sourceQuantifierCount_subst]
  omega
end ZFVP


