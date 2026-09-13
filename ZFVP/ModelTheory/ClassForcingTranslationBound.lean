import ZFVP.Syntax.ClassForcingTranslation
import ZFVP.SetTheory.FormulaStructuralHeight
import Mathlib.Tactic.Ring

/-! A scalar bound for the actual class-forcing translation. Logical height
counts the Boolean nodes where forcing inserts density quantifiers.
-/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace ClassForcingDictionary

theorem orStep_syntacticBound_le (d : ClassForcingDictionary) {K n : ℕ}
    (hP : levySyntacticBound d.carrier ≤ K) (hR : levySyntacticBound d.order ≤ K)
    (φ ψ : SetTheorySemisentence (n + 1)) :
    levySyntacticBound (d.orStep φ ψ) ≤
      max K (max (levySyntacticBound φ) (levySyntacticBound ψ)) + 4 := by
  simp only [orStep, levySyntacticBound, levySyntacticBound_rew, levySyntacticBound_neg]
  omega

theorem allStep_syntacticBound_le (d : ClassForcingDictionary) {K n : ℕ}
    (hP : levySyntacticBound d.carrier ≤ K) (hN : levySyntacticBound d.names ≤ K)
    (φ : SetTheorySemisentence (n + 1 + 1)) :
    levySyntacticBound (d.allStep φ) ≤ max K (levySyntacticBound φ) + 2 := by
  simp only [allStep, levySyntacticBound, levySyntacticBound_rew, levySyntacticBound_neg]
  omega

theorem exsStep_syntacticBound_le (d : ClassForcingDictionary) {K n : ℕ}
    (hP : levySyntacticBound d.carrier ≤ K) (hR : levySyntacticBound d.order ≤ K)
    (hN : levySyntacticBound d.names ≤ K) (φ : SetTheorySemisentence (n + 1 + 1)) :
    levySyntacticBound (d.exsStep φ) ≤ max K (levySyntacticBound φ) + 6 := by
  simp only [exsStep, levySyntacticBound, levySyntacticBound_rew, levySyntacticBound_neg]
  omega

private theorem coefficient_le (K s : ℕ) (hs : 1 ≤ s) : K ≤ K * s := by
  simpa using Nat.mul_le_mul_left K hs

/-- A linear context bound for atomic clauses gives a linear logical-height
bound for the full translation, in both polarities. -/
theorem translation_syntacticBound_le (d : ClassForcingDictionary) {K : ℕ}
    (hK : 6 ≤ K)
    (hP : levySyntacticBound d.carrier ≤ K) (hR : levySyntacticBound d.order ≤ K)
    (hN : levySyntacticBound d.names ≤ K)
    (hbase : ∀ {n a : ℕ} (r : Language.Set.Rel a) (ts : Fin a → SetTheorySemiterm Empty n),
      levySyntacticBound (d.base (.rel r ts)) ≤ K * (n + 1) ∧
      levySyntacticBound (d.base (.nrel r ts)) ≤ K * (n + 1))
    {n : ℕ} (φ : SetTheorySemisentence n) :
    levySyntacticBound (d.translation φ) ≤ K * (n + 2 * formulaStructuralHeight φ + 1) := by
  induction φ with
  | @verum n =>
    simpa only [translation, formulaStructuralHeight, Nat.mul_zero, Nat.add_zero,
      levySyntacticBound_rew] using hP.trans (coefficient_le K (n + 1) (by omega))
  | falsum => simp only [translation, levySyntacticBound]; omega
  | rel r ts => simpa only [translation, formulaStructuralHeight, Nat.mul_zero, Nat.add_zero]
      using (hbase r ts).1
  | nrel r ts => simpa only [translation, formulaStructuralHeight, Nat.mul_zero, Nat.add_zero]
      using (hbase r ts).2
  | and φ ψ ihφ ihψ =>
    simp only [translation, levySyntacticBound, formulaStructuralHeight]
    apply max_le
    · exact ihφ.trans (Nat.mul_le_mul_left K (by omega))
    · exact ihψ.trans (Nat.mul_le_mul_left K (by omega))
  | @or n φ ψ ihφ ihψ =>
    let m := max (formulaStructuralHeight φ) (formulaStructuralHeight ψ)
    let B := K * (n + 2 * m + 1)
    have hφ : levySyntacticBound (d.translation φ) ≤ B :=
      ihφ.trans (Nat.mul_le_mul_left K (by dsimp only [m]; omega))
    have hψ : levySyntacticBound (d.translation ψ) ≤ B :=
      ihψ.trans (Nat.mul_le_mul_left K (by dsimp only [m]; omega))
    have hKB : K ≤ B := coefficient_le _ _ (by omega)
    have hh := (d.orStep_syntacticBound_le hP hR (d.translation φ) (d.translation ψ)).trans
      (Nat.add_le_add_right (max_le hKB (max_le hφ hψ)) 4)
    change _ ≤ K * (n + 2 * (m + 1) + 1)
    calc
      _ ≤ B + 4 := hh
      _ ≤ B + 2 * K := Nat.add_le_add_left (by omega) B
      _ = _ := by dsimp only [B]; ring
  | @all n φ ih =>
    let B := K * (n + 1 + 2 * formulaStructuralHeight φ + 1)
    have hKB : K ≤ B := coefficient_le _ _ (by omega)
    have hh := (d.allStep_syntacticBound_le hP hN (d.translation φ)).trans
      (Nat.add_le_add_right (max_le hKB ih) 2)
    change _ ≤ K * (n + 2 * (formulaStructuralHeight φ + 1) + 1)
    calc
      _ ≤ B + 2 := hh
      _ ≤ B + K := Nat.add_le_add_left (by omega) B
      _ = _ := by dsimp only [B]; ring
  | @exs n φ ih =>
    let B := K * (n + 1 + 2 * formulaStructuralHeight φ + 1)
    have hKB : K ≤ B := coefficient_le _ _ (by omega)
    have hh := (d.exsStep_syntacticBound_le hP hR hN (d.translation φ)).trans
      (Nat.add_le_add_right (max_le hKB ih) 6)
    change _ ≤ K * (n + 2 * (formulaStructuralHeight φ + 1) + 1)
    calc
      _ ≤ B + 6 := hh
      _ ≤ B + K := Nat.add_le_add_left hK B
      _ = _ := by dsimp only [B]; ring

end ClassForcingDictionary
end ZFVP
