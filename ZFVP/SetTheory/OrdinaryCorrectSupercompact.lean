import ZFVP.SetTheory.CnExtendibleWoodinSupercompact
import ZFVP.SetTheory.CnExtendibleHighCriticalWoodin
import ZFVP.SetTheory.ChoicelessCorrectness

set_option maxRecDepth 10000

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

attribute [local irreducible] sigmaOneStarCorrectFormula woodinSupercompactWitnessFormula
  highCriticalWoodinWitnessFormula

/-- The two formulas fixed in V13, with both negations explicitly included. -/
@[irreducible] def ordinaryWoodinDictionary : SetFormulaDictionary :=
  [⟨1, sigmaOneStarCorrectFormula⟩, ⟨1, ∼sigmaOneStarCorrectFormula⟩,
   ⟨3, woodinSupercompactWitnessFormula⟩, ⟨3, ∼woodinSupercompactWitnessFormula⟩]

private def positiveDictionaryBound (D : SetFormulaDictionary) :
    {n : ℕ // n = levyDictionaryBound D + 1 ∧ 1 ≤ n ∧
      ∀ φ ∈ D, levySyntacticBound φ.2 < n} :=
  ⟨levyDictionaryBound D + 1, rfl, Nat.succ_le_succ (Nat.zero_le _),
    fun φ hφ ↦ Nat.lt_succ_of_le (levySyntacticBound_le_dictionaryBound D φ hφ)⟩

/-- Seal the computed numeral to avoid reducing the expanded formula repeatedly.
The checked package retains its exact syntactic computation equation. -/
opaque ordinaryWoodinBoundData :
    {n : ℕ // n = levyDictionaryBound ordinaryWoodinDictionary + 1 ∧ 1 ≤ n ∧
      ∀ φ ∈ ordinaryWoodinDictionary, levySyntacticBound φ.2 < n} :=
  positiveDictionaryBound ordinaryWoodinDictionary

def ordinaryWoodinBound : ℕ := ordinaryWoodinBoundData.val

theorem ordinaryWoodinBound_computed :
    ordinaryWoodinBound = levyDictionaryBound ordinaryWoodinDictionary + 1 :=
  ordinaryWoodinBoundData.property.1

theorem ordinaryWoodinBound_positive : 1 ≤ ordinaryWoodinBound :=
  ordinaryWoodinBoundData.property.2.1

theorem ordinaryWoodinDictionary_bound {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : ⟨n, φ⟩ ∈ ordinaryWoodinDictionary) :
    levySyntacticBound φ < ordinaryWoodinBound :=
  ordinaryWoodinBoundData.property.2.2 _ hφ

theorem ordinaryWoodinDictionary_complexity {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : ⟨n, φ⟩ ∈ ordinaryWoodinDictionary) (p : LevyPolarity) :
    IsLevyFormula p ordinaryWoodinBound φ :=
  (isLevyFormula_syntacticBound φ p).mono (Nat.le_of_lt (ordinaryWoodinDictionary_bound hφ))

theorem ordinaryWoodinWitness_complexity (p : LevyPolarity) :
    IsLevyFormula p ordinaryWoodinBound woodinSupercompactWitnessFormula := by
  apply ordinaryWoodinDictionary_complexity
  unfold ordinaryWoodinDictionary
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem ordinaryWoodinStar_complexity (p : LevyPolarity) :
    IsLevyFormula p ordinaryWoodinBound sigmaOneStarCorrectFormula := by
  apply ordinaryWoodinDictionary_complexity
  unfold ordinaryWoodinDictionary
  exact List.mem_cons_self

theorem ordinaryWoodinStar_neg_complexity (p : LevyPolarity) :
    IsLevyFormula p ordinaryWoodinBound (∼sigmaOneStarCorrectFormula) := by
  apply ordinaryWoodinDictionary_complexity
  unfold ordinaryWoodinDictionary
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem ordinaryWoodinWitness_neg_complexity (p : LevyPolarity) :
    IsLevyFormula p ordinaryWoodinBound (∼woodinSupercompactWitnessFormula) := by
  apply ordinaryWoodinDictionary_complexity
  unfold ordinaryWoodinDictionary
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local irreducible] ordinaryWoodinBound

/-- The positive levels used by the paper's UE scheme gain two correctness levels. -/
theorem IsCnExtendible.correct_add_two {s : ℕ} {κ : V}
    (hs : 1 ≤ s) (hκ : IsCnExtendible s κ) : Cn (s + 2) κ := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  exact hκ.cn

/-- V13's one bound works at every larger level. Reflection uses the entire
small-embedding witness, so its source correctness is returned to the ground. -/
theorem IsCnExtendible.woodinSupercompact_of_bound {s : ℕ} {κ : V}
    (hs : ordinaryWoodinBound ≤ s) (hκ : IsCnExtendible s κ) :
    IsWoodinSupercompact κ := by
  have hpos := Nat.le_trans ordinaryWoodinBound_positive hs
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  exact hκ.woodinSupercompact_of_complexity ((ordinaryWoodinWitness_complexity .sigma).mono hs)

theorem ordinary_correct_supercompact {s : ℕ} {κ : V}
    (hs : ordinaryWoodinBound ≤ s) (hκ : IsCnExtendible s κ) :
    Cn (s + 2) κ ∧ IsWoodinSupercompact κ :=
  ⟨hκ.correct_add_two (Nat.le_trans ordinaryWoodinBound_positive hs),
    hκ.woodinSupercompact_of_bound hs⟩

/-- The optional high-critical version has its own explicit uniform threshold. -/
theorem IsCnExtendible.highCriticalWoodin_of_bound {s : ℕ} {κ : V}
    (hs : highCriticalWoodinBound ≤ s) (hκ : IsCnExtendible s κ) :
    HasHighCriticalWoodinWitnesses κ := by
  have hpos : 1 ≤ s := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) hs
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  exact hκ.highCriticalWoodin_of_complexity (highCriticalWoodinWitness_complexity.mono hs)

end ZFVP
