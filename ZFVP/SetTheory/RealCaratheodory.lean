import ZFVP.SetTheory.RealOuterMeasureSubadditive

/-! The full Carathéodory test-set criterion for actual internal real sets. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def isRealLebesgueMeasurableFormula : SetTheorySemisentence 1 :=
  f“A. A ⊆ !dedekindRealsFormula ∧ ∀ T, T ⊆ !dedekindRealsFormula →
    !realOuterMeasureFormula T = !extendedRealAddFormula
      (!realOuterMeasureFormula (!inter.dfn T A)) (!realOuterMeasureFormula (!sdiff.dfn T A))”

def realLebesgueMeasurableSentence : SetTheorySentence :=
  f“∀ A, A ⊆ !dedekindRealsFormula → !isRealLebesgueMeasurableFormula A”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsRealLebesgueMeasurable (A : V) : Prop := A ⊆ dedekindReals V ∧
  ∀ T, T ⊆ dedekindReals V → realOuterMeasure T =
    extendedRealAdd (realOuterMeasure (T ∩ A)) (realOuterMeasure (T \ A))

instance isRealLebesgueMeasurableFormula_defined :
    ℒₛₑₜ-predicate[V] IsRealLebesgueMeasurable via isRealLebesgueMeasurableFormula :=
  ⟨fun v ↦ by simp [isRealLebesgueMeasurableFormula, IsRealLebesgueMeasurable]⟩

instance isRealLebesgueMeasurable_definable : ℒₛₑₜ-predicate[V] IsRealLebesgueMeasurable :=
  isRealLebesgueMeasurableFormula_defined.to_definable

def AllRealLebesgueMeasurable (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : Prop :=
  ∀ A : V, A ⊆ dedekindReals V → IsRealLebesgueMeasurable A

instance realLebesgueMeasurableSentence_defined :
    Defined (fun _ : Fin 0 → V ↦ AllRealLebesgueMeasurable V) realLebesgueMeasurableSentence :=
  ⟨fun v ↦ by simp [realLebesgueMeasurableSentence, AllRealLebesgueMeasurable]⟩

theorem realOuterMeasure_split_le (T A : V) :
    realOuterMeasure T ⊆ extendedRealAdd (realOuterMeasure (T ∩ A)) (realOuterMeasure (T \ A)) := by
  have h := realOuterMeasure_union_le (T ∩ A) (T \ A)
  have he : (T ∩ A) ∪ (T \ A) = T := by
    apply mem_ext
    intro x
    simp only [mem_union_iff, mem_inter_iff, mem_sdiff_iff]
    tauto
  rwa [he] at h

theorem realLebesgueMeasurable_of_split_ge {A : V} (hA : A ⊆ dedekindReals V)
    (h : ∀ T, T ⊆ dedekindReals V →
      extendedRealAdd (realOuterMeasure (T ∩ A)) (realOuterMeasure (T \ A)) ⊆ realOuterMeasure T) :
    IsRealLebesgueMeasurable A :=
  ⟨hA, fun T hT ↦ subset_antisymm (realOuterMeasure_split_le T A) (h T hT)⟩

theorem realNull_lebesgueMeasurable {A : V} (hA : IsRealNull A) : IsRealLebesgueMeasurable A := by
  apply realLebesgueMeasurable_of_split_ge (realNull_subset_reals hA)
  intro T _hT
  have hnull : IsRealNull (T ∩ A) := realNull_subset hA (fun _ h ↦ (mem_inter_iff.mp h).2)
  rw [realNull_outerMeasure_zero hnull, extendedRealAdd_zero_left (realOuterMeasure_extended (T \ A))]
  exact realOuterMeasure_mono (fun _ h ↦ (mem_sdiff_iff.mp h).1)

theorem realNull_union {A B : V} (hA : IsRealNull A) (hB : IsRealNull B) : IsRealNull (A ∪ B) := by
  apply realNull_of_outerMeasure_zero
  apply subset_antisymm ?_ (realOuterMeasure_extended (A ∪ B)).2.1
  have h := realOuterMeasure_union_le A B
  rw [realNull_outerMeasure_zero hA, extendedRealAdd_zero_left (realOuterMeasure_extended B),
    realNull_outerMeasure_zero hB] at h
  exact h

end ZFVP
