import ZFVP.SetTheory.RealCaratheodory

/-! Finite algebra closure of the full real Carathéodory criterion. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem realLebesgueMeasurable_complement {A : V} (hA : IsRealLebesgueMeasurable A) :
    IsRealLebesgueMeasurable ((dedekindReals V) \ A) := by
  refine ⟨fun _ h ↦ (mem_sdiff_iff.mp h).1, ?_⟩
  intro T hT
  have hleft : T ∩ ((dedekindReals V) \ A) = T \ A := by
    apply mem_ext
    intro x
    simp only [mem_inter_iff, mem_sdiff_iff]
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hT x h.1, h.2⟩⟩
  have hright : T \ ((dedekindReals V) \ A) = T ∩ A := by
    apply mem_ext
    intro x
    simp only [mem_inter_iff, mem_sdiff_iff]
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨hx, by_contra (fun hn ↦ h ⟨hT x hx, hn⟩)⟩
    · rintro ⟨hx, ha⟩
      exact ⟨hx, fun h ↦ h.2 ha⟩
  rw [hleft, hright, extendedRealAdd_comm (realOuterMeasure_extended (T \ A)).1
    (realOuterMeasure_extended (T ∩ A)).1]
  exact hA.2 T hT

theorem realLebesgueMeasurable_inter {A B : V}
    (hA : IsRealLebesgueMeasurable A) (hB : IsRealLebesgueMeasurable B) :
    IsRealLebesgueMeasurable (A ∩ B) := by
  apply realLebesgueMeasurable_of_split_ge (fun _ h ↦ hA.1 _ (mem_inter_iff.mp h).1)
  intro T hT
  have hTA : T ∩ A ⊆ dedekindReals V := fun _ h ↦ hT _ (mem_inter_iff.mp h).1
  have hdecomp : T \ (A ∩ B) = ((T ∩ A) \ B) ∪ (T \ A) := by
    apply mem_ext
    intro x
    simp only [mem_sdiff_iff, mem_inter_iff, mem_union_iff]
    tauto
  have hfirst : T ∩ (A ∩ B) = (T ∩ A) ∩ B := by
    apply mem_ext
    intro x
    simp only [mem_inter_iff, and_assoc]
  have hbound := realOuterMeasure_union_le ((T ∩ A) \ B) (T \ A)
  rw [← hdecomp] at hbound
  have h := extendedRealAdd_mono
    (u := realOuterMeasure (T ∩ (A ∩ B))) (s := realOuterMeasure (T ∩ (A ∩ B)))
    (fun _ h ↦ h) hbound
  rw [hfirst, ← extendedRealAdd_assoc (realOuterMeasure_extended ((T ∩ A) ∩ B)).1
    (realOuterMeasure_extended ((T ∩ A) \ B)).1 (realOuterMeasure_extended (T \ A)).1,
    ← hB.2 (T ∩ A) hTA, ← hA.2 T hT] at h
  simpa only [hfirst] using h

theorem realLebesgueMeasurable_union {A B : V}
    (hA : IsRealLebesgueMeasurable A) (hB : IsRealLebesgueMeasurable B) :
    IsRealLebesgueMeasurable (A ∪ B) := by
  have h := realLebesgueMeasurable_complement
    (realLebesgueMeasurable_inter (realLebesgueMeasurable_complement hA)
      (realLebesgueMeasurable_complement hB))
  have he : (dedekindReals V) \ (((dedekindReals V) \ A) ∩ ((dedekindReals V) \ B)) = A ∪ B := by
    apply mem_ext
    intro x
    simp only [mem_sdiff_iff, mem_inter_iff, mem_union_iff]
    have ha := hA.1 x
    have hb := hB.1 x
    tauto
  rwa [he] at h

theorem realLebesgueMeasurable_sdiff {A B : V}
    (hA : IsRealLebesgueMeasurable A) (hB : IsRealLebesgueMeasurable B) :
    IsRealLebesgueMeasurable (A \ B) := by
  have h := realLebesgueMeasurable_inter hA (realLebesgueMeasurable_complement hB)
  have he : A ∩ ((dedekindReals V) \ B) = A \ B := by
    apply mem_ext
    intro x
    simp only [mem_sdiff_iff, mem_inter_iff]
    have ha := hA.1 x
    tauto
  rwa [he] at h

theorem realLebesgueMeasurable_of_null_symmetricDifference {A B : V}
    (_hA : A ⊆ dedekindReals V) (hB : IsRealLebesgueMeasurable B)
    (hnull : IsRealNull ((A \ B) ∪ (B \ A))) : IsRealLebesgueMeasurable A := by
  have hab : IsRealNull (A \ B) := realNull_subset hnull (fun _ h ↦ mem_union_iff.mpr (Or.inl h))
  have hba : IsRealNull (B \ A) := realNull_subset hnull (fun _ h ↦ mem_union_iff.mpr (Or.inr h))
  have h := realLebesgueMeasurable_union
    (realLebesgueMeasurable_sdiff hB (realNull_lebesgueMeasurable hba))
    (realNull_lebesgueMeasurable hab)
  have he : (B \ (B \ A)) ∪ (A \ B) = A := by
    apply mem_ext
    intro x
    simp only [mem_sdiff_iff, mem_union_iff]
    tauto
  rwa [he] at h

end ZFVP
