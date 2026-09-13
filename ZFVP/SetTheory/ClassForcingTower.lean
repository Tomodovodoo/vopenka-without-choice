import ZFVP.SetTheory.ForcingIterationSystem
import ZFVP.SetTheory.FormulaReflection

/-! A definable ordinal-indexed tower of set forcings, with sections and
projections. These are the algebraic data of the set stages used to form
a proper-class iteration. No forcing theorem or preservation conclusion
is included in the data. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure DefinableForcingTower where
  P : V → V
  R : V → V
  sectionMap : V → V → V
  projection : V → V → V
  top : V → V
  P_definable : ℒₛₑₜ-function₁ P
  R_definable : ℒₛₑₜ-function₁ R
  section_definable : ℒₛₑₜ-function₂ sectionMap
  projection_definable : ℒₛₑₜ-function₂ projection
  top_definable : ℒₛₑₜ-function₁ top
  order : ∀ i : V, IsOrdinal i → IsForcingPreorder (P i) (R i)
  top_spec : ∀ i : V, IsOrdinal i → IsForcingTop (P i) (R i) (top i)
  section_function : ∀ i j : V, IsOrdinal i → IsOrdinal j → i ⊆ j →
    sectionMap i j ∈ (P j) ^ (P i)
  projection_function : ∀ i j : V, IsOrdinal i → IsOrdinal j → i ⊆ j →
    projection i j ∈ (P i) ^ (P j)
  section_self : ∀ i : V, IsOrdinal i → ∀ p ∈ P i, (sectionMap i i) ‘ p = p
  projection_self : ∀ i : V, IsOrdinal i → ∀ p ∈ P i, (projection i i) ‘ p = p
  section_comp : (∀ i j k : V, IsOrdinal i → IsOrdinal j → IsOrdinal k →
    i ⊆ j → j ⊆ k → ∀ p ∈ P i,
      (sectionMap j k) ‘ ((sectionMap i j) ‘ p) = (sectionMap i k) ‘ p)
  projection_comp : (∀ i j k : V, IsOrdinal i → IsOrdinal j → IsOrdinal k →
    i ⊆ j → j ⊆ k → ∀ p ∈ P k,
      (projection i j) ‘ ((projection j k) ‘ p) = (projection i k) ‘ p)
  projection_section : (∀ i j : V, IsOrdinal i → IsOrdinal j → i ⊆ j →
    ∀ p ∈ P i, (projection i j) ‘ ((sectionMap i j) ‘ p) = p)
  projection_mono : (∀ i j : V, IsOrdinal i → IsOrdinal j → i ⊆ j →
    ∀ p ∈ P j, ∀ q ∈ P j, ⟨p, q⟩ₖ ∈ R j →
      ⟨(projection i j) ‘ p, (projection i j) ‘ q⟩ₖ ∈ R i)
  below_section : (∀ i j : V, IsOrdinal i → IsOrdinal j → i ⊆ j →
    ∀ p ∈ P j, ∀ q ∈ P i,
      ⟨p, (sectionMap i j) ‘ q⟩ₖ ∈ R j ↔ ⟨(projection i j) ‘ p, q⟩ₖ ∈ R i)
  section_top : ∀ i j : V, IsOrdinal i → IsOrdinal j → i ⊆ j →
    (sectionMap i j) ‘ (top i) = top j
  lift : (∀ i j : V, IsOrdinal i → IsOrdinal j → i ⊆ j →
    ∀ p ∈ P j, ∀ q ∈ P i, ⟨q, (projection i j) ‘ p⟩ₖ ∈ R i →
      ∃ r ∈ P j, ⟨r, p⟩ₖ ∈ R j ∧ (projection i j) ‘ r = q)

namespace DefinableForcingTower

variable {V} (T : DefinableForcingTower V)

theorem section_mem {i j p : V} [IsOrdinal i] [IsOrdinal j]
    (hij : i ⊆ j) (hp : p ∈ T.P i) : (T.sectionMap i j) ‘ p ∈ T.P j :=
  function_value_mem (T.section_function i j inferInstance inferInstance hij) hp

theorem projection_mem {i j p : V} [IsOrdinal i] [IsOrdinal j]
    (hij : i ⊆ j) (hp : p ∈ T.P j) : (T.projection i j) ‘ p ∈ T.P i :=
  function_value_mem (T.projection_function i j inferInstance inferInstance hij) hp

theorem section_order_iff {i j p q : V} [IsOrdinal i] [IsOrdinal j]
    (hij : i ⊆ j) (hp : p ∈ T.P i) (hq : q ∈ T.P i) :
    ⟨(T.sectionMap i j) ‘ p, (T.sectionMap i j) ‘ q⟩ₖ ∈ T.R j ↔
      ⟨p, q⟩ₖ ∈ T.R i := by
  rw [T.below_section i j inferInstance inferInstance hij _ (T.section_mem hij hp) q hq,
    T.projection_section i j inferInstance inferInstance hij p hp]

theorem section_injective {i j : V} [IsOrdinal i] [IsOrdinal j] (hij : i ⊆ j) :
    Injective (T.sectionMap i j) := by
  let := IsFunction.of_mem (T.section_function i j inferInstance inferInstance hij)
  intro p q z hp hq
  have hpP : p ∈ T.P i :=
    (mem_of_mem_functions (T.section_function i j inferInstance inferInstance hij) hp).1
  have hqP : q ∈ T.P i :=
    (mem_of_mem_functions (T.section_function i j inferInstance inferInstance hij) hq).1
  have he := congrArg (fun x ↦ (T.projection i j) ‘ x)
    ((value_eq_of_kpair_mem hp).trans (value_eq_of_kpair_mem hq).symm)
  simpa only [T.projection_section i j inferInstance inferInstance hij p hpP,
    T.projection_section i j inferInstance inferInstance hij q hqP] using he

end DefinableForcingTower
end ZFVP
