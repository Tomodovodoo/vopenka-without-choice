import ZFVP.SetTheory.CantorInfiniteOnes
import ZFVP.SetTheory.LeastOrdinalChoice
import ZFVP.SetTheory.NaturalArithmeticOrder
import ZFVP.SetTheory.NaturalIteration

/-! Definable separator positions for decoding the run representation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def isCantorOneFromFormula : SetTheorySemisentence 3 :=
  f“x l k. k ∈ !isω ∧ l ⊆ k ∧ !value.dfn x k = !(numeralFormula 1)”

def cantorNextOneFormula : SetTheorySemisentence 3 :=
  f“k x l. (!IsOrdinal.dfn k ∧ !isCantorOneFromFormula x l k ∧
    ∀ j, !IsOrdinal.dfn j → !isCantorOneFromFormula x l j → k ⊆ j) ∨
    ((∀ j, !IsOrdinal.dfn j → ¬!isCantorOneFromFormula x l j) ∧ !isEmpty k)”

def naturalDifferenceFormula : SetTheorySemisentence 3 :=
  f“d l k. (!IsOrdinal.dfn d ∧ (d ∈ !isω ∧ !ordinalAddFormula k l d) ∧
    ∀ j, !IsOrdinal.dfn j → (j ∈ !isω ∧ !ordinalAddFormula k l j) → d ⊆ j) ∨
    ((∀ j, !IsOrdinal.dfn j → ¬(j ∈ !isω ∧ !ordinalAddFormula k l j)) ∧ !isEmpty d)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsCantorOneFrom (x l k : V) : Prop := k ∈ (ω : V) ∧ l ⊆ k ∧ x ‘ k = 1

instance isCantorOneFromFormula_defined :
    ℒₛₑₜ-relation₃[V] IsCantorOneFrom via isCantorOneFromFormula :=
  ⟨fun v ↦ by simp [isCantorOneFromFormula, IsCantorOneFrom]⟩

instance isCantorOneFrom_definable : ℒₛₑₜ-relation₃[V] IsCantorOneFrom :=
  isCantorOneFromFormula_defined.to_definable

noncomputable def cantorNextOne (x l : V) : V :=
  leastOrdinalOrZero (fun x k ↦ IsCantorOneFrom x l k) (by definability) x

instance cantorNextOneFormula_defined :
    ℒₛₑₜ-function₂[V] cantorNextOne via cantorNextOneFormula := by
  refine ⟨fun v ↦ ?_⟩
  change cantorNextOneFormula.Evalb v ↔ v 0 = cantorNextOne (v 1) (v 2)
  rw [cantorNextOne, leastOrdinalOrZero_eq_iff]
  simp [cantorNextOneFormula, IsLeastOrdinal, zero_def]

instance cantorNextOne_definable : ℒₛₑₜ-function₂[V] cantorNextOne :=
  cantorNextOneFormula_defined.to_definable

theorem cantorNextOne_spec {x l : V} (hx : x ∈ cantorInfiniteOnes V) (hl : l ∈ (ω : V)) :
    IsLeastOrdinal (IsCantorOneFrom x l) (cantorNextOne x l) := by
  obtain ⟨k, hk, hlk, hxk⟩ := ((mem_cantorInfiniteOnes_iff x).mp hx).2 l hl
  exact leastOrdinalOrZero_spec _ _ x ⟨k, IsOrdinal.of_mem hk, hk, hlk, hxk⟩

theorem cantorNextOne_mem {x l : V} (hx : x ∈ cantorInfiniteOnes V) (hl : l ∈ (ω : V)) :
    cantorNextOne x l ∈ (ω : V) := (cantorNextOne_spec hx hl).2.1.1

theorem cantorNextOne_ge {x l : V} (hx : x ∈ cantorInfiniteOnes V) (hl : l ∈ (ω : V)) :
    l ⊆ cantorNextOne x l := (cantorNextOne_spec hx hl).2.1.2.1

theorem cantorNextOne_value {x l : V} (hx : x ∈ cantorInfiniteOnes V) (hl : l ∈ (ω : V)) :
    x ‘ (cantorNextOne x l) = 1 := (cantorNextOne_spec hx hl).2.1.2.2

theorem cantorNextOne_before_zero {x l i : V} (hx : x ∈ cantorInfiniteOnes V)
    (hl : l ∈ (ω : V)) (hli : l ⊆ i) (hi : i ∈ cantorNextOne x l) : x ‘ i = 0 := by
  have hiω : i ∈ (ω : V) := IsTransitive.ω.transitive _ (cantorNextOne_mem hx hl) _ hi
  have hv := function_value_mem ((mem_cantorInfiniteOnes_iff x).mp hx).1 hiω
  rcases show x ‘ i = (0 : V) ∨ x ‘ i = 1 from by simpa using hv with hzero | hone
  · exact hzero
  · have hle := (cantorNextOne_spec hx hl).2.2 i (IsOrdinal.of_mem hiω) ⟨hiω, hli, hone⟩
    exact (mem_irrefl i (hle i hi)).elim

noncomputable def naturalDifference (l k : V) : V :=
  leastOrdinalOrZero (fun l d ↦ d ∈ (ω : V) ∧ ordinalAdd l d = k) (by definability) l

instance naturalDifferenceFormula_defined :
    ℒₛₑₜ-function₂[V] naturalDifference via naturalDifferenceFormula := by
  refine ⟨fun v ↦ ?_⟩
  change naturalDifferenceFormula.Evalb v ↔ v 0 = naturalDifference (v 1) (v 2)
  rw [naturalDifference, leastOrdinalOrZero_eq_iff]
  simp [naturalDifferenceFormula, IsLeastOrdinal, zero_def, eq_comm]
  exact or_congr Iff.rfl (and_congr (forall_congr' (fun j ↦ by tauto)) Iff.rfl)

instance naturalDifference_definable : ℒₛₑₜ-function₂[V] naturalDifference :=
  naturalDifferenceFormula_defined.to_definable

theorem naturalDifference_spec {l k : V} (hl : l ∈ (ω : V)) (hk : k ∈ (ω : V)) (hlk : l ⊆ k) :
    naturalDifference l k ∈ (ω : V) ∧ ordinalAdd l (naturalDifference l k) = k := by
  obtain ⟨d, hd, he⟩ := ordinalAdd_difference_natural hl hk hlk
  exact (leastOrdinalOrZero_spec
    (fun l d : V ↦ d ∈ (ω : V) ∧ ordinalAdd l d = k) (by definability) l
    ⟨d, IsOrdinal.of_mem hd, hd, he⟩).2.1

def cantorRunStartStepFormula : SetTheorySemisentence 3 :=
  f“z x g. (!domain.dfn g = !isEmpty ∧ !isEmpty z) ∨
    (!domain.dfn g ≠ !isEmpty ∧ z = !succ.dfn
      (!cantorNextOneFormula x (!value.dfn g (!sUnion.dfn (!domain.dfn g)))))”

def cantorRunStartFormula : SetTheorySemisentence 3 :=
  parameterRecursionFormula cantorRunStartStepFormula

noncomputable def cantorRunStartStep (x g : V) : V :=
  naturalIterationStep (fun l ↦ succ (cantorNextOne x l)) 0 g

instance cantorRunStartStepFormula_defined :
    ℒₛₑₜ-function₂[V] cantorRunStartStep via cantorRunStartStepFormula :=
  ⟨fun v ↦ by
    by_cases h : domain (v 2) = 0
    · simp_all [cantorRunStartStepFormula, cantorRunStartStep, naturalIterationStep, zero_def]
    · simp_all [cantorRunStartStepFormula, cantorRunStartStep, naturalIterationStep,
        zero_def, -ne_empty_iff_isNonempty]⟩

instance cantorRunStartStep_definable : ℒₛₑₜ-function₂[V] cantorRunStartStep :=
  cantorRunStartStepFormula_defined.to_definable

noncomputable def cantorRunStart (x n : V) : V :=
  naturalIteration (fun l ↦ succ (cantorNextOne x l)) (by definability) 0 n

instance cantorRunStartFormula_defined :
    ℒₛₑₜ-function₂[V] cantorRunStart via cantorRunStartFormula :=
  parameterRecursionFormula_defined cantorRunStartStep cantorRunStartStepFormula

instance cantorRunStart_definable : ℒₛₑₜ-function₂[V] cantorRunStart :=
  cantorRunStartFormula_defined.to_definable

theorem cantorRunStart_zero (x : V) : cantorRunStart x 0 = 0 :=
  naturalIteration_zero _ _ _

theorem cantorRunStart_succ (x : V) {n : V} (hn : n ∈ (ω : V)) :
    cantorRunStart x (succ n) = succ (cantorNextOne x (cantorRunStart x n)) :=
  naturalIteration_succ _ _ _ hn

theorem cantorRunStart_mem {x n : V} (hx : x ∈ cantorInfiniteOnes V) (hn : n ∈ (ω : V)) :
    cantorRunStart x n ∈ (ω : V) := by
  apply naturalNumber_induction (fun n ↦ cantorRunStart x n ∈ (ω : V)) (by definability) ?_ ?_ n hn
  · rw [cantorRunStart_zero]; simp
  · intro n hn ih
    rw [cantorRunStart_succ x hn]
    exact ω_succ_closed (cantorNextOne_mem hx ih)

theorem cantorRunStart_length_bound {x n : V} (hx : x ∈ cantorInfiniteOnes V) (hn : n ∈ (ω : V)) :
    n ⊆ cantorRunStart x n := by
  apply naturalNumber_induction (fun n ↦ n ⊆ cantorRunStart x n) (by definability) ?_ ?_ n hn
  · exact empty_subset _
  · intro n hn ih
    have : IsOrdinal n := IsOrdinal.of_mem hn
    have : IsOrdinal (cantorNextOne x (cantorRunStart x n)) :=
      IsOrdinal.of_mem (cantorNextOne_mem hx (cantorRunStart_mem hx hn))
    have hle := subset_trans ih (cantorNextOne_ge hx (cantorRunStart_mem hx hn))
    rw [cantorRunStart_succ x hn]
    intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hle)
    · exact mem_succ_iff.mpr (Or.inr (hle i hi))

end ZFVP
