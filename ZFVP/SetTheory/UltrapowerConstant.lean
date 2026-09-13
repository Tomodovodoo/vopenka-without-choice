import ZFVP.SetTheory.UltrapowerBase
import ZFVP.ModelTheory.ConstantStructure

/-! Constant functions in the internal ultrapower. The two almost everywhere relations are
computed on a constant function: against an arbitrary function the index set reduces to a
separation on the constant value, and against a second constant function it is either the whole
index set or empty. With a set ultrafilter this turns `AEEq` and `AEMem` between constants back
into equality and membership of the values, which is what makes `x ↦ [constantGraph P x]` an
embedding later on. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The index set where a constant function's value belongs to `g`'s value. -/
theorem membershipSet_constantGraph_left (P x g : V) :
    membershipSet P (constantGraph P x) g = {p ∈ P ; x ∈ g ‘ p} := by
  apply mem_ext
  intro p
  rw [mem_membershipSet_iff, mem_sep_iff]
  constructor
  · rintro ⟨hp, hv⟩
    rw [value_constantGraph P x hp] at hv
    exact ⟨hp, hv⟩
  · rintro ⟨hp, hv⟩
    rw [value_constantGraph P x hp]
    exact ⟨hp, hv⟩

/-- The index set where `f`'s value belongs to a constant function's value. -/
theorem membershipSet_constantGraph_right (P f y : V) :
    membershipSet P f (constantGraph P y) = {p ∈ P ; f ‘ p ∈ y} := by
  apply mem_ext
  intro p
  rw [mem_membershipSet_iff, mem_sep_iff]
  constructor
  · rintro ⟨hp, hv⟩
    rw [value_constantGraph P y hp] at hv
    exact ⟨hp, hv⟩
  · rintro ⟨hp, hv⟩
    rw [value_constantGraph P y hp]
    exact ⟨hp, hv⟩

/-- The index set where a constant function agrees with `g`. -/
theorem agreementSet_constantGraph_left (P x g : V) :
    agreementSet P (constantGraph P x) g = {p ∈ P ; x = g ‘ p} := by
  apply mem_ext
  intro p
  rw [mem_agreementSet_iff, mem_sep_iff]
  constructor
  · rintro ⟨hp, hv⟩
    rw [value_constantGraph P x hp] at hv
    exact ⟨hp, hv⟩
  · rintro ⟨hp, hv⟩
    rw [value_constantGraph P x hp]
    exact ⟨hp, hv⟩

/-- A constant function agrees with itself everywhere on the index set. -/
theorem agreementSet_constantGraph_eq (P x : V) :
    agreementSet P (constantGraph P x) (constantGraph P x) = P :=
  agreementSet_self P (constantGraph P x)

/-- Constant functions with different values agree nowhere. -/
theorem agreementSet_constantGraph_ne {P x y : V} (h : x ≠ y) :
    agreementSet P (constantGraph P x) (constantGraph P y) = (∅ : V) := by
  apply mem_ext
  intro p
  rw [mem_agreementSet_iff]
  simp only [not_mem_empty, iff_false, not_and]
  intro hp
  rw [value_constantGraph P x hp, value_constantGraph P y hp]
  exact h

/-- If the value of one constant function belongs to the value of another, the membership set is
the whole index set. -/
theorem membershipSet_constantGraph_mem {P x y : V} (h : x ∈ y) :
    membershipSet P (constantGraph P x) (constantGraph P y) = P := by
  apply mem_ext
  intro p
  rw [mem_membershipSet_iff]
  constructor
  · exact fun hp ↦ hp.1
  · intro hp
    refine ⟨hp, ?_⟩
    rw [value_constantGraph P x hp, value_constantGraph P y hp]
    exact h

/-- If the value of one constant function does not belong to the value of another, the membership
set is empty. -/
theorem membershipSet_constantGraph_not_mem {P x y : V} (h : x ∉ y) :
    membershipSet P (constantGraph P x) (constantGraph P y) = (∅ : V) := by
  apply mem_ext
  intro p
  rw [mem_membershipSet_iff]
  simp only [not_mem_empty, iff_false, not_and]
  intro hp
  rw [value_constantGraph P x hp, value_constantGraph P y hp]
  exact h

variable {P U : V}

/-- Two constant functions agree almost everywhere exactly when their values are equal. -/
theorem aeEq_constantGraph_iff (hU : IsSetUltrafilter P U) (x y : V) :
    AEEq P U (constantGraph P x) (constantGraph P y) ↔ x = y := by
  constructor
  · intro hae
    by_contra hne
    rw [AEEq, agreementSet_constantGraph_ne hne] at hae
    exact hU.empty_not_mem' hae
  · rintro rfl
    rw [AEEq, agreementSet_constantGraph_eq]
    exact hU.index_mem

/-- One constant function is an a.e. member of another exactly when its value is. -/
theorem aeMem_constantGraph_iff (hU : IsSetUltrafilter P U) (x y : V) :
    AEMem P U (constantGraph P x) (constantGraph P y) ↔ x ∈ y := by
  constructor
  · intro hae
    by_contra hnm
    rw [AEMem, membershipSet_constantGraph_not_mem hnm] at hae
    exact hU.empty_not_mem' hae
  · intro hm
    rw [AEMem, membershipSet_constantGraph_mem hm]
    exact hU.index_mem

/-- A constant function lands in the functions from `P` to `A` as soon as its value does. -/
theorem constantGraph_mem_ultraFunctions {P A x : V} (hx : x ∈ A) :
    constantGraph P x ∈ A ^ P :=
  constantGraph_mem_function P A x hx

end ZFVP
