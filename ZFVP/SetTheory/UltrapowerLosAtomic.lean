import ZFVP.SetTheory.UltrapowerCollapse
import ZFVP.SetTheory.UltrapowerAssignment
import ZFVP.SetTheory.FunctionComposition
import ZFVP.Syntax.DirectMembershipAtoms

/-! The atomic clause of Los's theorem for the internal ultrapower.

An assignment for the ultrapower of a transitive set `A` by an ultrafilter `U` on `P` is a function
`b ∈ (A ^ P) ^ n`. Composing it with the collapse map gives an assignment into the collapsed set
`ultraTarget P U A`, and evaluating it at an index `p ∈ P` gives an assignment into `A`. An atomic
formula of the membership language relates the values of two variables by equality or by membership.
On the collapsed side the collapse map turns those two relations into a.e. equality and a.e.
membership of the two functions; on the pointwise side the set of indices where the formula holds is
exactly the index set of that a.e. relation. So the two sides are the same set fed into `U`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The set of indices at which an atomic formula holds of the pointwise assignment. -/
noncomputable def atomicLosSet (P A n b r args : V) : V :=
  {p ∈ P ; AtomicHolds membershipLanguageCode ∅ (membershipStructureCode A) ∅ n
    (pointwiseAssignment n b p) r args}

theorem mem_atomicLosSet_iff {P A n b r args p : V} :
    p ∈ atomicLosSet P A n b r args ↔ p ∈ P ∧
      AtomicHolds membershipLanguageCode ∅ (membershipStructureCode A) ∅ n
        (pointwiseAssignment n b p) r args := by
  rw [atomicLosSet, mem_sep_iff]

theorem atomicLosSet_subset (P A n b r args : V) : atomicLosSet P A n b r args ⊆ P :=
  fun _ hp ↦ (mem_atomicLosSet_iff.mp hp).1

/-! ### The two computations the proof runs on -/

/-- Each of the `n` entries of an ultrapower assignment is a function from `P` into `A`. -/
theorem ultraAssignment_value_mem {P A n b i : V} (hb : b ∈ (A ^ P) ^ n) (hi : i ∈ n) :
    b ‘ i ∈ A ^ P := function_value_mem hb hi

/-- Composing an ultrapower assignment with the collapse map gives an assignment into the
collapsed set. -/
theorem compose_ultraCollapse_mem_function {P U A n b : V}
    (hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P)) (hb : b ∈ (A ^ P) ^ n) :
    compose b (ultraCollapse P U A) ∈ (ultraTarget P U A) ^ n :=
  compose_function hb (ultraCollapse_mem_function hwf)

/-- The `i`-th value of the composed assignment is the collapse of the `i`-th function. -/
theorem value_compose_ultraCollapse {P U A n b i : V}
    (hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P)) (hb : b ∈ (A ^ P) ^ n)
    (hi : i ∈ n) :
    (compose b (ultraCollapse P U A)) ‘ i = (ultraCollapse P U A) ‘ (b ‘ i) :=
  value_compose_of_mem_function hb (ultraCollapse_mem_function hwf) hi

/-! ### The index sets of the three atomic shapes -/

theorem atomicLosSet_logicalEquality {P A n b i j : V} (hn : n ∈ (ω : V)) (hi : i ∈ n)
    (hj : j ∈ n) :
    atomicLosSet P A n b equalityToken (boundPairArguments i j) = ultraAgree P (b ‘ i) (b ‘ j) := by
  apply mem_ext
  intro p
  rw [mem_atomicLosSet_iff, mem_ultraAgree_iff]
  refine and_congr_right fun _ ↦ ?_
  rw [membershipAtomic_logicalEquality hn hi hj, value_pointwiseAssignment hi,
    value_pointwiseAssignment hj]

theorem atomicLosSet_relationEquality {P A n b i j : V} (hn : n ∈ (ω : V)) (hi : i ∈ n)
    (hj : j ∈ n) (hb : b ∈ (A ^ P) ^ n) :
    atomicLosSet P A n b (relationToken (0 : V)) (boundPairArguments i j) =
      ultraAgree P (b ‘ i) (b ‘ j) := by
  apply mem_ext
  intro p
  rw [mem_atomicLosSet_iff, mem_ultraAgree_iff]
  refine and_congr_right fun hp ↦ ?_
  rw [membershipAtomic_relationEquality hn hi hj (pointwiseAssignment_mem_function hb hp),
    value_pointwiseAssignment hi, value_pointwiseAssignment hj]

theorem atomicLosSet_membership {P A n b i j : V} (hn : n ∈ (ω : V)) (hi : i ∈ n) (hj : j ∈ n)
    (hb : b ∈ (A ^ P) ^ n) :
    atomicLosSet P A n b (relationToken (1 : V)) (boundPairArguments i j) =
      ultraMem P (b ‘ i) (b ‘ j) := by
  apply mem_ext
  intro p
  rw [mem_atomicLosSet_iff, mem_ultraMem_iff]
  refine and_congr_right fun hp ↦ ?_
  rw [membershipAtomic_membership hn hi hj (pointwiseAssignment_mem_function hb hp),
    value_pointwiseAssignment hi, value_pointwiseAssignment hj]

/-! ### The atomic clause -/

/-- Los's theorem for atomic formulas: an atomic formula holds of the collapsed assignment in the
ultrapower exactly when it holds pointwise on a set in the ultrafilter. -/
theorem atomicHolds_ultraTarget_iff (hAC : InternalChoice V) {P U A κ : V} [IsOrdinal κ]
    [IsTransitive A] (hU : IsSetUltrafilter P U) (hcomp : IsOrdinalCompleteOn P κ U)
    (hω : (ω : V) ∈ κ) (hA : IsNonempty A) {n b r args : V} (hn : n ∈ (ω : V))
    (hb : b ∈ (A ^ P) ^ n) (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) :
    AtomicHolds membershipLanguageCode ∅ (membershipStructureCode (ultraTarget P U A)) ∅ n
        (compose b (ultraCollapse P U A)) r args ↔
      atomicLosSet P A n b r args ∈ U := by
  have hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P) :=
    ultraMemRelation_wellFounded hAC hU hcomp hω
  obtain ⟨hr, i, hi, j, hj, rfl⟩ := (membershipAtomicArguments_iff hn).mp ha
  have hbi : b ‘ i ∈ A ^ P := ultraAssignment_value_mem hb hi
  have hbj : b ‘ j ∈ A ^ P := ultraAssignment_value_mem hb hj
  have hci := value_compose_ultraCollapse hwf hb hi
  have hcj := value_compose_ultraCollapse hwf hb hj
  rcases hr with rfl | rfl | rfl
  · rw [membershipAtomic_logicalEquality hn hi hj, hci, hcj,
      ultraCollapse_eq_iff hAC hU hcomp hω hA hbi hbj, atomicLosSet_logicalEquality hn hi hj]
    exact Iff.rfl
  · rw [membershipAtomic_relationEquality hn hi hj (compose_ultraCollapse_mem_function hwf hb),
      hci, hcj, ultraCollapse_eq_iff hAC hU hcomp hω hA hbi hbj,
      atomicLosSet_relationEquality hn hi hj hb]
    exact Iff.rfl
  · rw [membershipAtomic_membership hn hi hj (compose_ultraCollapse_mem_function hwf hb),
      hci, hcj, ultraCollapse_mem_iff hAC hU hcomp hω hA hbi hbj,
      atomicLosSet_membership hn hi hj hb]
    exact Iff.rfl

end ZFVP
