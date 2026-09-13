import ZFVP.SetTheory.UltrapowerStage
import ZFVP.Syntax.Assignments
import ZFVP.Syntax.TermSubstitutionSemantics

/-! Assignments for the internal ultrapower. An assignment for the ultrapower of `A` by an index
set `P` is a function `b ∈ (A ^ P) ^ n`, that is `n` many functions on `P`. Evaluating all of them
at one index `p` gives an ordinary assignment in `A ^ n`, which is what the Los induction feeds to
internal satisfaction. This file builds that pointwise assignment and shows it commutes with
prepending a value. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The `i`-th value of the pointwise assignment: apply the `i`-th function of `b` to `p`. -/
noncomputable def pointwiseValue (b p i : V) : V := (b ‘ i) ‘ p

instance pointwiseValue_definable : ℒₛₑₜ-function₃[V] pointwiseValue := by
  have h : ℒₛₑₜ-relation₄ (fun y b p i : V ↦ ∃ z, z = b ‘ i ∧ y = z ‘ p) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = pointwiseValue (v 1) (v 2) (v 3) ↔ _
  unfold pointwiseValue
  constructor
  · intro hy
    exact ⟨_, rfl, hy⟩
  · rintro ⟨z, hz, hy⟩
    rw [hy, hz]

/-- The assignment obtained by evaluating each of the `n` functions of `b` at the index `p`. -/
noncomputable def pointwiseAssignment (n b p : V) : V :=
  definableGraph n (pointwiseValue b p) (by definability)

instance pointwiseAssignment_isFunction (n b p : V) : IsFunction (pointwiseAssignment n b p) :=
  definableGraph_isFunction _ _ _

@[simp] theorem domain_pointwiseAssignment (n b p : V) :
    domain (pointwiseAssignment n b p) = n :=
  domain_definableGraph _ _ _

instance pointwiseAssignment_definable : ℒₛₑₜ-function₃[V] pointwiseAssignment := by
  have h : ℒₛₑₜ-relation₄ (fun B n b p : V ↦ ∀ q, q ∈ B ↔
      ∃ i ∈ n, q = ⟨i, pointwiseValue b p i⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = pointwiseAssignment (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [pointwiseAssignment, mem_definableGraph_iff]

theorem value_pointwiseAssignment {n b p i : V} (hi : i ∈ n) :
    (pointwiseAssignment n b p) ‘ i = (b ‘ i) ‘ p :=
  value_definableGraph n (pointwiseValue b p) (by definability) hi

theorem pointwiseAssignment_mem_function {P A n b p : V} (hb : b ∈ (A ^ P) ^ n) (hp : p ∈ P) :
    pointwiseAssignment n b p ∈ A ^ n := by
  apply definableGraph_mem_function_of_mapsTo
  intro i hi
  exact function_value_mem (function_value_mem hb hi) hp

/-- Prepending a function on the index set commutes with evaluating at an index. -/
theorem pointwiseAssignment_prepend {P A n b k p : V} (hn : n ∈ (ω : V)) (hb : b ∈ (A ^ P) ^ n)
    (hk : k ∈ A ^ P) (hp : p ∈ P) :
    pointwiseAssignment (succ n) (assignmentPrepend n b k) p =
      assignmentPrepend n (pointwiseAssignment n b p) (k ‘ p) := by
  apply function_eq_of_values
    (pointwiseAssignment_mem_function (assignmentPrepend_mem_function hn hb hk) hp)
    (assignmentPrepend_mem_function hn (pointwiseAssignment_mem_function hb hp)
      (function_value_mem hk hp))
  intro j hj
  by_cases hzero : j = 0
  · subst hzero
    rw [value_pointwiseAssignment (zero_mem_succ_natural hn), assignmentPrepend_zero hn,
      assignmentPrepend_zero hn]
  · have hjω : j ∈ (ω : V) :=
      IsOrdinal.toIsTransitive.mem_trans hj (ω_succ_closed hn)
    obtain ⟨i, hiω, rfl⟩ : ∃ i ∈ (ω : V), j = succ i :=
      (internalNatural_cases hjω).resolve_left hzero
    have : IsOrdinal i := IsOrdinal.of_mem hiω
    have hi : i ∈ n := by
      have := natural_predecessor_mem hn hj hzero
      rwa [sUnion_succ_of_transitive] at this
    rw [value_pointwiseAssignment hj, assignmentPrepend_succ hn hi,
      assignmentPrepend_succ hn hi, value_pointwiseAssignment hi]

end ZFVP
