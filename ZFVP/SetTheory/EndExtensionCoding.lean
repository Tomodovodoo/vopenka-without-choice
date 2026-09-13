import ZFVP.SetTheory.EndExtensionLevy
import ZFVP.SetTheory.BoundedSequenceSupport
import ZFVP.SetTheory.BoundedFunctionDomain

/-! Coding operations and all internally finite assignments agree across ZF end extensions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_empty (j : MembershipEndExtension V W) : j ∅ = ∅ :=
  (j.bounded_defined boundedEmptyFormula_bounded (fun v ↦ v 0 = (∅ : V))
    (fun v ↦ v 0 = (∅ : W)) ![∅]).mp rfl

theorem map_kpair (j : MembershipEndExtension V W) (x y : V) : j ⟨x, y⟩ₖ = ⟨j x, j y⟩ₖ :=
  (j.bounded_defined boundedKpairFormula_bounded (fun v ↦ v 0 = ⟨v 1, v 2⟩ₖ)
    (fun v ↦ v 0 = ⟨v 1, v 2⟩ₖ) ![⟨x, y⟩ₖ, x, y]).mp rfl

theorem map_doubleton (j : MembershipEndExtension V W) (x y : V) :
    j (doubleton x y) = doubleton (j x) (j y) :=
  (j.bounded_defined boundedDoubletonFormula_bounded (fun v ↦ v 0 = doubleton (v 1) (v 2))
    (fun v ↦ v 0 = doubleton (v 1) (v 2)) ![doubleton x y, x, y]).mp rfl

theorem map_union (j : MembershipEndExtension V W) (x y : V) : j (x ∪ y) = j x ∪ j y :=
  (j.bounded_defined boundedUnionFormula_bounded (fun v ↦ v 0 = v 1 ∪ v 2)
    (fun v ↦ v 0 = v 1 ∪ v 2) ![x ∪ y, x, y]).mp rfl

theorem map_succ (j : MembershipEndExtension V W) (x : V) : j (succ x) = succ (j x) :=
  (j.bounded_defined boundedSuccFormula_bounded (fun v ↦ v 0 = succ (v 1))
    (fun v ↦ v 0 = succ (v 1)) ![succ x, x]).mp rfl

theorem map_numeral (j : MembershipEndExtension V W) (n : ℕ) : j (n : V) = (n : W) := by
  induction n with
  | zero => exact j.map_empty
  | succ n ih => rw [num_succ_def, j.map_succ, ih, num_succ_def]

theorem map_omega (j : MembershipEndExtension V W) : j (ω : V) = (ω : W) :=
  (j.bounded_defined boundedOmegaFormula_bounded (fun v ↦ v 0 = (ω : V))
    (fun v ↦ v 0 = (ω : W)) ![ω]).mp rfl

theorem natural_iff (j : MembershipEndExtension V W) (n : V) : j n ∈ (ω : W) ↔ n ∈ (ω : V) := by
  rw [← j.map_omega, j.mem_iff]

omit [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem subset_iff (j : MembershipEndExtension V W) (A B : V) : j A ⊆ j B ↔ A ⊆ B := by
  constructor
  · intro h x hx
    exact (j.mem_iff _ _).mp (h (j x) ((j.mem_iff _ _).mpr hx))
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := j.endExtension A y hy
    exact (j.mem_iff _ _).mpr (h x hx)

theorem function_iff (j : MembershipEndExtension V W) (f A B : V) :
    j f ∈ j B ^ j A ↔ f ∈ B ^ A :=
  (j.bounded_defined boundedFunctionFormula_bounded (fun v ↦ v 0 ∈ v 2 ^ v 1)
    (fun v ↦ v 0 ∈ v 2 ^ v 1) ![f, A, B]).symm

theorem function_on_iff (j : MembershipEndExtension V W) (f A : V) :
    (IsFunction (j f) ∧ domain (j f) = j A) ↔ (IsFunction f ∧ domain f = A) :=
  (j.bounded_defined boundedFunctionDomainFormula_bounded (fun v ↦ IsFunction (v 0) ∧ domain (v 0) = v 1)
    (fun v ↦ IsFunction (v 0) ∧ domain (v 0) = v 1) ![f, A]).symm

theorem map_function (j : MembershipEndExtension V W) (f : V) [IsFunction f] : IsFunction (j f) :=
  ((j.function_on_iff f (domain f)).mpr ⟨inferInstance, rfl⟩).1

theorem map_domain (j : MembershipEndExtension V W) (f : V) [IsFunction f] : j (domain f) = domain (j f) :=
  ((j.function_on_iff f (domain f)).mpr ⟨inferInstance, rfl⟩).2.symm

theorem map_value (j : MembershipEndExtension V W) (f x : V) [IsFunction f] (hx : x ∈ domain f) :
    j (f ‘ x) = (j f) ‘ (j x) := by
  let := j.map_function f
  have hp := (j.mem_iff _ _).mpr (kpair_value_mem hx)
  rw [j.map_kpair] at hp
  exact (value_eq_of_kpair_mem hp).symm

theorem sequenceSupport_iff (j : MembershipEndExtension V W) (U : V) :
    IsSequenceSupport (j U) ↔ IsSequenceSupport U :=
  (j.bounded_defined sequenceSupportFormula_bounded (fun v ↦ IsSequenceSupport (v 0))
    (fun v ↦ IsSequenceSupport (v 0)) ![U]).symm

theorem map_finiteFunctionSet (j : MembershipEndExtension V W) (A : V) {n : V} (hn : n ∈ (ω : V)) :
    j (A ^ n) = j A ^ j n := by
  obtain ⟨U, hU, hAU⟩ := sequenceSupport_containing A
  let := (j.sequenceSupport_iff U).mpr hU
  have hAsub : j A ⊆ j U := (inferInstance : IsSequenceSupport (j U)).transitive _ (by
    exact (j.mem_iff _ _).mpr hAU)
  apply mem_ext
  intro b
  constructor
  · intro hb
    obtain ⟨a, ha, rfl⟩ := j.endExtension _ b hb
    exact (j.function_iff a n A).mpr ha
  · intro hb
    have hbU := function_mem_sequenceSupport hAsub ((j.natural_iff n).mpr hn) hb
    obtain ⟨a, _, rfl⟩ := j.endExtension U b hbU
    exact (j.mem_iff _ _).mpr ((j.function_iff a n A).mp hb)

theorem map_finiteSequences (j : MembershipEndExtension V W) (A : V) :
    j (finiteSequences A) = finiteSequences (j A) := by
  obtain ⟨U, hU, hAU⟩ := sequenceSupport_containing A
  let := (j.sequenceSupport_iff U).mpr hU
  have hAsub : j A ⊆ j U := (inferInstance : IsSequenceSupport (j U)).transitive _ ((j.mem_iff _ _).mpr hAU)
  apply mem_ext
  intro b
  constructor
  · intro hb
    obtain ⟨a, ha, rfl⟩ := j.endExtension _ b hb
    obtain ⟨n, hn, ha⟩ := (mem_finiteSequences_iff A a).mp ha
    exact (mem_finiteSequences_iff _ _).mpr ⟨j n, (j.natural_iff n).mpr hn, (j.function_iff a n A).mpr ha⟩
  · intro hb
    have hbU := finiteSequences_subset_support hAsub b hb
    obtain ⟨a, _, rfl⟩ := j.endExtension U b hbU
    obtain ⟨m, hm, ha⟩ := (mem_finiteSequences_iff _ _).mp hb
    rw [← j.map_omega] at hm
    obtain ⟨n, hn, rfl⟩ := j.endExtension ω m hm
    exact (j.mem_iff _ _).mpr ((mem_finiteSequences_iff _ _).mpr ⟨n, hn, (j.function_iff a n A).mp ha⟩)

end MembershipEndExtension
end ZFVP
