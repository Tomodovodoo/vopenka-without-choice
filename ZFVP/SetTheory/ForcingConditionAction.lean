import ZFVP.SetTheory.ForcingQuantifiers
import ZFVP.SetTheory.ForcingAutomorphisms

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingNegation_action_iff {P R π A B p : V} (hπ : IsForcingAutomorphism P R π)
    (hAB : ∀ q ∈ P, π ‘ q ∈ B ↔ q ∈ A) (hp : p ∈ P) :
    π ‘ p ∈ forcingNegation P R B ↔ p ∈ forcingNegation P R A := by
  rw [mem_forcingNegation_iff, mem_forcingNegation_iff]
  constructor
  · rintro ⟨_, hh⟩
    refine ⟨hp, ?_⟩
    intro q hq hqp hqA
    exact hh (π ‘ q) (function_value_mem hπ.1 hq) ((hπ.2.2.2 q hq p hp).mp hqp) ((hAB q hq).mpr hqA)
  · rintro ⟨_, hh⟩
    refine ⟨function_value_mem hπ.1 hp, ?_⟩
    intro q' hq' hq'p hq'B
    obtain ⟨q, hq, he⟩ := forcingAutomorphism_surjective hπ q' hq'
    subst q'
    exact hh q hq ((hπ.2.2.2 q hq p hp).mpr hq'p) ((hAB q hq).mp hq'B)

theorem forcingClosure_action_iff {P R π A B p : V} (hπ : IsForcingAutomorphism P R π)
    (hA : A ⊆ P) (hB : B ⊆ P) (hAB : ∀ q ∈ P, π ‘ q ∈ B ↔ q ∈ A) (hp : p ∈ P) :
    π ‘ p ∈ forcingClosure P R B ↔ p ∈ forcingClosure P R A := by
  rw [mem_forcingClosure_iff, mem_forcingClosure_iff]
  constructor
  · rintro ⟨_, hh⟩
    refine ⟨hp, ?_⟩
    intro q hq hqp
    obtain ⟨r', hr'B, hr'q⟩ := hh (π ‘ q) (function_value_mem hπ.1 hq) ((hπ.2.2.2 q hq p hp).mp hqp)
    obtain ⟨r, hr, he⟩ := forcingAutomorphism_surjective hπ r' (hB r' hr'B)
    subst r'
    exact ⟨r, (hAB r hr).mp hr'B, (hπ.2.2.2 r hr q hq).mpr hr'q⟩
  · rintro ⟨_, hh⟩
    refine ⟨function_value_mem hπ.1 hp, ?_⟩
    intro q' hq' hq'p
    obtain ⟨q, hq, he⟩ := forcingAutomorphism_surjective hπ q' hq'
    subst q'
    obtain ⟨r, hrA, hrq⟩ := hh q hq ((hπ.2.2.2 q hq p hp).mpr hq'p)
    exact ⟨π ‘ r, (hAB r (hA r hrA)).mpr hrA, (hπ.2.2.2 r (hA r hrA) q hq).mp hrq⟩

theorem forcingClassIntersection_action_iff {P R π p : V} (hπ : IsForcingAutomorphism P R π)
    (N : V → Prop) (hN : ℒₛₑₜ-predicate N) (T : V → V)
    (hT : ∀ x, N x → N (T x)) (hsurj : ∀ y, N y → ∃ x, N x ∧ T x = y)
    (A B : V → V) (hA : ℒₛₑₜ-function₁ A) (hB : ℒₛₑₜ-function₁ B)
    (hAB : ∀ x, N x → ∀ q ∈ P, π ‘ q ∈ B (T x) ↔ q ∈ A x) (hp : p ∈ P) :
    π ‘ p ∈ forcingClassIntersection P N hN B hB ↔ p ∈ forcingClassIntersection P N hN A hA := by
  rw [mem_forcingClassIntersection_iff, mem_forcingClassIntersection_iff]
  constructor
  · rintro ⟨_, hh⟩
    exact ⟨hp, fun x hx ↦ (hAB x hx p hp).mp (hh (T x) (hT x hx))⟩
  · rintro ⟨_, hh⟩
    refine ⟨function_value_mem hπ.1 hp, ?_⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hsurj y hy
    exact (hAB x hx p hp).mpr (hh x hx)

theorem forcingClassUnion_action_iff {P R π p : V} (hπ : IsForcingAutomorphism P R π)
    (N : V → Prop) (hN : ℒₛₑₜ-predicate N) (T : V → V)
    (hT : ∀ x, N x → N (T x)) (hsurj : ∀ y, N y → ∃ x, N x ∧ T x = y)
    (A B : V → V) (hA : ℒₛₑₜ-function₁ A) (hB : ℒₛₑₜ-function₁ B)
    (hAB : ∀ x, N x → ∀ q ∈ P, π ‘ q ∈ B (T x) ↔ q ∈ A x) (hp : p ∈ P) :
    π ‘ p ∈ forcingClassUnion P N hN B hB ↔ p ∈ forcingClassUnion P N hN A hA := by
  rw [mem_forcingClassUnion_iff, mem_forcingClassUnion_iff]
  constructor
  · rintro ⟨_, y, hy, hpB⟩
    obtain ⟨x, hx, rfl⟩ := hsurj y hy
    exact ⟨hp, x, hx, (hAB x hx p hp).mp hpB⟩
  · rintro ⟨_, x, hx, hpA⟩
    exact ⟨function_value_mem hπ.1 hp, T x, hT x hx, (hAB x hx p hp).mpr hpA⟩

end ZFVP
