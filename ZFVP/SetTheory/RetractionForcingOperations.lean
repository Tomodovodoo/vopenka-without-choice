import ZFVP.SetTheory.ForcingRetraction
import ZFVP.SetTheory.ClassFormulaForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingRetraction.forcingNegation_iff {P R N T m A B p : V}
    (hr : IsForcingRetraction N T P R m)
    (he : ∀ q ∈ P, q ∈ A ↔ m ‘ q ∈ B) (hp : p ∈ P) :
    p ∈ forcingNegation P R A ↔ m ‘ p ∈ forcingNegation N T B := by
  rw [mem_forcingNegation_iff, mem_forcingNegation_iff]
  constructor
  · rintro ⟨_, hh⟩
    refine ⟨function_value_mem hr.maps hp, ?_⟩
    intro n hn hnp hnB
    obtain ⟨q, hq, hqp, hqn⟩ := hr.lift p hp n hn hnp
    exact hh q hq hqp ((he q hq).mpr (hqn.symm ▸ hnB))
  · rintro ⟨_, hh⟩
    exact ⟨hp, fun q hq hqp hqA ↦ hh _ (function_value_mem hr.maps hq)
      (hr.monotone q hq p hp hqp) ((he q hq).mp hqA)⟩

theorem IsForcingRetraction.forcingClosure_iff {P R N T m A B p : V}
    (hr : IsForcingRetraction N T P R m) (hA : A ⊆ P) (hB : B ⊆ N)
    (he : ∀ q ∈ P, q ∈ A ↔ m ‘ q ∈ B) (hp : p ∈ P) :
    p ∈ forcingClosure P R A ↔ m ‘ p ∈ forcingClosure N T B := by
  rw [mem_forcingClosure_iff, mem_forcingClosure_iff]
  constructor
  · rintro ⟨_, hh⟩
    refine ⟨function_value_mem hr.maps hp, ?_⟩
    intro n hn hnp
    obtain ⟨q, hq, hqp, hqn⟩ := hr.lift p hp n hn hnp
    obtain ⟨r, hrA, hrq⟩ := hh q hq hqp
    refine ⟨m ‘ r, (he r (hA r hrA)).mp hrA, ?_⟩
    simpa only [hqn] using hr.monotone r (hA r hrA) q hq hrq
  · rintro ⟨_, hh⟩
    refine ⟨hp, ?_⟩
    intro q hq hqp
    obtain ⟨n, hnB, hnq⟩ := hh _ (function_value_mem hr.maps hq) (hr.monotone q hq p hp hqp)
    obtain ⟨r, hrP, hrq, hrn⟩ := hr.lift q hq n (hB n hnB) hnq
    exact ⟨r, (he r hrP).mpr (hrn.symm ▸ hnB), hrq⟩

theorem IsForcingRetraction.forcingClassIntersection_iff {P R N T m p : V}
    (hr : IsForcingRetraction N T P R m)
    (A B : V → Prop) (hA : ℒₛₑₜ-predicate A) (hB : ℒₛₑₜ-predicate B)
    (F : V → V) (hF : ∀ x, A x → B (F x)) (hsurj : ∀ y, B y → ∃ x, A x ∧ F x = y)
    (X Y : V → V) (hX : ℒₛₑₜ-function₁ X) (hY : ℒₛₑₜ-function₁ Y)
    (he : ∀ x, A x → ∀ q ∈ P, q ∈ X x ↔ m ‘ q ∈ Y (F x)) (hp : p ∈ P) :
    p ∈ forcingClassIntersection P A hA X hX ↔
      m ‘ p ∈ forcingClassIntersection N B hB Y hY := by
  rw [mem_forcingClassIntersection_iff, mem_forcingClassIntersection_iff]
  constructor
  · rintro ⟨_, hh⟩
    refine ⟨function_value_mem hr.maps hp, ?_⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hsurj y hy
    exact (he x hx p hp).mp (hh x hx)
  · rintro ⟨_, hh⟩
    exact ⟨hp, fun x hx ↦ (he x hx p hp).mpr (hh _ (hF x hx))⟩

theorem IsForcingRetraction.forcingClassUnion_iff {P R N T m p : V}
    (hr : IsForcingRetraction N T P R m)
    (A B : V → Prop) (hA : ℒₛₑₜ-predicate A) (hB : ℒₛₑₜ-predicate B)
    (F : V → V) (hF : ∀ x, A x → B (F x)) (hsurj : ∀ y, B y → ∃ x, A x ∧ F x = y)
    (X Y : V → V) (hX : ℒₛₑₜ-function₁ X) (hY : ℒₛₑₜ-function₁ Y)
    (he : ∀ x, A x → ∀ q ∈ P, q ∈ X x ↔ m ‘ q ∈ Y (F x)) (hp : p ∈ P) :
    p ∈ forcingClassUnion P A hA X hX ↔ m ‘ p ∈ forcingClassUnion N B hB Y hY := by
  rw [mem_forcingClassUnion_iff, mem_forcingClassUnion_iff]
  constructor
  · rintro ⟨_, x, hx, hh⟩
    exact ⟨function_value_mem hr.maps hp, F x, hF x hx, (he x hx p hp).mp hh⟩
  · rintro ⟨_, y, hy, hh⟩
    obtain ⟨x, hx, rfl⟩ := hsurj y hy
    exact ⟨hp, x, hx, (he x hx p hp).mpr hh⟩

end ZFVP
