import ZFVP.SetTheory.ForcingRegular

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingClassUnion (P : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) : V := sep P (fun p ↦ ∃ x, N x ∧ p ∈ F x) (by definability)

noncomputable def forcingClassIntersection (P : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) : V := sep P (fun p ↦ ∀ x, N x → p ∈ F x) (by definability)

theorem mem_forcingClassUnion_iff (P : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) (p : V) :
    p ∈ forcingClassUnion P N hN F hF ↔ p ∈ P ∧ ∃ x, N x ∧ p ∈ F x := mem_sep_iff

theorem mem_forcingClassIntersection_iff (P : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) (p : V) :
    p ∈ forcingClassIntersection P N hN F hF ↔ p ∈ P ∧ ∀ x, N x → p ∈ F x := mem_sep_iff

theorem forcingClassUnion_subset (P : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) : forcingClassUnion P N hN F hF ⊆ P := by
  intro p hp
  exact (mem_sep_iff.mp hp).1

theorem forcingClassUnion_downward {P R : V} (N : V → Prop) (hN : ℒₛₑₜ-predicate N)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) (hreg : ∀ x, N x → IsForcingDownwardClosed P R (F x)) :
    IsForcingDownwardClosed P R (forcingClassUnion P N hN F hF) := by
  intro p hp q hq hqp
  obtain ⟨_, x, hx, hpF⟩ := (mem_forcingClassUnion_iff _ _ _ _ _ _).mp hp
  exact (mem_forcingClassUnion_iff _ _ _ _ _ _).mpr ⟨hq, x, hx, hreg x hx p hpF q hq hqp⟩

theorem forcingClassIntersection_regular {P R : V} (N : V → Prop) (hN : ℒₛₑₜ-predicate N)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) (hreg : ∀ x, N x → IsForcingRegular P R (F x)) :
    IsForcingRegular P R (forcingClassIntersection P N hN F hF) := by
  refine ⟨fun p hp ↦ (mem_sep_iff.mp hp).1, ?_, ?_⟩
  · intro p hp q hq hqp
    obtain ⟨_, hh⟩ := (mem_forcingClassIntersection_iff _ _ _ _ _ _).mp hp
    exact (mem_forcingClassIntersection_iff _ _ _ _ _ _).mpr
      ⟨hq, fun x hx ↦ (hreg x hx).2.1 p (hh x hx) q hq hqp⟩
  · intro p hp hd
    apply (mem_forcingClassIntersection_iff _ _ _ _ _ _).mpr
    refine ⟨hp, ?_⟩
    intro x hx
    apply (hreg x hx).2.2 p hp
    intro q hq hqp
    obtain ⟨r, hr, hrq⟩ := hd q hq hqp
    exact ⟨r, ((mem_forcingClassIntersection_iff _ _ _ _ _ _).mp hr).2 x hx, hrq⟩

theorem forcingClassIntersection_eq_negation {P R : V} (hR : IsForcingPreorder P R)
    (N : V → Prop) (hN : ℒₛₑₜ-predicate N) (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (hreg : ∀ x, N x → IsForcingRegular P R (F x)) :
    forcingClassIntersection P N hN F hF =
      forcingNegation P R (forcingClassUnion P N hN (fun x ↦ forcingNegation P R (F x)) (by definability)) := by
  classical
  apply SetTheory.mem_ext_iff.mpr
  intro p
  rw [mem_forcingClassIntersection_iff, mem_forcingNegation_iff]
  constructor
  · rintro ⟨hp, hall⟩
    refine ⟨hp, ?_⟩
    intro q hq hqp hqU
    obtain ⟨_, x, hx, hqN⟩ := (mem_forcingClassUnion_iff _ _ _ _ _ _).mp hqU
    exact forcingNegation_disjoint hR hqN ((hreg x hx).2.1 p (hall x hx) q hq hqp)
  · rintro ⟨hp, hnone⟩
    refine ⟨hp, ?_⟩
    intro x hx
    by_contra hpN
    obtain ⟨q, hqN, hqp⟩ := exists_forcingNegation_of_not_mem hp hpN (hreg x hx).2.2
    have hqP := forcingNegation_subset _ _ _ q hqN
    exact hnone q hqP hqp ((mem_forcingClassUnion_iff _ _ _ _ _ _).mpr ⟨hqP, x, hx, hqN⟩)

noncomputable def forcingExistential (P R : V) (N : V → Prop) (hN : ℒₛₑₜ-predicate N)
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) : V := forcingClosure P R (forcingClassUnion P N hN F hF)

theorem forcingExistential_regular {P R : V} (hR : IsForcingPreorder P R)
    (N : V → Prop) (hN : ℒₛₑₜ-predicate N) (F : V → V) (hF : ℒₛₑₜ-function₁ F) :
    IsForcingRegular P R (forcingExistential P R N hN F hF) :=
  forcingClosure_regular hR (forcingClassUnion_subset P N hN F hF)

end ZFVP
