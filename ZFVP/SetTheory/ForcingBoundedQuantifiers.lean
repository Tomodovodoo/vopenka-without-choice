import ZFVP.SetTheory.ForcingImplication
import ZFVP.SetTheory.ForcingQuantifiers
import ZFVP.SetTheory.AtomicForcingSubstitution
import ZFVP.SetTheory.ForcingNames

/-! Bounded forcing quantifiers range over the subnames of their bound. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingBoundedExistential_iff {P R τ p : V} (hR : IsForcingPreorder P R)
    (N : V → Prop) (hN : ℒₛₑₜ-predicate N) (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (hτ : IsForcingName P τ) (hsub : ∀ υ s, ⟨υ, s⟩ₖ ∈ τ → N υ)
    (hreg : ∀ x, IsForcingRegular P R (F x))
    (hcongr : ∀ x y r, r ∈ P → r ∈ atomicEquality P R x y → (r ∈ F x ↔ r ∈ F y)) :
    p ∈ forcingExistential P R N hN (fun x ↦ atomicMembership P R x τ ∩ F x) (by definability) ↔
      p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
        ∃ υ s, ⟨υ, s⟩ₖ ∈ τ ∧ ⟨r, s⟩ₖ ∈ R ∧ r ∈ F υ := by
  rw [forcingExistential, mem_forcingClosure_iff]
  constructor
  · rintro ⟨hp, hd⟩
    refine ⟨hp, ?_⟩
    intro q hq hqp
    obtain ⟨r, hr, hrq⟩ := hd q hq hqp
    obtain ⟨hrP, x, _, hrx⟩ := (mem_forcingClassUnion_iff _ _ _ _ _ _).mp hr
    obtain ⟨hrmem, hrF⟩ := mem_inter_iff.mp hrx
    obtain ⟨t, ht, htr, υ, s, hυ, hts, he⟩ :=
      ((mem_atomicMembership_iff _ _ _ _ _).mp hrmem).2 r hrP (hR.2.1 r hrP)
    exact ⟨t, ht, hR.2.2 t ht r hrP q hq htr hrq, υ, s, hυ, hts,
      (hcongr x υ t ht he).mp ((hreg x).2.1 r hrF t ht htr)⟩
  · rintro ⟨hp, hd⟩
    refine ⟨hp, ?_⟩
    intro q hq hqp
    obtain ⟨r, hr, hrq, υ, s, hυ, hrs, hrF⟩ := hd q hq hqp
    have hs := forcingName_condition hτ hυ
    have hrmem := atomicMembership_mono hR (atomicMembership_of_pair hR hs hυ) hr hrs
    exact ⟨r, (mem_forcingClassUnion_iff _ _ _ _ _ _).mpr
      ⟨hr, υ, hsub υ s hυ, mem_inter_iff.mpr ⟨hrmem, hrF⟩⟩, hrq⟩

theorem forcingBoundedUniversal_iff {P R τ p : V} (hR : IsForcingPreorder P R)
    (N : V → Prop) (hN : ℒₛₑₜ-predicate N) (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (hτ : IsForcingName P τ) (hsub : ∀ υ s, ⟨υ, s⟩ₖ ∈ τ → N υ)
    (hreg : ∀ x, IsForcingRegular P R (F x))
    (hcongr : ∀ x y r, r ∈ P → r ∈ atomicEquality P R x y → (r ∈ F x ↔ r ∈ F y)) :
    p ∈ forcingClassIntersection P N hN
      (fun x ↦ forcingClosure P R (forcingNegation P R (atomicMembership P R x τ) ∪ F x)) (by definability) ↔
      p ∈ P ∧ ∀ υ s, ⟨υ, s⟩ₖ ∈ τ → ∀ q ∈ P,
        ⟨q, p⟩ₖ ∈ R → ⟨q, s⟩ₖ ∈ R → q ∈ F υ := by
  rw [mem_forcingClassIntersection_iff]
  constructor
  · rintro ⟨hp, hall⟩
    refine ⟨hp, ?_⟩
    intro υ s hυ q hq hqp hqs
    have hImp := (forcingImplication_iff hR (atomicMembership_regular hR υ τ) (hreg υ)).mp
      (hall υ (hsub υ s hυ))
    have hs := forcingName_condition hτ hυ
    exact hImp.2 q hq hqp (atomicMembership_mono hR (atomicMembership_of_pair hR hs hυ) hq hqs)
  · rintro ⟨hp, hall⟩
    refine ⟨hp, ?_⟩
    intro x _
    apply (forcingImplication_iff hR (atomicMembership_regular hR x τ) (hreg x)).mpr
    refine ⟨hp, ?_⟩
    intro q hq hqp hqx
    apply (hreg x).2.2 q hq
    intro r hr hrq
    obtain ⟨t, ht, htr, υ, s, hυ, hts, he⟩ :=
      ((mem_atomicMembership_iff _ _ _ _ _).mp hqx).2 r hr hrq
    have htq := hR.2.2 t ht r hr q hq htr hrq
    have htp := hR.2.2 t ht q hq p hp htq hqp
    exact ⟨t, (hcongr x υ t ht he).mpr (hall υ s hυ t ht htp hts), htr⟩

end ZFVP
