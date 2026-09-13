import ZFVP.SetTheory.ForcingNegation
import ZFVP.SetTheory.AtomicMembership

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsForcingDownwardClosed (P R A : V) : Prop :=
  ∀ p ∈ A, ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → q ∈ A

def IsForcingRegular (P R A : V) : Prop :=
  A ⊆ P ∧ IsForcingDownwardClosed P R A ∧
    ∀ p ∈ P, (∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ A, ⟨r, q⟩ₖ ∈ R) → p ∈ A

instance isForcingDownwardClosed_definable : ℒₛₑₜ-relation₃[V] IsForcingDownwardClosed := by
  unfold IsForcingDownwardClosed
  definability

instance isForcingRegular_definable : ℒₛₑₜ-relation₃[V] IsForcingRegular := by
  unfold IsForcingRegular
  definability

noncomputable def forcingClosure (P R A : V) : V :=
  {p ∈ P ; ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ A, ⟨r, q⟩ₖ ∈ R}

theorem mem_forcingClosure_iff (P R A p : V) : p ∈ forcingClosure P R A ↔
    p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ A, ⟨r, q⟩ₖ ∈ R := mem_sep_iff

instance forcingClosure_definable : ℒₛₑₜ-function₃[V] forcingClosure := by
  have h : ℒₛₑₜ-relation₄ (fun C P R A : V ↦ ∀ p, p ∈ C ↔
      p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ A, ⟨r, q⟩ₖ ∈ R) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingClosure (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [mem_forcingClosure_iff]

theorem forcingClosure_subset (P R A : V) : forcingClosure P R A ⊆ P := by
  intro p hp
  exact (mem_sep_iff.mp hp).1

theorem forcingClosure_downward {P R A : V} (hR : IsForcingPreorder P R) :
    IsForcingDownwardClosed P R (forcingClosure P R A) := by
  intro p hp q hq hqp
  obtain ⟨hpP, hh⟩ := (mem_forcingClosure_iff _ _ _ _).mp hp
  exact (mem_forcingClosure_iff _ _ _ _).mpr
    ⟨hq, fun r hr hrq ↦ hh r hr (hR.2.2 r hr q hq p hpP hrq hqp)⟩

theorem forcingClosure_regular {P R A : V} (hR : IsForcingPreorder P R) (hA : A ⊆ P) :
    IsForcingRegular P R (forcingClosure P R A) := by
  refine ⟨forcingClosure_subset _ _ _, forcingClosure_downward hR, ?_⟩
  intro p hp hd
  apply (mem_forcingClosure_iff _ _ _ _).mpr
  refine ⟨hp, ?_⟩
  intro q hq hqp
  obtain ⟨r, hr, hrq⟩ := hd q hq hqp
  obtain ⟨hrP, hh⟩ := (mem_forcingClosure_iff _ _ _ _).mp hr
  obtain ⟨v, hv, hvr⟩ := hh r hrP (hR.2.1 r hrP)
  exact ⟨v, hv, hR.2.2 v (hA v hv) r hrP q hq hvr hrq⟩

theorem subset_forcingClosure {P R A : V} (hR : IsForcingPreorder P R)
    (hAP : A ⊆ P) (hA : IsForcingDownwardClosed P R A) : A ⊆ forcingClosure P R A := by
  intro p hp
  exact (mem_forcingClosure_iff _ _ _ _).mpr
    ⟨hAP p hp, fun q hq hqp ↦ ⟨q, hA p hp q hq hqp, hR.2.1 q hq⟩⟩

theorem forcingClosure_eq {P R A : V} (hR : IsForcingPreorder P R) (hA : IsForcingRegular P R A) :
    forcingClosure P R A = A := by
  apply SetTheory.subset_antisymm ?_ (subset_forcingClosure hR hA.1 hA.2.1)
  intro p hp
  obtain ⟨hpP, hh⟩ := (mem_forcingClosure_iff _ _ _ _).mp hp
  exact hA.2.2 p hpP hh

theorem forcingNegation_regular {P R A : V} (hR : IsForcingPreorder P R)
    (hA : IsForcingDownwardClosed P R A) : IsForcingRegular P R (forcingNegation P R A) := by
  refine ⟨forcingNegation_subset _ _ _, fun _ hp _ hq hqp ↦ forcingNegation_mono hR hp hq hqp, ?_⟩
  intro p hp hd
  apply (mem_forcingNegation_iff _ _ _ _).mpr
  refine ⟨hp, ?_⟩
  intro q hq hqp hqA
  obtain ⟨r, hrN, hrq⟩ := hd q hq hqp
  exact forcingNegation_disjoint hR hrN
    (hA q hqA r (forcingNegation_subset _ _ _ r hrN) hrq)

theorem forcingRegular_inter {P R A B : V} (hA : IsForcingRegular P R A)
    (hB : IsForcingRegular P R B) : IsForcingRegular P R (A ∩ B) := by
  refine ⟨fun p hp ↦ hA.1 p (mem_inter_iff.mp hp).1, ?_, ?_⟩
  · intro p hp q hq hqp
    exact mem_inter_iff.mpr ⟨hA.2.1 p (mem_inter_iff.mp hp).1 q hq hqp,
      hB.2.1 p (mem_inter_iff.mp hp).2 q hq hqp⟩
  · intro p hp hd
    apply mem_inter_iff.mpr
    constructor
    · apply hA.2.2 p hp
      intro q hq hqp
      obtain ⟨r, hr, hrq⟩ := hd q hq hqp
      exact ⟨r, (mem_inter_iff.mp hr).1, hrq⟩
    · apply hB.2.2 p hp
      intro q hq hqp
      obtain ⟨r, hr, hrq⟩ := hd q hq hqp
      exact ⟨r, (mem_inter_iff.mp hr).2, hrq⟩

theorem forcingRegular_top (P R : V) : IsForcingRegular P R P :=
  ⟨subset_refl _, fun _ _ _ hq _ ↦ hq, fun _ hp _ ↦ hp⟩

theorem forcingRegular_empty {P R : V} (hR : IsForcingPreorder P R) : IsForcingRegular P R ∅ := by
  refine ⟨empty_subset _, ?_, ?_⟩
  · intro p hp
    exact False.elim (not_mem_empty hp)
  · intro p hp hd
    obtain ⟨q, hq, _⟩ := hd p hp (hR.2.1 p hp)
    exact False.elim (not_mem_empty hq)

theorem atomicEquality_regular {P R : V} (hR : IsForcingPreorder P R) (σ τ : V) :
    IsForcingRegular P R (atomicEquality P R σ τ) :=
  ⟨atomicEquality_subset _ _ _ _, fun _ hp _ hq hqp ↦ atomicEquality_mono hR hp hq hqp,
    fun _ hp hd ↦ atomicEquality_dense hR hp hd⟩

theorem atomicMembership_regular {P R : V} (hR : IsForcingPreorder P R) (σ τ : V) :
    IsForcingRegular P R (atomicMembership P R σ τ) :=
  ⟨atomicMembership_subset _ _ _ _, fun _ hp _ hq hqp ↦ atomicMembership_mono hR hp hq hqp,
    fun _ hp hd ↦ atomicMembership_dense hR hp hd⟩

end ZFVP
