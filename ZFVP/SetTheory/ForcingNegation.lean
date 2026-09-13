import ZFVP.SetTheory.ForcingOrder

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingNegation (P R A : V) : V :=
  {p ∈ P ; ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → q ∉ A}

theorem mem_forcingNegation_iff (P R A p : V) :
    p ∈ forcingNegation P R A ↔ p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → q ∉ A := mem_sep_iff

instance forcingNegation_definable : ℒₛₑₜ-function₃[V] forcingNegation := by
  have h : ℒₛₑₜ-relation₄ (fun C P R A : V ↦
      ∀ p, p ∈ C ↔ p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → q ∉ A) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingNegation (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [mem_forcingNegation_iff]

theorem forcingNegation_subset (P R A : V) : forcingNegation P R A ⊆ P := by
  intro p hp
  exact (mem_sep_iff.mp hp).1

theorem forcingNegation_mono {P R A p q : V} (hR : IsForcingPreorder P R)
    (hp : p ∈ forcingNegation P R A) (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R) :
    q ∈ forcingNegation P R A := by
  obtain ⟨hpP, hh⟩ := (mem_forcingNegation_iff _ _ _ _).mp hp
  exact (mem_forcingNegation_iff _ _ _ _).mpr
    ⟨hq, fun r hr hrq ↦ hh r hr (hR.2.2 r hr q hq p hpP hrq hqp)⟩

theorem forcingNegation_disjoint {P R A p : V} (hR : IsForcingPreorder P R)
    (hp : p ∈ forcingNegation P R A) : p ∉ A := by
  obtain ⟨hpP, hh⟩ := (mem_forcingNegation_iff _ _ _ _).mp hp
  exact hh p hpP (hR.2.1 p hpP)

theorem exists_forcingNegation_of_not_mem {P R A p : V} (hp : p ∈ P) (hn : p ∉ A)
    (hclosed : ∀ q ∈ P,
      (∀ r ∈ P, ⟨r, q⟩ₖ ∈ R → ∃ s ∈ A, ⟨s, r⟩ₖ ∈ R) → q ∈ A) :
    ∃ q ∈ forcingNegation P R A, ⟨q, p⟩ₖ ∈ R := by
  classical
  by_contra hnone
  apply hn
  apply hclosed p hp
  intro q hq hqp
  by_contra hnoA
  apply hnone
  refine ⟨q, (mem_forcingNegation_iff _ _ _ _).mpr ⟨hq, ?_⟩, hqp⟩
  intro r _ hrq hrA
  exact hnoA ⟨r, hrA, hrq⟩

end ZFVP
