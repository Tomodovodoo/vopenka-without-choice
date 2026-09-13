import ZFVP.SetTheory.CohenProjectionHomogeneity
import ZFVP.SetTheory.AtomicForcingSubstitution

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Enlarging a finite support preserves the support property. -/
theorem IsCohenNameSupport.enlarge {τ E F : V} (hE : IsCohenNameSupport τ E)
    (hFω : F ⊆ (ω : V)) (hFf : IsInternallyFinite F) (hEF : E ⊆ F) :
    IsCohenNameSupport τ F :=
  ⟨hFω, hFf, fun π hπ hfix ↦ hE.2.2 π hπ (fun i hi ↦ hfix i (hEF i hi))⟩

private theorem support_union_left {τ E F : V} (hE : IsCohenNameSupport τ E)
    (hFω : F ⊆ (ω : V)) (hFf : IsInternallyFinite F) :
    IsCohenNameSupport τ (E ∪ F) := by
  apply hE.enlarge (fun i hi ↦ (mem_union_iff.mp hi).elim (hE.1 i) (hFω i))
    (internallyFinite_union hE.2.1 hFf)
  exact fun i hi ↦ mem_union_iff.mpr (Or.inl hi)

private theorem support_union_right {τ E F : V} (hF : IsCohenNameSupport τ F)
    (hEω : E ⊆ (ω : V)) (hEf : IsInternallyFinite E) :
    IsCohenNameSupport τ (E ∪ F) := by
  apply hF.enlarge (fun i hi ↦ (mem_union_iff.mp hi).elim (hEω i) (hF.1 i))
    (internallyFinite_union hEf hF.2.1)
  exact fun i hi ↦ mem_union_iff.mpr (Or.inr hi)

/-- Below an equality condition, membership uses only the member's support and the overlap
of the two container supports. This is the membership projection step of Jech 5.23. -/
theorem cohen_atomicMembership_overlap_restrict {E F D τ σ μ p q : V}
    (hτ : IsForcingName (cohenConditions (ω : V)) τ)
    (hσ : IsForcingName (cohenConditions (ω : V)) σ)
    (hμ : IsForcingName (cohenConditions (ω : V)) μ)
    (hE : IsCohenNameSupport τ E) (hF : IsCohenNameSupport σ F)
    (hD : IsCohenNameSupport μ D)
    (hp : p ∈ atomicEquality (cohenConditions (ω : V)) (cohenOrder (ω : V)) τ σ)
    (hqp : ⟨q, p⟩ₖ ∈ cohenOrder (ω : V))
    (hqμ : q ∈ atomicMembership (cohenConditions (ω : V)) (cohenOrder (ω : V)) μ τ) :
    p ∪ cohenConditionRestrict q (D ∪ (E ∩ F)) ∈ cohenConditions (ω : V) ∧
    p ∪ cohenConditionRestrict q (D ∪ (E ∩ F)) ∈
      atomicMembership (cohenConditions (ω : V)) (cohenOrder (ω : V)) μ τ := by
  have hR := (cohen_poset (ω : V)).1
  obtain ⟨hq, hpP, hpq⟩ := (pair_mem_cohenOrder _ _ _).mp hqp
  have hqeq := atomicEquality_mono hR hp hq hqp
  have hqσ := (atomicEquality_membership_iff hR hqeq μ).2.mp hqμ
  have hproj := cohen_atomicMembership_restrict hμ hσ
    (support_union_left hD hF.1 hF.2.1) (support_union_right hF hD.1 hD.2.1) hqσ
  let r := p ∪ cohenConditionRestrict q (D ∪ F)
  have hrq : r ⊆ q := by
    intro z hz
    exact (mem_union_iff.mp hz).elim (hpq z) (cohenConditionRestrict_subset q (D ∪ F) z)
  have hr : r ∈ cohenConditions (ω : V) := finitePartialFunction_subset hq hrq
  have hrp : ⟨r, p⟩ₖ ∈ cohenOrder (ω : V) :=
    (pair_mem_cohenOrder _ _ _).mpr ⟨hr, hpP, fun z hz ↦ mem_union_iff.mpr (Or.inl hz)⟩
  have hrproj : ⟨r, cohenConditionRestrict q (D ∪ F)⟩ₖ ∈ cohenOrder (ω : V) :=
    (pair_mem_cohenOrder _ _ _).mpr ⟨hr, cohenConditionRestrict_condition hq _,
      fun z hz ↦ mem_union_iff.mpr (Or.inr hz)⟩
  have hrσ := atomicMembership_mono hR hproj hr hrproj
  have hrτ := (atomicEquality_membership_iff hR (atomicEquality_mono hR hp hr hrp) μ).2.mpr hrσ
  have hrprojτ := cohen_atomicMembership_restrict hμ hτ
    (support_union_left hD hE.1 hE.2.1) (support_union_right hE hD.1 hD.2.1) hrτ
  let s := p ∪ cohenConditionRestrict q (D ∪ (E ∩ F))
  have hsq : s ⊆ q := by
    intro z hz
    exact (mem_union_iff.mp hz).elim (hpq z)
      (cohenConditionRestrict_subset q (D ∪ (E ∩ F)) z)
  have hs : s ∈ cohenConditions (ω : V) := finitePartialFunction_subset hq hsq
  refine ⟨hs, atomicMembership_mono hR hrprojτ hs ?_⟩
  apply (pair_mem_cohenOrder _ _ _).mpr
  refine ⟨hs, cohenConditionRestrict_condition hr _, ?_⟩
  intro z hz
  change z ∈ cohenConditionRestrict (p ∪ cohenConditionRestrict q (D ∪ F)) (D ∪ E) at hz
  simp only [cohenConditionRestrict, mem_sep_iff, mem_union_iff, mem_inter_iff] at hz ⊢
  tauto

end ZFVP

