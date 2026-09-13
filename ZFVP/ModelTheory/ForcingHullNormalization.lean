import ZFVP.ModelTheory.ForcingHullImage

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingNameEqualityTable (P R D E : V) : V :=
  {z ∈ (P ×ˢ D) ×ˢ E ; kpair.π₁ (kpair.π₁ z) ∈
    atomicEquality P R (kpair.π₂ (kpair.π₁ z)) (kpair.π₂ z)}

instance forcingNameEqualityTable_definable (P R : V) :
    ℒₛₑₜ-function₂[V] (forcingNameEqualityTable P R) := by
  have hh : ℒₛₑₜ-relation₃[V] (fun T D E ↦ ∀ z, z ∈ T ↔ z ∈ (P ×ˢ D) ×ˢ E ∧
      kpair.π₁ (kpair.π₁ z) ∈ atomicEquality P R (kpair.π₂ (kpair.π₁ z)) (kpair.π₂ z)) := by
    definability
  apply Language.Definable.of_iff hh
  intro v
  change v 0 = forcingNameEqualityTable P R (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [forcingNameEqualityTable, mem_sep_iff]

theorem mem_forcingNameEqualityTable (P R D E p τ ν : V) :
    ⟨⟨p, τ⟩ₖ, ν⟩ₖ ∈ forcingNameEqualityTable P R D E ↔
      p ∈ P ∧ τ ∈ D ∧ ν ∈ E ∧ p ∈ atomicEquality P R τ ν := by
  simp only [forcingNameEqualityTable, mem_sep_iff, kpair_mem_iff,
    kpair.π₁_kpair, kpair.π₂_kpair]
  tauto

namespace ForcingContext

theorem hull_name_normalize (A : ForcingContext V) {X B D E : V} [IsTransitive B]
    (hX : IsElementaryInclusion X B) (hPX : A.P ⊆ X)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) (hE : ∀ τ ∈ E, IsForcingName A.P τ)
    (hT : forcingNameEqualityTable A.P A.R D E ∈ X)
    {τ : V} (hτX : τ ∈ X) (hτD : τ ∈ D)
    (hx : A.ofName ⟨τ, hD τ hτD⟩ ∈ range (A.evaluationGraph E hE)) :
    ∃ ν : V, ∃ hν : ν ∈ X ∩ E,
      A.ofName ⟨τ, hD τ hτD⟩ = A.ofName ⟨ν, hE ν (mem_inter_iff.mp hν).2⟩ := by
  obtain ⟨ν, hν, heq⟩ := (A.mem_range_evaluationGraph_iff E hE _).mp hx
  obtain ⟨p, hpG, hp⟩ := (forcingQuotientMk_eq_iff A.P A.R A.G A.order A.generic.1
    ⟨τ, hD τ hτD⟩ ⟨ν, hE ν hν⟩).mp heq
  have hpP := A.generic.1.1 p hpG
  have hrow := (mem_forcingNameEqualityTable A.P A.R D E p τ ν).mpr ⟨hpP, hτD, hν, hp⟩
  have hkeyB := (kpair_components_mem_transitive
    ((inferInstance : IsTransitive B).mem_trans hrow (hX.subset _ hT))).1
  have hkeyX := hX.kpair_mem (hPX p hpP) hτX hkeyB
  obtain ⟨σ, hσX, hrow⟩ := hX.table_fiber_witness hT hkeyX ⟨ν, hrow⟩
  obtain ⟨_, _, hσE, hpσ⟩ := (mem_forcingNameEqualityTable A.P A.R D E p τ σ).mp hrow
  refine ⟨σ, mem_inter_iff.mpr ⟨hσX, hσE⟩, ?_⟩
  exact (forcingQuotientMk_eq_iff A.P A.R A.G A.order A.generic.1 _ _).mpr ⟨p, hpG, hpσ⟩

theorem hullImage_normalize (A : ForcingContext V) {X B D E : V} [IsTransitive B]
    (hX : IsElementaryInclusion X B) (hPX : A.P ⊆ X)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) (hE : ∀ τ ∈ E, IsForcingName A.P τ)
    (hT : forcingNameEqualityTable A.P A.R D E ∈ X) :
    A.hullImage D hD X ∩ range (A.evaluationGraph E hE) ⊆ A.hullImage E hE X := by
  intro x hx
  obtain ⟨τ, hτ, rfl⟩ := (A.mem_hullImage_iff D hD X x).mp (mem_inter_iff.mp hx).1
  obtain ⟨ν, hν, he⟩ := A.hull_name_normalize hX hPX hD hE hT
    (mem_inter_iff.mp hτ).1 (mem_inter_iff.mp hτ).2 (mem_inter_iff.mp hx).2
  exact (A.mem_hullImage_iff E hE X _).mpr ⟨ν, hν, he⟩

theorem lowRank_hullImage_normalize (A : ForcingContext V) {X B D η : V} [IsTransitive B]
    (hX : IsElementaryInclusion X B) (hPX : A.P ⊆ X)
    (hD : ∀ τ ∈ D, IsForcingName A.P τ) (hη : Cn 1 η) (hP : A.P ∈ hierarchy η)
    (hT : forcingNameEqualityTable A.P A.R D (lowRankNameSet A.P η) ∈ X) :
    A.hullImage D hD X ∩ hierarchy (A.check η) ⊆
      A.hullImage (lowRankNameSet A.P η) (A.lowRankNameSet_names η) X := by
  rw [← A.lowRankEvaluation_range hη hP]
  exact A.hullImage_normalize hX hPX hD (A.lowRankNameSet_names η) hT

end ForcingContext
end ZFVP
