import ZFVP.Syntax.CorrectDomainAbsoluteness

/-! Arbitrarily large rank stages satisfying each recursive correctness condition. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem hierarchy_isSequenceSupport {δ : V} [IsOrdinal δ]
    (hω : (ω : V) ∈ δ) (hlim : ∀ ξ ∈ δ, succ ξ ∈ δ) : IsSequenceSupport (hierarchy δ) := by
  have hu {x y : V} (hx : x ∈ hierarchy δ) (hy : y ∈ hierarchy δ) : x ∪ y ∈ hierarchy δ := by
    have h := sUnion_mem_hierarchy_limit hlim (pair_mem_hierarchy_limit hlim hx hy)
    simpa only [pair_eq_doubleton, ← union_def] using h
  exact {
    toIsTransitive := hierarchy_transitive δ
    omega_mem := ordinal_subset_hierarchy δ _ hω
    kpair_closed := fun _ hx _ hy ↦ kpair_mem_hierarchy_limit hlim hx hy
    doubleton_closed := fun _ hx _ hy ↦ by simpa only [pair_eq_doubleton] using pair_mem_hierarchy_limit hlim hx hy
    succ_closed := fun x hx ↦ by
      have hs : ({x} : V) ∈ hierarchy δ := by simpa using pair_mem_hierarchy_limit hlim hx hx
      change ({x} : V) ∪ x ∈ hierarchy δ
      exact hu hs hx
    union_closed := fun _ hx _ hy ↦ hu hx hy }

def domainWitnessRelation (k : ℕ) (p A : V) : Prop :=
  CorrectDomain k A ∧ kpair.π₂ p ∈ A ^ (kpair.π₁ (kpair.π₁ p)) ∧
    MembershipSatisfies A (kpair.π₁ (kpair.π₁ p)) (kpair.π₂ (kpair.π₁ p)) (kpair.π₂ p)

instance domainWitnessRelation_definable (k : ℕ) : ℒₛₑₜ-relation[V] (domainWitnessRelation k) := by
  unfold domainWitnessRelation
  definability

def correctDomainWitnessRelation : ℕ → V → V → Prop
  | 0 => fun _ _ ↦ False
  | k + 1 => mergeWitnessRelations (correctDomainWitnessRelation k) (domainWitnessRelation k)

theorem correctDomainWitnessRelation_definable (k : ℕ) : ℒₛₑₜ-relation[V] (correctDomainWitnessRelation k) := by
  induction k with
  | zero => change ℒₛₑₜ-relation[V] (fun _ _ ↦ False); definability
  | succ k ih => exact mergeWitnessRelations_definable _ _ ih (domainWitnessRelation_definable k)

theorem correctDomain_of_witnessClosed (k : ℕ) {δ : V} [IsOrdinal δ]
    (hω : (ω : V) ∈ δ) (hlim : ∀ ξ ∈ δ, succ ξ ∈ δ)
    (hc : IsWitnessClosed (correctDomainWitnessRelation k) δ) : CorrectDomain k (hierarchy δ) := by
  let hU := hierarchy_isSequenceSupport hω hlim
  induction k with
  | zero => exact hU
  | succ k ih =>
    obtain ⟨hprev, hw⟩ := mergeWitnessClosed hω hlim hc
    have hD := ih hprev
    refine ⟨hD, ?_⟩
    intro n hn φ hφ b hb hcode htyped htruth
    have hp := hU.kpair_closed _ (hU.kpair_closed _ hn _ hφ) _ hb
    obtain ⟨B, hB, hDB, hbB, hsB⟩ := hw ⟨⟨n, φ⟩ₖ, b⟩ₖ hp (by
      simpa only [domainWitnessRelation, kpair.π₁_kpair, kpair.π₂_kpair] using htruth)
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hbB hsB
    exact correctDomainCode_upward k hcode B (hierarchy δ) hDB hD (hU.transitive B hB) b hbB hsB

theorem correctDomain_witnessClosed_above (k : ℕ) (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
    (γ : V) [IsOrdinal γ] :
    ∃ δ : V, IsOrdinal δ ∧ γ ∈ δ ∧ (ω : V) ∈ δ ∧ (∀ ξ ∈ δ, succ ξ ∈ δ) ∧
      CorrectDomain k (hierarchy δ) ∧ IsWitnessClosed R δ := by
  have : IsOrdinal (γ ∪ (ω : V)) := ordinal_union_ordinal _ _
  obtain ⟨δ, hδ, hbig, hlim, hc⟩ := witnessClosed_above
    (mergeWitnessRelations (correctDomainWitnessRelation k) R)
    (mergeWitnessRelations_definable _ _ (correctDomainWitnessRelation_definable k) hR) (γ ∪ (ω : V))
  let := hδ
  have hγ : γ ∈ δ := ordinal_mem_of_subset_mem (fun x hx ↦ mem_union_iff.mpr (Or.inl hx)) hbig
  have hω : (ω : V) ∈ δ := ordinal_mem_of_subset_mem (fun x hx ↦ mem_union_iff.mpr (Or.inr hx)) hbig
  obtain ⟨hD, hR'⟩ := mergeWitnessClosed hω hlim hc
  exact ⟨δ, hδ, hγ, hω, hlim, correctDomain_of_witnessClosed k hω hlim hD, hR'⟩

theorem correctDomain_containing (k : ℕ) (X : V) :
    ∃ A : V, CorrectDomain k A ∧ X ∈ A := by
  obtain ⟨δ, hδ, hX, _, _, hD, _⟩ := correctDomain_witnessClosed_above k
    (fun _ _ : V ↦ False) (by definability) (rank X)
  let := hδ
  exact ⟨hierarchy δ, hD, (mem_hierarchy_iff_rank_mem X δ).mpr hX⟩

theorem correctDomain_formula_reflection (k : ℕ) {n : ℕ} (φ : SetTheorySemisentence n) (X : V) :
    ∃ δ : V, IsOrdinal δ ∧ X ∈ hierarchy δ ∧ (ω : V) ∈ δ ∧ (∀ ξ ∈ δ, succ ξ ∈ δ) ∧
      CorrectDomain k (hierarchy δ) ∧ IsFormulaAbsoluteAt φ δ := by
  obtain ⟨δ, hδ, hX, hω, hlim, hD, hc⟩ := correctDomain_witnessClosed_above k
    (reflectionWitnessRelation φ) (reflectionWitnessRelation_definable φ) (rank X)
  let := hδ
  exact ⟨δ, hδ, (mem_hierarchy_iff_rank_mem X δ).mpr hX, hω, hlim, hD,
    formula_absolute_of_witnessClosed hω hlim φ hc⟩

end ZFVP
