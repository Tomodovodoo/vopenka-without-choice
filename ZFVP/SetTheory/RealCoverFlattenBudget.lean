import ZFVP.SetTheory.RealCoverFlattenRow
import ZFVP.SetTheory.NaturalPairing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def realCoverFlatten (cov e : V) : V :=
  definableGraph (ω : V) (fun j ↦ (cov ‘ (kpair.π₁ (e ‘ j))) ‘ (kpair.π₂ (e ‘ j))) (by definability)

instance realCoverFlatten_definable : ℒₛₑₜ-function₂[V] realCoverFlatten := by
  have h : ℒₛₑₜ-relation₃[V] (fun d cov e ↦ ∀ p, p ∈ d ↔ ∃ j ∈ (ω : V),
      p = ⟨j, (cov ‘ (kpair.π₁ (e ‘ j))) ‘ (kpair.π₂ (e ‘ j))⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [realCoverFlatten, mem_definableGraph_iff]

theorem realCoverFlatten_value (cov e : V) {j : V} (hj : j ∈ (ω : V)) :
    (realCoverFlatten cov e) ‘ j = (cov ‘ (kpair.π₁ (e ‘ j))) ‘ (kpair.π₂ (e ‘ j)) :=
  value_definableGraph _ _ _ hj

theorem realCoverFlatten_mem {cov e : V}
    (hcov : cov ∈ ((realBasicCodes V) ^ (ω : V)) ^ (ω : V))
    (he : e ∈ ((ω : V) ×ˢ (ω : V)) ^ (ω : V)) :
    realCoverFlatten cov e ∈ (realBasicCodes V) ^ (ω : V) := by
  apply definableGraph_mem_function_of_mapsTo
  intro j hj
  obtain ⟨i, hi, k, hk, hpair⟩ := mem_prod_iff.mp (function_value_mem he hj)
  rw [hpair, kpair.π₁_kpair, kpair.π₂_kpair]
  exact function_value_mem (function_value_mem hcov hi) hk

theorem flattenFinite_natural_bound (F : V → V) (hF : ℒₛₑₜ-function₁[V] F)
    {k : V} (hk : k ∈ (ω : V)) (hFn : ∀ j ∈ k, F j ∈ (ω : V)) :
    ∃ N ∈ (ω : V), ∀ j ∈ k, F j ∈ N := by
  have hfin : IsInternallyFinite (repl F hF k) := internallyFinite_repl _ _
    (internallyFinite_of_cardLE_natural hk (CardLE.refl _))
  have hsub : repl F hF k ⊆ (ω : V) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := (repl_spec hF).mp hx
    exact hFn j hj
  obtain ⟨N, hN, hBN⟩ := internallyFinite_naturals_bounded hfin hsub
  exact ⟨N, hN, fun j hj ↦ hBN _ ((repl_spec hF).mpr ⟨j, hj, rfl⟩)⟩

theorem realCoverFlatten_cost_bound {cov e b B : V}
    (hcov : cov ∈ ((realBasicCodes V) ^ (ω : V)) ^ (ω : V))
    (he : e ∈ ((ω : V) ×ˢ (ω : V)) ^ (ω : V)) (hei : Injective e)
    (hb : b ∈ (internalRationals V) ^ (ω : V)) (hB : B ∈ internalRationals V)
    (hrow : ∀ i ∈ (ω : V), ∀ n ∈ (ω : V), ¬InternalRationalLT (b ‘ i) (realCoverCost (cov ‘ i) n))
    (hbudget : ∀ n ∈ (ω : V), ¬InternalRationalLT B (rationalPartialSum b n)) :
    ∀ k ∈ (ω : V), ¬InternalRationalLT B (realCoverCost (realCoverFlatten cov e) k) := by
  intro k hk
  have hd := realCoverFlatten_mem hcov he
  have hcoord : ∀ j ∈ k, kpair.π₁ (e ‘ j) ∈ (ω : V) ∧ kpair.π₂ (e ‘ j) ∈ (ω : V) := by
    intro j hj
    obtain ⟨i, hi, l, hl, heq⟩ := mem_prod_iff.mp (function_value_mem he (IsTransitive.ω.transitive k hk j hj))
    simpa only [heq, kpair.π₁_kpair, kpair.π₂_kpair] using And.intro hi hl
  obtain ⟨M, hM, hrows⟩ := flattenFinite_natural_bound (fun j ↦ kpair.π₁ (e ‘ j)) (by definability) hk
    (fun j hj ↦ (hcoord j hj).1)
  obtain ⟨N, hN, hcols⟩ := flattenFinite_natural_bound (fun j ↦ kpair.π₂ (e ‘ j)) (by definability) hk
    (fun j hj ↦ (hcoord j hj).2)
  let w := realCoverLengths (realCoverFlatten cov e)
  have hw : ∀ j ∈ (ω : V), w ‘ j ∈ internalRationals V := fun j hj ↦ realCoverLengths_mem hd hj
  have hbmem : ∀ j ∈ (ω : V), b ‘ j ∈ internalRationals V := fun j hj ↦ function_value_mem hb hj
  have htot : ∀ i ∈ (ω : V), ¬InternalRationalLT (b ‘ i) ((flattenRowTotals e w k) ‘ i) := by
    intro i hi
    have hcovi := function_value_mem hcov hi
    have hu : ∀ j ∈ (ω : V), (realCoverLengths (cov ‘ i)) ‘ j ∈ internalRationals V :=
      fun j hj ↦ realCoverLengths_mem hcovi hj
    have hupos : ∀ j ∈ (ω : V), ¬InternalRationalLT ((realCoverLengths (cov ‘ i)) ‘ j) (rationalZero V) :=
      fun j hj ↦ realCoverLengths_nonnegative hcovi hj
    have hmatch : ∀ j ∈ k, kpair.π₁ (e ‘ j) = i → w ‘ j = (realCoverLengths (cov ‘ i)) ‘ (kpair.π₂ (e ‘ j)) := by
      intro j hj hji
      have hjω := IsTransitive.ω.transitive k hk j hj
      rw [realCoverLengths, value_definableGraph _ _ _ (hcoord j hj).2]
      change (realCoverLengths (realCoverFlatten cov e)) ‘ j = _
      rw [realCoverLengths, value_definableGraph _ _ _ hjω, realCoverFlatten_value _ _ hjω, hji]
    have hr := flattenRow_sum_le he hei hk hN hw hu hupos hcols hmatch
    rw [flattenRowTotals_value _ _ _ hi]
    exact le_trans
      (show (⟨rationalPartialSum (rationalMaskedWeights w (flattenRowIndices e i)) k,
        rationalPartialSum_mem (rationalMaskedWeights_mem hw _) k hk⟩ : InternalRational V) ≤
        ⟨realCoverCost (cov ‘ i) N, realCoverCost_mem hcovi N hN⟩ from hr)
      (show (⟨realCoverCost (cov ‘ i) N, realCoverCost_mem hcovi N hN⟩ : InternalRational V) ≤
        ⟨b ‘ i, hbmem i hi⟩ from hrow i hi N hN)
  have hsum := rationalFiniteSum_pointwise_le (flattenRowTotals_mem hw hk e) hbmem htot M hM
  rw [flattenRowTotals_partition hk hM hw hrows] at hsum
  exact le_trans
    (show (⟨realCoverCost (realCoverFlatten cov e) k, realCoverCost_mem hd k hk⟩ : InternalRational V) ≤
      ⟨rationalPartialSum b M, rationalPartialSum_mem hbmem M hM⟩ from hsum)
    (show (⟨rationalPartialSum b M, rationalPartialSum_mem hbmem M hM⟩ : InternalRational V) ≤ ⟨B, hB⟩ from hbudget M hM)

noncomputable def realCoverFamilyUnion (cov : V) : V :=
  {x ∈ dedekindReals V ; ∃ i ∈ (ω : V), ∃ j ∈ (ω : V),
    x ∈ realInterval (kpair.π₁ ((cov ‘ i) ‘ j)) (kpair.π₂ ((cov ‘ i) ‘ j))}

theorem mem_realCoverFamilyUnion_iff (cov x : V) : x ∈ realCoverFamilyUnion cov ↔
    x ∈ dedekindReals V ∧ ∃ i ∈ (ω : V), ∃ j ∈ (ω : V),
      x ∈ realInterval (kpair.π₁ ((cov ‘ i) ‘ j)) (kpair.π₂ ((cov ‘ i) ‘ j)) := by simp [realCoverFamilyUnion]

instance realCoverFamilyUnion_definable : ℒₛₑₜ-function₁[V] realCoverFamilyUnion := by
  have h : ℒₛₑₜ-relation[V] (fun A cov ↦ ∀ x, x ∈ A ↔ x ∈ dedekindReals V ∧
      ∃ i ∈ (ω : V), ∃ j ∈ (ω : V), x ∈ realInterval (kpair.π₁ ((cov ‘ i) ‘ j)) (kpair.π₂ ((cov ‘ i) ‘ j))) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [mem_realCoverFamilyUnion_iff]

/-- Countably many genuine interval covers flatten with exactly the supplied total
budget. The enumeration is bijective, so no padding or choice principle is required. -/
theorem realCoverFamily_flatten_budget {cov b B : V}
    (hcov : cov ∈ ((realBasicCodes V) ^ (ω : V)) ^ (ω : V))
    (hb : b ∈ (internalRationals V) ^ (ω : V)) (hB : B ∈ internalRationals V)
    (hrow : ∀ i ∈ (ω : V), ∀ n ∈ (ω : V), ¬InternalRationalLT (b ‘ i) (realCoverCost (cov ‘ i) n))
    (hbudget : ∀ n ∈ (ω : V), ¬InternalRationalLT B (rationalPartialSum b n)) :
    ∃ d, IsRealIntervalCover d (realCoverFamilyUnion cov) ∧
      ∀ n ∈ (ω : V), ¬InternalRationalLT B (realCoverCost d n) := by
  have hωprod : (ω : V) ≤# ((ω : V) ×ˢ (ω : V)) := by
    apply cardLE_of_injective_map (fun i ↦ ⟨i, (0 : V)⟩ₖ) (by definability)
    · intro i hi
      exact kpair_mem_iff.mpr ⟨hi, by simp⟩
    · intro i hi j hj he
      exact (kpair_inj he).1
  obtain ⟨e, he, hei, her⟩ := exists_bijection_of_cardEQ (And.intro hωprod omega_prod_cardLE_omega)
  have : IsFunction e := IsFunction.of_mem he
  refine ⟨realCoverFlatten cov e, ⟨realCoverFlatten_mem hcov he, ?_⟩,
    realCoverFlatten_cost_bound hcov he hei hb hB hrow hbudget⟩
  intro x hx
  obtain ⟨_, i, hi, j, hj, hxij⟩ := (mem_realCoverFamilyUnion_iff _ _).mp hx
  have hp : ⟨i, j⟩ₖ ∈ range e := her.symm ▸ kpair_mem_iff.mpr ⟨hi, hj⟩
  obtain ⟨k, hk⟩ := mem_range_iff.mp hp
  have hkω : k ∈ (ω : V) := by simpa only [domain_eq_of_mem_function he] using mem_domain_of_kpair_mem hk
  refine ⟨k, hkω, ?_⟩
  rw [realCoverFlatten_value _ _ hkω, value_eq_of_kpair_mem hk, kpair.π₁_kpair, kpair.π₂_kpair]
  exact hxij

end ZFVP
