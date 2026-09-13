import ZFVP.ModelTheory.CohenLeastSupportPool
import ZFVP.ModelTheory.CohenAssignmentRanges
import ZFVP.SetTheory.CohenSupportTransport

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CohenModel

variable {G : Set V}
  (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G)

theorem least_support_assignment_range_subset {D E : V} (hD : IsCohenSupportPool D)
    (hEω : E ⊆ (ω : V)) (hEf : IsInternallyFinite E)
    {x : (cohenContext (ω : V) G hG).Model}
    (hmin : ∀ (σ : (cohenContext (ω : V) G hG).Name) F,
      (cohenContext (ω : V) G hG).ofName σ = x → IsCohenNameSupport σ.val F → E ⊆ F)
    {j a : (cohenContext (ω : V) G hG).Model}
    (hj : j ∈ (cohenContext (ω : V) G hG).check D)
    (hax : ⟨a, x⟩ₖ ∈ (orbitFamily hG D hD) ‘ j) :
    range (finiteAssignmentValue hG E hEω hEf (identity (ω : V)) (internalPermutation_identity _)) ⊆
      range a := by
  let S := cohenContext (ω : V) G hG
  obtain ⟨z, hz, rfl⟩ := (S.mem_check_iff D j).mp hj
  rw [orbitFamily_value hG hD hz] at hax
  obtain ⟨b, hb, he⟩ := (mem_orbitEvaluation_iff hG _ _ _ _ _).mp hax
  obtain ⟨ha, hx⟩ := kpair_iff.mp he
  rw [ha]
  apply (finiteAssignmentValue_identity_range_subset_iff hG E hEω hEf
    (kpair.π₂ z) (hD z hz).2.1 (hD z hz).2.2.1 b hb).mpr
  let σ : S.Name := ⟨nameAction (cohenPermutation (ω : V) b) (kpair.π₁ z),
    hereditarilySymmetric_nameAction S.group S.normal
      ((mem_cohenGroup (ω : V) _).mpr ⟨b, hb, rfl⟩) (hD z hz).1⟩
  exact hmin σ _ hx.symm ((hD z hz).2.image (hD z hz).1.1 hb)

theorem least_support_assignment_in_family {D E : V} (hD : IsCohenSupportPool D)
    (ν : (cohenContext (ω : V) G hG).Name) (hE : IsCohenNameSupport ν.val E)
    (hνD : ⟨ν.val, E⟩ₖ ∈ D) :
    ⟨finiteAssignmentValue hG E hE.1 hE.2.1 (identity (ω : V)) (internalPermutation_identity _),
      (cohenContext (ω : V) G hG).ofName ν⟩ₖ ∈
      (orbitFamily hG D hD) ‘ ((cohenContext (ω : V) G hG).check ⟨ν.val, E⟩ₖ) := by
  rw [orbitFamily_value hG hD hνD]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  change ⟨finiteAssignmentValue hG E hE.1 hE.2.1 (identity (ω : V)) (internalPermutation_identity _),
      (cohenContext (ω : V) G hG).ofName ν⟩ₖ ∈ orbitEvaluation hG E hE.1 hE.2.1 ν
  apply (mem_orbitEvaluation_iff hG E hE.1 hE.2.1 ν _).mpr
  refine ⟨identity (ω : V), internalPermutation_identity _, ?_⟩
  rw [orbitValue_identity]

theorem orbitFamily_inputs_fixed_finite_domain {D : V} (hD : IsCohenSupportPool D)
    {j : (cohenContext (ω : V) G hG).Model}
    (hj : j ∈ (cohenContext (ω : V) G hG).check D) :
    ∃ B : (cohenContext (ω : V) G hG).Model, IsInternallyFinite B ∧
      ∀ a ∈ domain ((orbitFamily hG D hD) ‘ j), IsFunction a ∧ domain a = B := by
  let S := cohenContext (ω : V) G hG
  obtain ⟨z, hz, rfl⟩ := (S.mem_check_iff D j).mp hj
  refine ⟨S.check (kpair.π₂ z), S.checkEmbedding.map_internallyFinite (hD z hz).2.2.1, ?_⟩
  intro a ha
  obtain ⟨x, hax⟩ := mem_domain_iff.mp ha
  rw [orbitFamily_value hG hD hz] at hax
  obtain ⟨b, hb, he⟩ := (mem_orbitEvaluation_iff hG _ _ _ _ _).mp hax
  rw [(kpair_iff.mp he).1]
  have hf := finiteAssignmentValue_function hG (kpair.π₂ z) (hD z hz).2.1 (hD z hz).2.2.1 b hb
  exact ⟨IsFunction.of_mem hf, domain_eq_of_mem_function hf⟩

end CohenModel

end ZFVP
