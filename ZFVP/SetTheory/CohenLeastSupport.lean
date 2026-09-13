import ZFVP.SetTheory.CohenSupportIntersection

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- An internally finite coordinate support of a ground Cohen name. -/
def IsCohenNameSupport (τ E : V) : Prop :=
  E ⊆ (ω : V) ∧ IsInternallyFinite E ∧
    ∀ π, IsInternalPermutation (ω : V) π → (∀ i ∈ E, π ‘ i = i) →
      nameAction (cohenPermutation (ω : V) π) τ = τ

instance isCohenNameSupport_definable : ℒₛₑₜ-relation[V] IsCohenNameSupport := by
  unfold IsCohenNameSupport
  definability

theorem IsCohenNameSupport.inter {τ E F : V}
    (hτ : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) τ)
    (hE : IsCohenNameSupport τ E) (hF : IsCohenNameSupport τ F) :
    IsCohenNameSupport τ (E ∩ F) :=
  ⟨fun i hi ↦ hE.1 i (mem_inter_iff.mp hi).1,
    internallyFinite_subset hE.2.1 (fun _ hi ↦ (mem_inter_iff.mp hi).1),
    cohenName_support_intersection hτ hE.1 hE.2.1 hF.1 hF.2.1 hE.2.2 hF.2.2⟩

/-- Every hereditarily symmetric ground Cohen name has a least internally finite support.
The finite induction removes each coordinate that some finite support omits. -/
theorem cohenName_exists_least_support {τ : V}
    (hτ : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) τ) :
    ∃ E, IsCohenNameSupport τ E ∧ ∀ F, IsCohenNameSupport τ F → E ⊆ F := by
  classical
  obtain ⟨D, hDω, hDf, hDs⟩ := cohenName_finiteSupport hτ
  have hD : IsCohenNameSupport τ D := ⟨hDω, hDf, hDs⟩
  have key : ∀ A : V, IsInternallyFinite A →
      ∃ E, IsCohenNameSupport τ E ∧ E ⊆ D ∧
        ∀ i ∈ A, i ∈ E → ∀ F, IsCohenNameSupport τ F → i ∈ F := by
    apply internallyFinite_induction (fun A ↦
      ∃ E, IsCohenNameSupport τ E ∧ E ⊆ D ∧
        ∀ i ∈ A, i ∈ E → ∀ F, IsCohenNameSupport τ F → i ∈ F) (by definability)
    · exact ⟨D, hD, subset_refl D, fun i hi ↦ (not_mem_empty hi).elim⟩
    · intro A a ih
      obtain ⟨E, hE, hED, hmin⟩ := ih
      by_cases hall : ∀ F, IsCohenNameSupport τ F → a ∈ F
      · refine ⟨E, hE, hED, ?_⟩
        intro i hi hiE F hF
        rcases mem_insert.mp hi with rfl | hi
        · exact hall F hF
        · exact hmin i hi hiE F hF
      · push Not at hall
        obtain ⟨F, hF, haF⟩ := hall
        refine ⟨E ∩ F, hE.inter hτ hF,
          fun i hi ↦ hED i (mem_inter_iff.mp hi).1, ?_⟩
        intro i hi hiEF K hK
        rcases mem_insert.mp hi with rfl | hi
        · exact (haF (mem_inter_iff.mp hiEF).2).elim
        · exact hmin i hi (mem_inter_iff.mp hiEF).1 K hK
  obtain ⟨E, hE, hED, hmin⟩ := key D hDf
  exact ⟨E, hE, fun F hF i hi ↦ hmin i (hED i hi) hi F hF⟩

/-- The canonical support consists of the natural coordinates occurring in every finite support. -/
noncomputable def cohenNameLeastSupport (τ : V) : V :=
  {i ∈ (ω : V) ; ∀ F, IsCohenNameSupport τ F → i ∈ F}

instance cohenNameLeastSupport_definable : ℒₛₑₜ-function₁[V] cohenNameLeastSupport := by
  have h : ℒₛₑₜ-relation[V] (fun E τ ↦
      ∀ i, i ∈ E ↔ i ∈ (ω : V) ∧ ∀ F, IsCohenNameSupport τ F → i ∈ F) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = cohenNameLeastSupport (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [cohenNameLeastSupport, mem_sep_iff]

theorem cohenNameLeastSupport_subset {τ F : V} (hF : IsCohenNameSupport τ F) :
    cohenNameLeastSupport τ ⊆ F :=
  fun _ hi ↦ (mem_sep_iff.mp hi).2 F hF

theorem cohenNameLeastSupport_isSupport {τ : V}
    (hτ : IsHereditarilySymmetricName (cohenConditions (ω : V))
      (cohenGroup (ω : V)) (cohenFilter (ω : V)) τ) :
    IsCohenNameSupport τ (cohenNameLeastSupport τ) := by
  obtain ⟨E, hE, hmin⟩ := cohenName_exists_least_support hτ
  have he : cohenNameLeastSupport τ = E := by
    apply SetTheory.subset_antisymm (cohenNameLeastSupport_subset hE)
    intro i hi
    exact mem_sep_iff.mpr ⟨hE.1 i hi, fun F hF ↦ hmin F hF i hi⟩
  rwa [he]

end ZFVP
