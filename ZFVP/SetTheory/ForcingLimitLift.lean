import ZFVP.SetTheory.DirectLimitSplice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingThreadSplice_parameters_definable (θ π L i : V) :
    ℒₛₑₜ-function₂[V] (fun f b ↦ forcingThreadSplice θ π L f i b) := by
  classical
  have h : ℒₛₑₜ-relation₃ (fun g f b : V ↦ ∀ z, z ∈ g ↔ ∃ j ∈ θ,
    (j ∈ i ∧ z = ⟨j, (π ‘ ⟨j, i⟩ₖ) ‘ b⟩ₖ) ∨
    (j ∉ i ∧ z = ⟨j, (L ‘ ⟨i, j⟩ₖ) ‘ ⟨f ‘ j, b⟩ₖ⟩ₖ)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingThreadSplice θ π L (v 1) i (v 2) ↔ _
  rw [mem_ext_iff]
  apply forall_congr'
  intro z
  rw [forcingThreadSplice, mem_definableGraph_iff]
  apply iff_congr Iff.rfl
  apply exists_congr
  intro j
  by_cases hj : j ∈ i <;> simp [forcingSpliceValue, hj]

/-- The new column of stronger-lift functions at a limit stage. -/
noncomputable def forcingLimitLift (C A θ π L i : V) : V :=
  definableGraph (C ×ˢ A)
    (fun z ↦ forcingThreadSplice θ π L (kpair.π₁ z) i (kpair.π₂ z)) (by
      exact Language.DefinableFunction₂.comp
        (F := fun f b ↦ forcingThreadSplice θ π L f i b)
        (by definability) (by definability))

theorem forcingLimitLift_value {C A θ π L i f b : V} (hf : f ∈ C) (hb : b ∈ A) :
    (forcingLimitLift C A θ π L i) ‘ ⟨f, b⟩ₖ = forcingThreadSplice θ π L f i b := by
  rw [forcingLimitLift, value_definableGraph _ _ _ (mem_prod_iff.mpr ⟨f, hf, b, hb, rfl⟩)]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]

theorem forcingLimitLift_commute {C A θ π L i j f b : V}
    (hf : f ∈ C) (hb : b ∈ A) (hj : j ∈ θ) (hij : i ⊆ j) :
    ((forcingLimitLift C A θ π L i) ‘ ⟨f, b⟩ₖ) ‘ j =
      (L ‘ ⟨i, j⟩ₖ) ‘ ⟨f ‘ j, b⟩ₖ := by
  rw [forcingLimitLift_value hf hb, forcingThreadSplice_coordinate hj hij]

theorem forcingLimitLift_inverse_lift {θ P R π E L U f i b : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hL : IsCoherentForcingLift θ P R π L)
    (hf : f ∈ forcingInverseLimit θ P π U) (hi : i ∈ θ) (hb : b ∈ P ‘ i)
    (hle : ⟨b, f ‘ i⟩ₖ ∈ R ‘ i) (hU : ∀ j ∈ θ, P ‘ j ⊆ U)
    (hπ : ∀ j ∈ i, ∀ p ∈ P ‘ i, ∀ q ∈ P ‘ i, ⟨p, q⟩ₖ ∈ R ‘ i →
      ⟨(π ‘ ⟨j, i⟩ₖ) ‘ p, (π ‘ ⟨j, i⟩ₖ) ‘ q⟩ₖ ∈ R ‘ j) :
    let g := (forcingLimitLift (forcingInverseLimit θ P π U) (P ‘ i) θ π L i) ‘ ⟨f, b⟩ₖ
    g ∈ forcingInverseLimit θ P π U ∧
      ⟨g, f⟩ₖ ∈ forcingThreadOrder θ R (forcingInverseLimit θ P π U) ∧ g ‘ i = b := by
  dsimp only
  rw [forcingLimitLift_value hf hb]
  exact ⟨forcingThreadSplice_mem h hL hf hi hb hle hU,
    forcingThreadSplice_le h hL hf hi hb hle hU hπ,
    (forcingThreadSplice_value hi).trans (forcingSpliceValue_self h hL hf hi hb hle)⟩

theorem forcingLimitLift_direct_lift {θ P R π E L U f i b : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hL : IsCoherentForcingLift θ P R π L)
    (hf : f ∈ forcingDirectLimit θ P π E U) (hi : i ∈ θ) (hb : b ∈ P ‘ i)
    (hle : ⟨b, f ‘ i⟩ₖ ∈ R ‘ i) (hU : ∀ j ∈ θ, P ‘ j ⊆ U)
    (hπ : ∀ j ∈ i, ∀ p ∈ P ‘ i, ∀ q ∈ P ‘ i, ⟨p, q⟩ₖ ∈ R ‘ i →
      ⟨(π ‘ ⟨j, i⟩ₖ) ‘ p, (π ‘ ⟨j, i⟩ₖ) ‘ q⟩ₖ ∈ R ‘ j)
    (hcompat : ∀ k ∈ θ, ∀ j ∈ θ, i ⊆ k → k ⊆ j → ∀ a ∈ P ‘ k, ∀ c ∈ P ‘ i,
      ⟨c, (π ‘ ⟨i, k⟩ₖ) ‘ a⟩ₖ ∈ R ‘ i →
      (L ‘ ⟨i, j⟩ₖ) ‘ ⟨(E ‘ ⟨k, j⟩ₖ) ‘ a, c⟩ₖ =
        (E ‘ ⟨k, j⟩ₖ) ‘ ((L ‘ ⟨i, k⟩ₖ) ‘ ⟨a, c⟩ₖ)) :
    let g := (forcingLimitLift (forcingDirectLimit θ P π E U) (P ‘ i) θ π L i) ‘ ⟨f, b⟩ₖ
    g ∈ forcingDirectLimit θ P π E U ∧
      ⟨g, f⟩ₖ ∈ forcingThreadOrder θ R (forcingDirectLimit θ P π E U) ∧ g ‘ i = b := by
  dsimp only
  rw [forcingLimitLift_value hf hb]
  have hf' := forcingDirectLimit_subset _ _ _ _ _ _ hf
  have hg := forcingThreadSplice_direct_mem h hL hf hi hb hle hU hcompat
  have hle' := forcingThreadSplice_le h hL hf' hi hb hle hU hπ
  exact ⟨hg, (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
    ⟨hg, hf, ((mem_forcingThreadOrder_iff _ _ _ _ _).mp hle').2.2⟩,
    (forcingThreadSplice_value hi).trans (forcingSpliceValue_self h hL hf' hi hb hle)⟩

end ZFVP
