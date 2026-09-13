import ZFVP.SetTheory.ForcingSectionThread

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingFamilyNextValue (θ P Q i : V) : V := by
  classical
  exact if i = θ then Q else P ‘ i

instance forcingFamilyNextValue_definable : ℒₛₑₜ-function₄[V] forcingFamilyNextValue := by
  classical
  have h : ℒₛₑₜ-relation₅ (fun y θ P Q i : V ↦
    (i = θ ∧ y = Q) ∨ (i ≠ θ ∧ y = P ‘ i)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingFamilyNextValue (v 1) (v 2) (v 3) (v 4) ↔ _
  by_cases he : v 4 = v 1 <;> simp [forcingFamilyNextValue, he]

noncomputable def forcingFamilyNext (θ P Q : V) : V :=
  definableGraph (succ θ) (forcingFamilyNextValue θ P Q) (by
    exact Language.DefinableFunction₄.comp (F := forcingFamilyNextValue)
      (by definability) (by definability) (by definability) (by definability))

theorem forcingFamilyNext_old {θ P Q i : V} (hi : i ∈ θ) :
    (forcingFamilyNext θ P Q) ‘ i = P ‘ i := by
  classical
  rw [forcingFamilyNext, value_definableGraph _ _ _ (mem_succ_iff.mpr (Or.inr hi))]
  exact ite_eq_right (ne_of_mem hi)

theorem forcingFamilyNext_new (θ P Q : V) : (forcingFamilyNext θ P Q) ‘ θ = Q := by
  classical
  rw [forcingFamilyNext, value_definableGraph _ _ _ (mem_succ_iff.mpr (Or.inl rfl))]
  simp [forcingFamilyNextValue]

/-- Extend the final column, including its diagonal entry, of a stage-map matrix. -/
noncomputable def forcingMatrixNextValue (θ M C d z : V) : V := by
  classical
  exact if kpair.π₂ z = θ then forcingFamilyNextValue θ C d (kpair.π₁ z) else M ‘ z

instance forcingMatrixNextValue_parameter_definable (θ M C d : V) :
    ℒₛₑₜ-function₁[V] (forcingMatrixNextValue θ M C d) := by
  classical
  have h : ℒₛₑₜ-relation (fun y z : V ↦
    (kpair.π₂ z = θ ∧ ((kpair.π₁ z = θ ∧ y = d) ∨
      (kpair.π₁ z ≠ θ ∧ y = C ‘ (kpair.π₁ z)))) ∨
    (kpair.π₂ z ≠ θ ∧ y = M ‘ z)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingMatrixNextValue θ M C d (v 1) ↔ _
  by_cases he : kpair.π₂ (v 1) = θ <;>
    by_cases hf : kpair.π₁ (v 1) = θ <;> simp [forcingMatrixNextValue, forcingFamilyNextValue, he, hf]

noncomputable def forcingMatrixNext (θ M C d : V) : V :=
  definableGraph (succ θ ×ˢ succ θ) (forcingMatrixNextValue θ M C d)
    (forcingMatrixNextValue_parameter_definable θ M C d)

theorem forcingMatrixNext_old {θ M C d i j : V} (hi : i ∈ succ θ) (hj : j ∈ θ) :
    (forcingMatrixNext θ M C d) ‘ ⟨i, j⟩ₖ = M ‘ ⟨i, j⟩ₖ := by
  classical
  rw [forcingMatrixNext, value_definableGraph _ _ _
    (mem_prod_iff.mpr ⟨i, hi, j, mem_succ_iff.mpr (Or.inr hj), rfl⟩)]
  simp only [forcingMatrixNextValue, kpair.π₂_kpair, ite_eq_right (ne_of_mem hj)]

theorem forcingMatrixNext_column {θ M C d i : V} (hi : i ∈ θ) :
    (forcingMatrixNext θ M C d) ‘ ⟨i, θ⟩ₖ = C ‘ i := by
  classical
  rw [forcingMatrixNext, value_definableGraph _ _ _
    (mem_prod_iff.mpr ⟨i, mem_succ_iff.mpr (Or.inr hi), θ, mem_succ_iff.mpr (Or.inl rfl), rfl⟩)]
  simp only [forcingMatrixNextValue, kpair.π₂_kpair, ite_true,
    kpair.π₁_kpair, forcingFamilyNextValue, ite_eq_right (ne_of_mem hi)]

theorem forcingMatrixNext_diagonal (θ M C d : V) :
    (forcingMatrixNext θ M C d) ‘ ⟨θ, θ⟩ₖ = d := by
  classical
  rw [forcingMatrixNext, value_definableGraph _ _ _
    (mem_prod_iff.mpr ⟨θ, mem_succ_iff.mpr (Or.inl rfl), θ, mem_succ_iff.mpr (Or.inl rfl), rfl⟩)]
  simp [forcingMatrixNextValue, forcingFamilyNextValue]

/-- The equations required of one new projection and section column. -/
structure IsSplitForcingColumn (θ P π E Q ρ F : V) : Prop where
  projMaps : (∀ i ∈ θ, ∀ q ∈ Q, (ρ ‘ i) ‘ q ∈ P ‘ i)
  secMaps : (∀ i ∈ θ, ∀ p ∈ P ‘ i, (F ‘ i) ‘ p ∈ Q)
  projComp : (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ q ∈ Q,
    (π ‘ ⟨i, j⟩ₖ) ‘ ((ρ ‘ j) ‘ q) = (ρ ‘ i) ‘ q)
  secComp : (∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ P ‘ i,
    (F ‘ j) ‘ ((E ‘ ⟨i, j⟩ₖ) ‘ p) = (F ‘ i) ‘ p)
  retraction : (∀ i ∈ θ, ∀ p ∈ P ‘ i, (ρ ‘ i) ‘ ((F ‘ i) ‘ p) = p)

private theorem old_of_subset_old {θ i j : V} (hi : i ∈ succ θ) (hj : j ∈ θ)
    (hij : i ⊆ j) : i ∈ θ := by
  rcases mem_succ_iff.mp hi with rfl | hi
  · exact (mem_irrefl j (hij j hj)).elim
  · exact hi

theorem IsSplitForcingSystem.extend {θ P π E Q ρ F : V}
    (h : IsSplitForcingSystem θ P π E) (c : IsSplitForcingColumn θ P π E Q ρ F) :
    IsSplitForcingSystem (succ θ) (forcingFamilyNext θ P Q)
      (forcingMatrixNext θ π ρ (identity Q)) (forcingMatrixNext θ E F (identity Q)) := by
  have old {i : V} (hi : i ∈ θ) : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj hij p hp
    rcases mem_succ_iff.mp hj with rfl | hj
    · rw [forcingFamilyNext_new] at hp
      rcases mem_succ_iff.mp hi with rfl | hi
      · rw [forcingMatrixNext_diagonal, forcingFamilyNext_new, identity_value hp]
        exact hp
      · rw [forcingMatrixNext_column hi, forcingFamilyNext_old hi]
        exact c.projMaps i hi p hp
    · have hi' := old_of_subset_old hi hj hij
      rw [forcingFamilyNext_old hj] at hp
      rw [forcingMatrixNext_old hi hj, forcingFamilyNext_old hi']
      exact h.projMaps i hi' j hj hij p hp
  · intro i hi j hj hij p hp
    rcases mem_succ_iff.mp hj with rfl | hj
    · rcases mem_succ_iff.mp hi with rfl | hi
      · rw [forcingFamilyNext_new] at hp
        rw [forcingMatrixNext_diagonal, forcingFamilyNext_new, identity_value hp]
        exact hp
      · rw [forcingFamilyNext_old hi] at hp
        rw [forcingMatrixNext_column hi, forcingFamilyNext_new]
        exact c.secMaps i hi p hp
    · have hi' := old_of_subset_old hi hj hij
      rw [forcingFamilyNext_old hi'] at hp
      rw [forcingMatrixNext_old hi hj, forcingFamilyNext_old hj]
      exact h.secMaps i hi' j hj hij p hp
  · intro i hi p hp
    rcases mem_succ_iff.mp hi with rfl | hi
    · rw [forcingFamilyNext_new] at hp
      rw [forcingMatrixNext_diagonal, identity_value hp]
    · rw [forcingFamilyNext_old hi] at hp
      rw [forcingMatrixNext_old (old hi) hi]
      exact h.secId i hi p hp
  · intro i hi j hj k hk hij hjk p hp
    rcases mem_succ_iff.mp hk with rfl | hk
    · rw [forcingFamilyNext_new] at hp
      rcases mem_succ_iff.mp hj with rfl | hj
      · rw [forcingMatrixNext_diagonal, identity_value hp]
      · have hi' := old_of_subset_old hi hj hij
        rw [forcingMatrixNext_old hi hj, forcingMatrixNext_column hj,
          forcingMatrixNext_column hi']
        exact c.projComp i hi' j hj hij p hp
    · have hj' := old_of_subset_old hj hk hjk
      have hi' := old_of_subset_old hi hj' hij
      rw [forcingFamilyNext_old hk] at hp
      rw [forcingMatrixNext_old hi hj', forcingMatrixNext_old hj hk,
        forcingMatrixNext_old hi hk]
      exact h.projComp i hi' j hj' k hk hij hjk p hp
  · intro i hi j hj k hk hij hjk p hp
    rcases mem_succ_iff.mp hk with rfl | hk
    · rcases mem_succ_iff.mp hj with rfl | hj
      · rcases mem_succ_iff.mp hi with rfl | hi
        · rw [forcingFamilyNext_new] at hp
          rw [forcingMatrixNext_diagonal, identity_value hp, identity_value hp]
        · rw [forcingFamilyNext_old hi] at hp
          rw [forcingMatrixNext_diagonal, forcingMatrixNext_column hi,
            identity_value (c.secMaps i hi p hp)]
      · have hi' := old_of_subset_old hi hj hij
        rw [forcingFamilyNext_old hi'] at hp
        rw [forcingMatrixNext_column hj, forcingMatrixNext_old hi hj,
          forcingMatrixNext_column hi']
        exact c.secComp i hi' j hj hij p hp
    · have hj' := old_of_subset_old hj hk hjk
      have hi' := old_of_subset_old hi hj' hij
      rw [forcingFamilyNext_old hi'] at hp
      rw [forcingMatrixNext_old hj hk, forcingMatrixNext_old hi hj',
        forcingMatrixNext_old hi hk]
      exact h.secComp i hi' j hj' k hk hij hjk p hp
  · intro i hi j hj hij p hp
    rcases mem_succ_iff.mp hj with rfl | hj
    · rcases mem_succ_iff.mp hi with rfl | hi
      · rw [forcingFamilyNext_new] at hp
        rw [forcingMatrixNext_diagonal, forcingMatrixNext_diagonal,
          identity_value hp, identity_value hp]
      · rw [forcingFamilyNext_old hi] at hp
        rw [forcingMatrixNext_column hi, forcingMatrixNext_column hi]
        exact c.retraction i hi p hp
    · have hi' := old_of_subset_old hi hj hij
      rw [forcingFamilyNext_old hi'] at hp
      rw [forcingMatrixNext_old hi hj, forcingMatrixNext_old hi hj]
      exact h.retraction i hi' j hj hij p hp

end ZFVP
