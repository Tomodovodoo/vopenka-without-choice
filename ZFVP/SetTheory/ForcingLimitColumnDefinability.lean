import ZFVP.SetTheory.ForcingLimitLiftColumns

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

instance forcingThreadCoordinate_uniform_definable :
    ℒₛₑₜ-function₂[V] forcingThreadCoordinate := by
  have h : ℒₛₑₜ-relation₃ (fun g C i : V ↦ ∀ z, z ∈ g ↔
      ∃ p ∈ C, z = ⟨p, p ‘ i⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingThreadCoordinate (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [forcingThreadCoordinate, mem_definableGraph_iff]

instance forcingLimitProjectionColumn_definable :
    ℒₛₑₜ-function₂[V] forcingLimitProjectionColumn := by
  have h : ℒₛₑₜ-relation₃ (fun g θ C : V ↦ ∀ z, z ∈ g ↔
      ∃ i ∈ θ, z = ⟨i, forcingThreadCoordinate C i⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingLimitProjectionColumn (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [forcingLimitProjectionColumn, mem_definableGraph_iff]

instance forcingThreadSection_uniform_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (forcingThreadSection (V := V)) := by
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun g θ P π E i : V ↦ ∀ z, z ∈ g ↔
      ∃ p ∈ P ‘ i, z = ⟨p, forcingSectionThread θ π E i p⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingThreadSection (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  rw [mem_ext_iff]
  simp only [forcingThreadSection, mem_definableGraph_iff]

instance forcingLimitSectionColumn_definable :
    ℒₛₑₜ-function₄[V] forcingLimitSectionColumn := by
  have h : ℒₛₑₜ-relation₅ (fun g θ P π E : V ↦ ∀ z, z ∈ g ↔
      ∃ i ∈ θ, z = ⟨i, forcingThreadSection θ P π E i⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingLimitSectionColumn (v 1) (v 2) (v 3) (v 4) ↔ _
  rw [mem_ext_iff]
  simp only [forcingLimitSectionColumn, mem_definableGraph_iff]

noncomputable def forcingThreadSplicePair (θ π L i a : V) : V :=
  forcingThreadSplice θ π L (kpair.π₁ a) i (kpair.π₂ a)

instance forcingThreadSplicePair_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (forcingThreadSplicePair (V := V)) := by
  classical
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun f θ π L i a : V ↦ ∀ z, z ∈ f ↔ ∃ j ∈ θ,
      (j ∈ i ∧ z = ⟨j, (π ‘ ⟨j, i⟩ₖ) ‘ (kpair.π₂ a)⟩ₖ) ∨
      (j ∉ i ∧ z = ⟨j, (L ‘ ⟨i, j⟩ₖ) ‘ ⟨(kpair.π₁ a) ‘ j, kpair.π₂ a⟩ₖ⟩ₖ)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingThreadSplicePair (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  rw [mem_ext_iff]
  apply forall_congr'
  intro z
  rw [forcingThreadSplicePair, forcingThreadSplice, mem_definableGraph_iff]
  apply iff_congr Iff.rfl
  apply exists_congr
  intro j
  by_cases hj : j ∈ v 4 <;> simp [forcingSpliceValue, hj]

instance forcingLimitLiftColumn_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (forcingLimitLiftColumn (V := V)) := by
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun g C θ P π L : V ↦ ∀ z, z ∈ g ↔
      ∃ i ∈ θ, ∃ f, z = ⟨i, f⟩ₖ ∧ ∀ w, w ∈ f ↔
        ∃ a ∈ C ×ˢ (P ‘ i), w = ⟨a, forcingThreadSplicePair θ π L i a⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingLimitLiftColumn (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  rw [mem_ext_iff]
  apply forall_congr'
  intro z
  rw [forcingLimitLiftColumn, mem_definableGraph_iff]
  apply iff_congr Iff.rfl
  apply exists_congr
  intro i
  apply and_congr_right
  intro _
  have he (f : V) : (∀ w, w ∈ f ↔ ∃ a ∈ (v 1) ×ˢ ((v 3) ‘ i),
      w = ⟨a, forcingThreadSplicePair (v 2) (v 4) (v 5) i a⟩ₖ) ↔
      f = forcingLimitLift (v 1) ((v 3) ‘ i) (v 2) (v 4) (v 5) i := by
    rw [mem_ext_iff]
    simp only [forcingLimitLift, mem_definableGraph_iff, forcingThreadSplicePair]
  simp only [he, exists_eq_right]

end ZFVP
