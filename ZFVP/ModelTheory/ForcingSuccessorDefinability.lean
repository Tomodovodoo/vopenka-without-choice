import ZFVP.ModelTheory.ForcingSuccessorCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingFamilyNext_definable : ℒₛₑₜ-function₃[V] forcingFamilyNext := by
  have h : ℒₛₑₜ-relation₄ (fun y θ P Q : V ↦ ∀ z, z ∈ y ↔
      ∃ i ∈ succ θ, z = ⟨i, forcingFamilyNextValue θ P Q i⟩ₖ) := by
    apply Language.Definable.all
    apply Language.Definable.biconditional
    · definability
    · apply Language.Definable.exs
      apply Language.Definable.and
      · definability
      · apply Language.DefinableRel.comp (P := Eq)
        · definability
        · apply Language.DefinableFunction₂.comp (F := kpair)
          · definability
          · apply Language.DefinableFunction₄.comp <;> definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingFamilyNext (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingFamilyNext, mem_definableGraph_iff]

instance forcingMatrixNextValue_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (forcingMatrixNextValue (V := V)) := by
  classical
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun y θ M C d z : V ↦
      (kpair.π₂ z = θ ∧ y = forcingFamilyNextValue θ C d (kpair.π₁ z)) ∨
      (kpair.π₂ z ≠ θ ∧ y = M ‘ z)) := by
    apply Language.Definable.or
    · apply Language.Definable.and
      · definability
      · apply Language.DefinableRel.comp (P := Eq)
        · definability
        · apply Language.DefinableFunction₄.comp <;> definability
    · definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingMatrixNextValue (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  by_cases he : kpair.π₂ (v 5) = v 1 <;> simp [forcingMatrixNextValue, he]

instance forcingMatrixNext_definable : ℒₛₑₜ-function₄[V] forcingMatrixNext := by
  have h : ℒₛₑₜ-relation₅ (fun y θ M C d : V ↦ ∀ z, z ∈ y ↔
      ∃ i ∈ succ θ ×ˢ succ θ, z = ⟨i, forcingMatrixNextValue θ M C d i⟩ₖ) := by
    apply Language.Definable.all
    apply Language.Definable.biconditional
    · definability
    · apply Language.Definable.exs
      apply Language.Definable.and
      · definability
      · apply Language.DefinableRel.comp (P := Eq)
        · definability
        · apply Language.DefinableFunction₂.comp (F := kpair)
          · definability
          · apply Language.DefinableFunction₅.comp <;> definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingMatrixNext (v 1) (v 2) (v 3) (v 4) ↔ _
  rw [mem_ext_iff]
  simp only [forcingMatrixNext, mem_definableGraph_iff]

instance successorStageProjection_definable : ℒₛₑₜ-function₄[V] successorStageProjection := by
  have h : ℒₛₑₜ-relation₅ (fun y C π k i : V ↦ ∀ z, z ∈ y ↔
      ∃ a ∈ C, z = ⟨a, (π ‘ ⟨i, k⟩ₖ) ‘ (kpair.π₁ a)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = successorStageProjection (v 1) (v 2) (v 3) (v 4) ↔ _
  rw [mem_ext_iff]
  simp only [successorStageProjection, mem_definableGraph_iff]

instance successorStageSection_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (successorStageSection (V := V)) := by
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun y P E k t i : V ↦ ∀ z, z ∈ y ↔
      ∃ p ∈ P ‘ i, z = ⟨p, ⟨(E ‘ ⟨i, k⟩ₖ) ‘ p, t⟩ₖ⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = successorStageSection (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  rw [mem_ext_iff]
  simp only [successorStageSection, mem_definableGraph_iff]

instance successorForcingLift_definable : ℒₛₑₜ-function₃[V] successorForcingLift := by
  have h : ℒₛₑₜ-relation₄ (fun y C A L : V ↦ ∀ z, z ∈ y ↔
      ∃ a ∈ C ×ˢ A, z = ⟨a, successorForcingLiftValue L (kpair.π₁ a) (kpair.π₂ a)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = successorForcingLift (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [successorForcingLift, mem_definableGraph_iff]

instance successorProjectionColumn_definable : ℒₛₑₜ-function₄[V] successorProjectionColumn := by
  have h : ℒₛₑₜ-relation₅ (fun y θ C π k : V ↦ ∀ z, z ∈ y ↔
      ∃ i ∈ θ, z = ⟨i, successorStageProjection C π k i⟩ₖ) := by
    apply Language.Definable.all
    apply Language.Definable.biconditional
    · definability
    · apply Language.Definable.exs
      apply Language.Definable.and
      · definability
      · apply Language.DefinableRel.comp (P := Eq)
        · definability
        · apply Language.DefinableFunction₂.comp (F := kpair)
          · definability
          · apply Language.DefinableFunction₄.comp <;> definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = successorProjectionColumn (v 1) (v 2) (v 3) (v 4) ↔ _
  rw [mem_ext_iff]
  simp only [successorProjectionColumn, mem_definableGraph_iff]

instance successorSectionColumn_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (successorSectionColumn (V := V)) := by
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun y θ P E k t : V ↦ ∀ z, z ∈ y ↔
      ∃ i ∈ θ, z = ⟨i, successorStageSection P E k t i⟩ₖ) := by
    apply Language.Definable.all
    apply Language.Definable.biconditional
    · definability
    · apply Language.Definable.exs
      apply Language.Definable.and
      · definability
      · apply Language.DefinableRel.comp (P := Eq)
        · definability
        · apply Language.DefinableFunction₂.comp (F := kpair)
          · definability
          · apply Language.DefinableFunction₅.comp <;> definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = successorSectionColumn (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  rw [mem_ext_iff]
  simp only [successorSectionColumn, mem_definableGraph_iff]

instance successorLiftColumn_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (successorLiftColumn (V := V)) := by
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun y θ C P L k : V ↦ ∀ z, z ∈ y ↔
      ∃ i ∈ θ, z = ⟨i, successorForcingLift C (P ‘ i) (L ‘ ⟨i, k⟩ₖ)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = successorLiftColumn (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  rw [mem_ext_iff]
  simp only [successorLiftColumn, mem_definableGraph_iff]

instance forcingIdentityLift_definable : ℒₛₑₜ-function₁[V] forcingIdentityLift := by
  have h : ℒₛₑₜ-relation (fun y Q : V ↦ ∀ z, z ∈ y ↔
      ∃ a ∈ Q ×ˢ Q, z = ⟨a, kpair.π₂ a⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingIdentityLift (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [forcingIdentityLift, mem_definableGraph_iff]

instance forcingIterationCodeNext_definable : Language.DefinableFunction ℒₛₑₜ
    (fun v : Fin 8 → V ↦ forcingIterationCodeNext (v 0) (v 1) (v 2) (v 3)
      (v 4) (v 5) (v 6) (v 7)) := by
  unfold forcingIterationCodeNext forcingIterationCode
  apply Language.DefinableFunction₂.comp (F := kpair)
  · apply Language.DefinableFunction₃.comp <;> definability
  · apply Language.DefinableFunction₂.comp (F := kpair)
    · apply Language.DefinableFunction₃.comp <;> definability
    · apply Language.DefinableFunction₂.comp (F := kpair)
      · apply Language.DefinableFunction₄.comp <;> definability
      · apply Language.DefinableFunction₂.comp (F := kpair)
        · apply Language.DefinableFunction₄.comp <;> definability
        · apply Language.DefinableFunction₂.comp (F := kpair)
          · apply Language.DefinableFunction₄.comp <;> definability
          · apply Language.DefinableFunction₃.comp <;> definability

theorem forcingIterationCodeNext_comp {n : ℕ}
    {a b c d e f g h : (Fin n → V) → V}
    (ha : Language.DefinableFunction ℒₛₑₜ a) (hb : Language.DefinableFunction ℒₛₑₜ b)
    (hc : Language.DefinableFunction ℒₛₑₜ c) (hd : Language.DefinableFunction ℒₛₑₜ d)
    (he : Language.DefinableFunction ℒₛₑₜ e) (hf : Language.DefinableFunction ℒₛₑₜ f)
    (hg : Language.DefinableFunction ℒₛₑₜ g) (hh : Language.DefinableFunction ℒₛₑₜ h) :
    Language.DefinableFunction ℒₛₑₜ (fun v ↦
      forcingIterationCodeNext (a v) (b v) (c v) (d v) (e v) (f v) (g v) (h v)) :=
  Language.DefinableFunction.substitution (f := ![a, b, c, d, e, f, g, h])
    forcingIterationCodeNext_definable
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, ha, hb, hc, hd, he, hf, hg, hh])

instance forcingSuccessorCode_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (forcingSuccessorCode (V := V)) := by
  unfold forcingSuccessorCode
  apply forcingIterationCodeNext_comp
  · definability
  · definability
  · apply Language.DefinableFunction₄.comp <;> definability
  · apply Language.DefinableFunction₅.comp <;> definability
  · apply Language.DefinableFunction₄.comp
    · definability
    · apply Language.DefinableFunction₄.comp <;> definability
    · definability
    · definability
  · apply Language.DefinableFunction₅.comp <;> definability
  · apply Language.DefinableFunction₅.comp
    · definability
    · apply Language.DefinableFunction₄.comp <;> definability
    · definability
    · definability
    · definability
  · definability

end ZFVP
