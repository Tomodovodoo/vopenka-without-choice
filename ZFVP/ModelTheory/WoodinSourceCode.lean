import ZFVP.SetTheory.WoodinSeedSystem
import ZFVP.SetTheory.WoodinSeedOrder
import ZFVP.ModelTheory.WoodinIterationInitial

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSourceCode (θ s : V) : V :=
  forcingIterationCode (woodinInsertSeed θ (forcingCodeP s) {∅})
    (woodinInsertSeed θ (forcingCodeR s) (({∅} : V) ×ˢ {∅}))
    (woodinSeedProjections θ (forcingCodeP s) (forcingCodeπ s))
    (woodinSeedSections θ (forcingCodeE s) (forcingCodet s))
    (woodinSeedLifts θ (forcingCodeP s) (forcingCodeL s))
    (woodinInsertSeed θ (forcingCodet s) ∅)

noncomputable def woodinSourceCardinals (θ K : V) : V := woodinInsertSeed θ K woodinSeedCardinal

theorem woodinInsertSeed_table (θ f a : V) :
    IsIterationTable (woodinSourceIndex θ) (woodinInsertSeed θ f a) :=
  ⟨inferInstance, woodinInsertSeed_domain _ _ _⟩

theorem woodinSeedMatrix_table (θ M C : V) :
    IsIterationTable (woodinSourceIndex θ ×ˢ woodinSourceIndex θ) (woodinSeedMatrix θ M C) :=
  ⟨inferInstance, domain_definableGraph _ _ _⟩

theorem woodinSourceCode_valid {θ s : V} [IsOrdinal θ] (hs : IsForcingIterationCode θ s) :
    IsForcingIterationCode (woodinSourceIndex θ) (woodinSourceCode θ s) := by
  unfold woodinSourceCode
  constructor <;> simp only [forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code,
    forcingCodeE_code, forcingCodeL_code, forcingCodet_code]
  · exact woodinSeed_system hs.system
  · exact woodinInsertSeed_table _ _ _
  · exact woodinInsertSeed_table _ _ _
  · exact woodinSeedMatrix_table _ _ _
  · exact woodinSeedMatrix_table _ _ _
  · exact woodinSeedMatrix_table _ _ _
  · exact woodinInsertSeed_table _ _ _

theorem woodinSourceCardinals_table (θ K : V) :
    IsIterationTable (woodinSourceIndex θ) (woodinSourceCardinals θ K) := woodinInsertSeed_table _ _ _

theorem woodinSourceCode_stage {θ s K α : V} [IsOrdinal θ] (hα : α ∈ θ) :
    woodinIterationStage (woodinSourceCode θ s) (woodinSourceCardinals θ K) (woodinSourceIndex α) =
      woodinIterationStage s K α := by
  simp only [woodinIterationStage, woodinSourceCode, woodinSourceCardinals,
    forcingCodeP_code, forcingCodeR_code, forcingCodet_code, woodinInsertSeed_at_sourceIndex hα]

theorem woodinSourceCode_seed (θ s K : V) [IsOrdinal θ] :
    woodinIterationStage (woodinSourceCode θ s) (woodinSourceCardinals θ K) ∅ = woodinSeedStage := by
  simp only [woodinIterationStage, woodinSourceCode, woodinSourceCardinals,
    forcingCodeP_code, forcingCodeR_code, forcingCodet_code, woodinInsertSeed_zero, woodinSeedStage]

theorem woodinSourceCode_firstRestoration :
    woodinIterationStage (woodinSourceCode (succ ∅) (woodinInitialCode : V))
      (woodinSourceCardinals (succ ∅) woodinInitialCardinals) (woodinSourceIndex ∅) =
      woodinSuccessorStep (woodinSeedStage : V) := by
  rw [woodinSourceCode_stage (mem_succ_self ∅), woodinInitialCode_stage]
  rfl

theorem woodinSourceCode_projection {θ s α β : V} [IsOrdinal θ] (hα : α ∈ θ) (hβ : β ∈ θ) :
    (forcingCodeπ (woodinSourceCode θ s)) ‘ ⟨woodinSourceIndex α, woodinSourceIndex β⟩ₖ =
      (forcingCodeπ s) ‘ ⟨α, β⟩ₖ := by
  simp only [woodinSourceCode, forcingCodeπ_code, woodinSeedProjections,
    woodinSeedMatrix_at_sourceIndex hα hβ]

theorem woodinSourceCode_section {θ s α β : V} [IsOrdinal θ] (hα : α ∈ θ) (hβ : β ∈ θ) :
    (forcingCodeE (woodinSourceCode θ s)) ‘ ⟨woodinSourceIndex α, woodinSourceIndex β⟩ₖ =
      (forcingCodeE s) ‘ ⟨α, β⟩ₖ := by
  simp only [woodinSourceCode, forcingCodeE_code, woodinSeedSections,
    woodinSeedMatrix_at_sourceIndex hα hβ]

theorem woodinSourceCode_lift {θ s α β : V} [IsOrdinal θ] (hα : α ∈ θ) (hβ : β ∈ θ) :
    (forcingCodeL (woodinSourceCode θ s)) ‘ ⟨woodinSourceIndex α, woodinSourceIndex β⟩ₖ =
      (forcingCodeL s) ‘ ⟨α, β⟩ₖ := by
  simp only [woodinSourceCode, forcingCodeL_code, woodinSeedLifts,
    woodinSeedMatrix_at_sourceIndex hα hβ]

theorem woodinSourceCardinals_stage {θ K α : V} [IsOrdinal θ] (hα : α ∈ θ) :
    (woodinSourceCardinals θ K) ‘ (woodinSourceIndex α) = K ‘ α :=
  woodinInsertSeed_at_sourceIndex hα

theorem woodinSourceCardinals_seed (θ K : V) [IsOrdinal θ] :
    (woodinSourceCardinals θ K) ‘ ∅ = woodinSeedCardinal := woodinInsertSeed_zero _ _ _

instance woodinSeedMatrix_definable : ℒₛₑₜ-function₃[V] woodinSeedMatrix := by
  have hd : ℒₛₑₜ-relation₄ (fun g θ M C : V ↦ ∀ z, z ∈ g ↔
    ∃ p ∈ woodinSourceIndex θ ×ˢ woodinSourceIndex θ, z = ⟨p, woodinSeedMatrixValue M C p⟩ₖ) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = woodinSeedMatrix (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [woodinSeedMatrix, mem_definableGraph_iff]

instance woodinSeedProjectionColumn_definable : ℒₛₑₜ-function₂[V] woodinSeedProjectionColumn := by
  have hd : ℒₛₑₜ-relation₃ (fun g θ Q : V ↦ ∀ z, z ∈ g ↔
    ∃ j ∈ woodinSourceIndex θ, z = ⟨j, (Q ‘ j) ×ˢ ({∅} : V)⟩ₖ) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = woodinSeedProjectionColumn (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [woodinSeedProjectionColumn, mem_definableGraph_iff]

instance woodinSeedSectionColumn_definable : ℒₛₑₜ-function₂[V] woodinSeedSectionColumn := by
  have hd : ℒₛₑₜ-relation₃ (fun g θ t : V ↦ ∀ z, z ∈ g ↔
    ∃ j ∈ woodinSourceIndex θ, z = ⟨j, ({∅} : V) ×ˢ {t ‘ j}⟩ₖ) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = woodinSeedSectionColumn (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [woodinSeedSectionColumn, mem_definableGraph_iff]

instance woodinSeedLiftColumn_definable : ℒₛₑₜ-function₂[V] woodinSeedLiftColumn := by
  have hd : ℒₛₑₜ-relation₃ (fun g θ Q : V ↦ ∀ z, z ∈ g ↔
    ∃ j ∈ woodinSourceIndex θ, z = ⟨j, woodinSeedLiftMap (Q ‘ j)⟩ₖ) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = woodinSeedLiftColumn (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [woodinSeedLiftColumn, mem_definableGraph_iff]

instance woodinSeedProjections_definable : ℒₛₑₜ-function₃[V] woodinSeedProjections := by
  unfold woodinSeedProjections
  definability

instance woodinSeedSections_definable : ℒₛₑₜ-function₃[V] woodinSeedSections := by
  unfold woodinSeedSections
  definability

instance woodinSeedLifts_definable : ℒₛₑₜ-function₃[V] woodinSeedLifts := by
  unfold woodinSeedLifts
  definability

instance woodinSourceCode_definable : ℒₛₑₜ-function₂[V] woodinSourceCode := by
  unfold woodinSourceCode forcingIterationCode
  definability

instance woodinSourceCardinals_definable : ℒₛₑₜ-function₂[V] woodinSourceCardinals := by
  unfold woodinSourceCardinals
  definability

end ZFVP
