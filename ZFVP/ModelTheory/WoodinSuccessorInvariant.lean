import ZFVP.SetTheory.WoodinSuccessorCode
import ZFVP.ModelTheory.WoodinPrefixRegularForcing
import ZFVP.ModelTheory.SaturatedWoodinPreservation
import ZFVP.ModelTheory.WoodinPrefixSourceCutoff
import ZFVP.ModelTheory.WoodinStrictPrefixCutoff

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsWoodinStage (x : V) : Prop :=
  IsForcingPreorder (woodinStagePoset x) (woodinStageOrder x) ∧
  IsForcingTop (woodinStagePoset x) (woodinStageOrder x) (woodinStageTop x) ∧
  IsOrdinal (woodinStageCardinal x) ∧
  (∀ p ∈ woodinStagePoset x, p ∈ forcingFormula (woodinStagePoset x) (woodinStageOrder x)
    regularCardinalFormula (standardTuple ![checkName (woodinStageTop x) (woodinStageCardinal x)])) ∧
  (∀ p ∈ woodinStagePoset x, p ∈ forcingFormula (woodinStagePoset x) (woodinStageOrder x)
    dependentChoiceBelowFormula (standardTuple ![checkName (woodinStageTop x) (woodinStageCardinal x)]))

instance isWoodinStage_definable : ℒₛₑₜ-predicate[V] IsWoodinStage := by
  have h (φ : SetTheorySemisentence 1) : ℒₛₑₜ-predicate[V] (fun x ↦
      ∀ p ∈ woodinStagePoset x, p ∈ forcingFormula (woodinStagePoset x) (woodinStageOrder x)
        φ (standardTuple ![checkName (woodinStageTop x) (woodinStageCardinal x)])) := by
    apply Language.Definable.all
    apply Language.Definable.imp
    · definability
    · apply Language.DefinableRel₄.comp (P := fun p P R b ↦ p ∈ forcingFormula P R φ b)
      · definability
      · definability
      · definability
      · simp only [standardTuple]; definability
  unfold IsWoodinStage
  exact Language.Definable.and (by definability) (Language.Definable.and (by definability)
    (Language.Definable.and (by definability) ((h _).and (h _))))

theorem woodinSuccessorAt_stage {P R one κ δ : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
    (hδ : IsWoodinPrefixCutoff P R one κ δ) (hP : P ∈ hierarchy δ) :
    IsWoodinStage (woodinSuccessorAt P R one κ δ) := by
  let := hδ.2.1.1
  have h := saturatedWoodinPrefix_iterand_of_cutoff hR htop hκ hδ hP
  simp only [IsWoodinStage, woodinSuccessorAt, woodinStagePoset_code, woodinStageOrder_code,
    woodinStageTop_code, woodinStageCardinal_code]
  have hf := saturatedWoodinSuccessor_forces_cardinal hR htop hκ hδ hP
  refine ⟨twoStep_preorder hR htop h, twoStep_top hR htop h, inferInstance, ?_, ?_⟩
  · intro p hp
    have hh := hf p hp
    rw [woodinStageCardinalFormula, forcingFormula_and, mem_inter_iff] at hh
    exact hh.1
  · intro p hp
    have hh := hf p hp
    rw [woodinStageCardinalFormula, forcingFormula_and, mem_inter_iff] at hh
    exact hh.2

theorem woodinSuccessorStep_stage {x δ : V} (hx : IsWoodinStage x)
    (hδ : IsWoodinPrefixCutoff (woodinStagePoset x) (woodinStageOrder x)
      (woodinStageTop x) (woodinStageCardinal x) δ)
    (hP : woodinStagePoset x ∈ hierarchy (woodinPrefixCutoff (woodinStagePoset x)
      (woodinStageOrder x) (woodinStageTop x) (woodinStageCardinal x))) :
    IsWoodinStage (woodinSuccessorStep x) :=
  woodinSuccessorAt_stage hx.1 hx.2.1 hx.2.2.2.1 (woodinPrefixCutoff_spec hδ).2.1 hP

theorem woodinSuccessorStep_cardinal_gt {x δ : V}
    (hδ : IsWoodinPrefixCutoff (woodinStagePoset x) (woodinStageOrder x)
      (woodinStageTop x) (woodinStageCardinal x) δ) :
    woodinStageCardinal x ∈ woodinStageCardinal (woodinSuccessorStep x) := by
  simpa [woodinSuccessorStep, woodinSuccessorAt] using (woodinPrefixCutoff_spec hδ).2.1.1

theorem woodinSuccessorStep_cardinal_inaccessible {x δ : V}
    (hδ : IsWoodinPrefixCutoff (woodinStagePoset x) (woodinStageOrder x)
      (woodinStageTop x) (woodinStageCardinal x) δ) :
    IsChoicelessInaccessible (woodinStageCardinal (woodinSuccessorStep x)) := by
  simpa [woodinSuccessorStep, woodinSuccessorAt] using (woodinPrefixCutoff_spec hδ).2.1.2.1

theorem woodinSuccessorStep_cardinal_lt_supercompact {x δ : V} (hx : IsWoodinStage x)
    (hδ : IsWoodinSupercompact δ) (hP : woodinStagePoset x ∈ hierarchy δ)
    (hR : woodinStageOrder x ∈ hierarchy δ) (hκ : woodinStageCardinal x ∈ δ) :
    woodinStageCardinal (woodinSuccessorStep x) ∈ δ := by
  simpa [woodinSuccessorStep, woodinSuccessorAt] using
    woodinPrefixCutoff_lt_supercompact hδ hx.1 hx.2.1 hP hR hκ hx.2.2.2.1 hx.2.2.2.2

end ZFVP
