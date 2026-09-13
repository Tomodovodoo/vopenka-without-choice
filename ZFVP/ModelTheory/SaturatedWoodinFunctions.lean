import ZFVP.ModelTheory.SaturatedWoodinSuccessor
import ZFVP.ModelTheory.TwoStepIntermediatePreservation
import ZFVP.SetTheory.WoodinCollapseDistributivity

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {P R one κ δ : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
  (h : IsForcingIterand P R (saturatedWoodinPrefixPosetName P R one κ δ)
    (saturatedWoodinPrefixOrderName P R one κ δ) ∅)
  {G : Set V} (hG : IsExternalForcingGeneric
    (twoStepConditions P R (saturatedWoodinPrefixPosetName P R one κ δ) ∅)
    (twoStepOrder P R (saturatedWoodinPrefixPosetName P R one κ δ)
      (saturatedWoodinPrefixOrderName P R one κ δ) ∅) G)

theorem saturatedWoodinSuccessor_function
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκδ : κ ⊆ δ)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
    (hDC : ∀ p ∈ P, p ∈ forcingFormula P R dependentChoiceBelowFormula (standardTuple ![checkName one κ]))
    {γ X : (twoStepFirstContext hR htop h hG).Model}
    (hγ : γ ∈ (twoStepFirstContext hR htop h hG).check κ)
    {f : (twoStepTotalContext hR htop h hG).Model}
    (hf : f ∈ twoStepIntermediateEmbedding hR htop h hG X ^
      twoStepIntermediateEmbedding hR htop h hG γ) :
    ∃ g ∈ X ^ γ, twoStepIntermediateEmbedding hR htop h hG g = f := by
  let A := twoStepFirstContext hR htop h hG
  let B := twoStepSecondContext hR htop h hG
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  have hk : IsRegularCardinal (A.check κ) := (Defined.eval_iff _).mp
    ((A.checked_unary_truth regularCardinalFormula κ).mpr ⟨p, hp, hκ p (A.generic.1.1 p hp)⟩)
  have hd : ∀ α ∈ A.check κ, InternalDependentChoiceAt α := (Defined.eval_iff _).mp
    ((A.checked_unary_truth dependentChoiceBelowFormula κ).mpr ⟨p, hp, hDC p (A.generic.1.1 p hp)⟩)
  have hBP : B.P = woodinCollapse (A.check κ) (A.check δ) :=
    A.saturatedWoodinPosetName_value hδ hP hκδ
  have hBR : B.R = woodinCollapseOrder (A.check κ) (A.check δ) :=
    A.saturatedWoodinOrderName_value hδ hP hκδ
  let := hk.1.1
  let := IsOrdinal.of_mem hγ
  apply twoStepIntermediate_function_of_closed hR htop h hG (hd γ hγ) ?_ hf
  intro α hα hαγ
  let := hα
  change IsForcingClosedAt B.P B.R α
  rw [hBP, hBR]
  exact woodinCollapse_closedBelow hk hd (A.check δ) α (ordinal_mem_of_subset_mem hαγ hγ)

end ZFVP
