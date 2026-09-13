import ZFVP.ModelTheory.WoodinSparseSuccessorCommonWitness
import ZFVP.ModelTheory.WoodinSparseCompletedCommonWitness
import ZFVP.ModelTheory.WoodinSparseLimitAutomorphismSupport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

noncomputable def woodinSparseHomogeneityInitialRow (θ p : V) : V :=
  ⟨identity ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ), p⟩ₖ

noncomputable def woodinSparseHomogeneitySuccessorRow (k H W p q : V) : V :=
  ⟨woodinSparseSuccessorHomogenizingMap k (H ‘ k) p q,
    woodinSparseSuccessorCommonWitness k (H ‘ k) p q (W ‘ k)⟩ₖ

noncomputable def woodinSparseHomogeneityDirectRow (θ H W : V) : V :=
  ⟨woodinSparseDirectAutomorphism θ (woodinSparsePrefixCode θ) H, ⋃ˢ range W⟩ₖ

noncomputable def woodinSparseHomogeneityInverseRow (θ H W p q : V) : V :=
  let f := woodinSparseInverseAutomorphism θ (woodinSparsePrefixCode θ) H;
  ⟨woodinSparseCompletedHomogenizingMap θ f p q,
    woodinSparseCompletedCommonWitness θ f p q (⋃ˢ range W)⟩ₖ

instance woodinSparseHomogeneityInitialRow_definable : ℒₛₑₜ-function₂[V] woodinSparseHomogeneityInitialRow := by
  unfold woodinSparseHomogeneityInitialRow
  definability

instance woodinSparseHomogeneitySuccessorRow_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (woodinSparseHomogeneitySuccessorRow (V := V)) := by
  unfold woodinSparseHomogeneitySuccessorRow
  definability

instance woodinSparseHomogeneityDirectRow_definable : ℒₛₑₜ-function₃[V] woodinSparseHomogeneityDirectRow := by
  unfold woodinSparseHomogeneityDirectRow
  definability

instance woodinSparseHomogeneityInverseRow_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (woodinSparseHomogeneityInverseRow (V := V)) := by
  unfold woodinSparseHomogeneityInverseRow
  dsimp only
  definability

noncomputable def woodinSparseHomogeneityRow (δ a b θ H W : V) : V := by
  classical
  exact if θ ⊆ δ then woodinSparseHomogeneityInitialRow θ (a ‘ θ)
    else if θ = succ (⋃ˢ θ) then woodinSparseHomogeneitySuccessorRow (⋃ˢ θ) H W (a ‘ θ) (b ‘ θ)
    else if IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)) then
      woodinSparseHomogeneityDirectRow θ H W
    else woodinSparseHomogeneityInverseRow θ H W (a ‘ θ) (b ‘ θ)

instance woodinSparseHomogeneityRow_definable (δ a b : V) :
    ℒₛₑₜ-function₃[V] (woodinSparseHomogeneityRow δ a b) := by
  classical
  have h : ℒₛₑₜ-relation₄[V] (fun z θ H W ↦
    (θ ⊆ δ ∧ z = woodinSparseHomogeneityInitialRow θ (a ‘ θ)) ∨
    (¬θ ⊆ δ ∧ θ = succ (⋃ˢ θ) ∧ z = woodinSparseHomogeneitySuccessorRow (⋃ˢ θ) H W (a ‘ θ) (b ‘ θ)) ∨
    (¬θ ⊆ δ ∧ θ ≠ succ (⋃ˢ θ) ∧ IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)) ∧
      z = woodinSparseHomogeneityDirectRow θ H W) ∨
    (¬θ ⊆ δ ∧ θ ≠ succ (⋃ˢ θ) ∧ ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)) ∧
      z = woodinSparseHomogeneityInverseRow θ H W (a ‘ θ) (b ‘ θ))) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = woodinSparseHomogeneityRow δ a b (v 1) (v 2) (v 3) ↔ _
  unfold woodinSparseHomogeneityRow
  split_ifs <;> tauto

end ZFVP
