import ZFVP.ModelTheory.WoodinBoundInvariant

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinBoundSuccessorRawTail (θ i f k : V) : V :=
  let s := woodinIterationPrefix (succ k)
  let P := (forcingCodeP s) ‘ k
  let R := (forcingCodeR s) ‘ k
  let o := (forcingCodet s) ‘ k
  let κ := (woodinIterationCardinalPrefix (succ k)) ‘ k
  let c := woodinPrefixCutoff P R o κ
  let Q := saturatedWoodinPrefixPosetName P R o κ c
  let E := (forcingCodeE s) ‘ ⟨i, k⟩ₖ
  forcingSelectedUnion P R o (twoStepNames Q ∅) (twoStepTailSelector P R Q ∅)
    (nameAction E (woodinBoundCoordinateName θ i f (succ k)))

noncomputable def woodinBoundInverseRawTail (θ i f j : V) : V :=
  let s := woodinIterationPrefix j
  let γ := woodinLimitCardinal (woodinIterationCardinalPrefix j)
  let c := forcingInverseSourceCutoff j s γ
  let Q := forcingInverseCollapseName j s c (forcingInverseHartogsName j s γ)
    (forcingInverseRestorationName j s γ)
  let P := forcingInverseCodePoset j s
  let R := forcingInverseCodeOrder j s
  let o := forcingInverseCodeTop j s
  let E := forcingThreadSection j (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s) i
  forcingSelectedUnion P R o (twoStepNames Q ∅) (twoStepTailSelector P R Q ∅)
    (nameAction E (woodinBoundCoordinateName θ i f j))

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

private theorem selectedUnion_comp {n : ℕ}
    {a b c d e f : (Fin n → V) → V}
    (ha : Language.DefinableFunction ℒₛₑₜ a) (hb : Language.DefinableFunction ℒₛₑₜ b)
    (hc : Language.DefinableFunction ℒₛₑₜ c) (hd : Language.DefinableFunction ℒₛₑₜ d)
    (he : Language.DefinableFunction ℒₛₑₜ e) (hf : Language.DefinableFunction ℒₛₑₜ f) :
    Language.DefinableFunction ℒₛₑₜ
      (fun v ↦ forcingSelectedUnion (a v) (b v) (c v) (d v) (e v) (f v)) :=
  Language.DefinableFunction.substitution (f := ![a, b, c, d, e, f]) forcingSelectedUnion_definable
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, ha, hb, hc, hd, he, hf])

instance woodinBoundSuccessorRawTail_definable (θ i f : V) :
    ℒₛₑₜ-function₁[V] (woodinBoundSuccessorRawTail θ i f) := by
  unfold woodinBoundSuccessorRawTail
  dsimp only
  apply selectedUnion_comp <;> definability

instance woodinBoundInverseRawTail_definable (θ i f : V) :
    ℒₛₑₜ-function₁[V] (woodinBoundInverseRawTail θ i f) := by
  unfold woodinBoundInverseRawTail
  dsimp only
  apply selectedUnion_comp <;> definability

instance woodinQuotientBoundHistory_definable (θ i p f : V) :
    ℒₛₑₜ-function₁[V] (woodinQuotientBoundHistory θ i p f) := by
  unfold woodinQuotientBoundHistory definableGraph
  definability

/-- Only newly constructed two-step tails have a normalization obligation. -/
def IsWoodinBoundNormalizationAt (θ i p f j : V) : Prop :=
  i ∈ j →
    (j = succ (⋃ˢ j) →
      woodinQuotientBoundRec θ i p f (⋃ˢ j) ∈ atomicEquality
        ((forcingCodeP (woodinIterationPrefix j)) ‘ (⋃ˢ j))
        ((forcingCodeR (woodinIterationPrefix j)) ‘ (⋃ˢ j))
        (woodinBoundSuccessorTail θ i p f (⋃ˢ j)) (woodinBoundSuccessorRawTail θ i f (⋃ˢ j))) ∧
    (j ≠ succ (⋃ˢ j) →
      ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j)) →
      woodinQuotientBoundHistory θ i p f j ∈ atomicEquality
        (forcingInverseCodePoset j (woodinIterationPrefix j))
        (forcingInverseCodeOrder j (woodinIterationPrefix j))
        (woodinBoundInverseTail θ i p f j) (woodinBoundInverseRawTail θ i f j))

instance isWoodinBoundNormalizationAt_definable (θ i p f : V) :
    ℒₛₑₜ-predicate[V] (IsWoodinBoundNormalizationAt θ i p f) := by
  let : ℒₛₑₜ-function₄[V] atomicEquality := atomicEqualityFormula_defined.to_definable
  let : ℒₛₑₜ-relation[V] (fun x y : V ↦ x ∈ y) := by definability
  let : ℒₛₑₜ-relation₅[V] (fun q P R σ τ ↦ q ∈ atomicEquality P R σ τ) := by
    apply Language.DefinableRel.comp (P := fun x y : V ↦ x ∈ y)
    · definability
    · apply Language.DefinableFunction₄.comp (F := atomicEquality) <;> definability
  unfold IsWoodinBoundNormalizationAt
  apply Language.Definable.imp
  · definability
  · apply Language.Definable.and
    · apply Language.Definable.imp
      · definability
      · apply Language.DefinableRel₅.comp (P := fun q P R σ τ ↦ q ∈ atomicEquality P R σ τ) <;> definability
    · apply Language.Definable.imp
      · definability
      · apply Language.Definable.imp
        · definability
        · apply Language.DefinableRel₅.comp (P := fun q P R σ τ ↦ q ∈ atomicEquality P R σ τ) <;> definability

def IsWoodinNormalizedQuotientBoundAt (θ i p f α j : V) : Prop :=
  IsWoodinQuotientBoundAt θ i p f α j ∧ IsWoodinBoundNormalizationAt θ i p f j

instance isWoodinNormalizedQuotientBoundAt_definable (θ i p f α : V) :
    ℒₛₑₜ-predicate[V] (IsWoodinNormalizedQuotientBoundAt θ i p f α) := by
  unfold IsWoodinNormalizedQuotientBoundAt
  definability

end ZFVP
