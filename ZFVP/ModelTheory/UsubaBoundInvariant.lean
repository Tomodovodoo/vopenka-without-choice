import ZFVP.ModelTheory.UsubaBoundCoherence
import ZFVP.ModelTheory.ProjectionQuotientSequenceForcing
import ZFVP.SetTheory.AtomicForcingDictionary

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)

attribute [local instance] DefinableForcingTower.P_definable DefinableForcingTower.R_definable
  DefinableForcingTower.top_definable DefinableForcingTower.projection_definable
  DefinableForcingTower.section_definable

def ForcesUsubaQuotientSequence (θ i p f α : V) : Prop :=
  p ∈ forcingFormula ((T).P i) ((T).R i) forcingSeparativeDescendingFormula
    (standardTuple ![projectionQuotientName ((T).P θ) ((T).projection i θ) ((T).top i),
      projectionQuotientOrderName ((T).R θ) ((T).projection i θ) ((T).top i),
      checkName ((T).top i) α, f])

def IsUsubaQuotientBoundAt (θ i p f α j : V) : Prop :=
  usubaQuotientBoundRec θ i p f j ∈ (T).P j ∧
    (i ⊆ j → p ∈ forcingFormula ((T).P i) ((T).R i) forcingSeparativeBoundFormula
      (standardTuple ![projectionQuotientName ((T).P j) ((T).projection i j) ((T).top i),
        projectionQuotientOrderName ((T).R j) ((T).projection i j) ((T).top i),
        checkName ((T).top i) α, usubaBoundCoordinateName θ i f j,
        checkName ((T).top i) (usubaQuotientBoundRec θ i p f j)]))

instance isUsubaQuotientBoundAt_definable (θ i p f α : V) :
    ℒₛₑₜ-predicate[V] (IsUsubaQuotientBoundAt θ i p f α) := by
  unfold IsUsubaQuotientBoundAt
  apply Language.Definable.and
  · definability
  · apply Language.Definable.imp
    · definability
    · apply Language.DefinableRel₄.comp
        (P := fun p B R v ↦ p ∈ forcingFormula B R forcingSeparativeBoundFormula v)
      · definability
      · definability
      · definability
      · simp only [standardTuple]
        definability

def IsUsubaBoundNormalizationAt (θ i p f j : V) : Prop :=
  i ∈ j → j = succ (⋃ˢ j) →
    usubaQuotientBoundRec θ i p f (⋃ˢ j) ∈
      atomicEquality ((T).P (⋃ˢ j)) ((T).R (⋃ˢ j))
        (usubaBoundSuccessorTail θ i p f (⋃ˢ j)) (usubaBoundSuccessorRawTail θ i f (⋃ˢ j))

instance isUsubaBoundNormalizationAt_definable (θ i p f : V) :
    ℒₛₑₜ-predicate[V] (IsUsubaBoundNormalizationAt θ i p f) := by
  let : ℒₛₑₜ-function₄[V] atomicEquality := atomicEqualityFormula_defined.to_definable
  let : ℒₛₑₜ-relation[V] (fun x y : V ↦ x ∈ y) := by definability
  let : ℒₛₑₜ-relation₅[V] (fun q P R σ τ ↦ q ∈ atomicEquality P R σ τ) := by
    apply Language.DefinableRel.comp (P := fun x y : V ↦ x ∈ y)
    · definability
    · apply Language.DefinableFunction₄.comp (F := atomicEquality) <;> definability
  unfold IsUsubaBoundNormalizationAt
  apply Language.Definable.imp
  · definability
  · apply Language.Definable.imp
    · definability
    · apply Language.DefinableRel₅.comp
        (P := fun q P R σ τ ↦ q ∈ atomicEquality P R σ τ) <;> definability

def IsUsubaNormalizedQuotientBoundAt (θ i p f α j : V) : Prop :=
  IsUsubaQuotientBoundAt θ i p f α j ∧ IsUsubaBoundNormalizationAt θ i p f j

instance isUsubaNormalizedQuotientBoundAt_definable (θ i p f α : V) :
    ℒₛₑₜ-predicate[V] (IsUsubaNormalizedQuotientBoundAt θ i p f α) := by
  unfold IsUsubaNormalizedQuotientBoundAt
  definability

noncomputable def usubaStageContext (i : V) [IsOrdinal i] {G : Set V}
    (hG : IsExternalForcingGeneric ((T).P i) ((T).R i) G) : ForcingContext V :=
  ⟨(T).P i, (T).R i, (T).top i, G, (T).order i inferInstance, (T).top_spec i inferInstance, hG⟩

theorem usubaQuotientSequence_semantics {θ i p α : V} [IsOrdinal θ] [IsOrdinal i]
    (hiθ : i ⊆ θ) (f : ForcingName ((T).P i))
    (hf : ForcesUsubaQuotientSequence θ i p f.val α)
    {G : Set V} (hG : IsExternalForcingGeneric ((T).P i) ((T).R i) G) (hpG : p ∈ G) :
    let A := usubaStageContext i hG
    IsForcingDescending (A.projectionQuotient ((T).P θ) ((T).projection i θ))
      (forcingSeparativeOrder (A.projectionQuotient ((T).P θ) ((T).projection i θ))
        (A.projectionQuotientOrder ((T).P θ) ((T).R θ) ((T).projection i θ)))
      (A.check α) (A.ofName f) :=
  (usubaStageContext i hG).projectionQuotient_descending_of_forced
    ((T).splitProjection hiθ).projection ((T).order θ inferInstance) f hpG hf

theorem usubaQuotientBoundAt_iff_generics [Countable V]
    {θ i p α j : V} [IsOrdinal i] [IsOrdinal j] (hij : i ⊆ j)
    (hp : p ∈ (T).P i) (f : ForcingName ((T).P i)) :
    IsUsubaQuotientBoundAt θ i p f.val α j ↔
      usubaQuotientBoundRec θ i p f.val j ∈ (T).P j ∧
      ∀ (G : Set V) (hG : IsExternalForcingGeneric ((T).P i) ((T).R i) G), p ∈ G →
        let A := usubaStageContext i hG
        let μ : ForcingName A.P := ⟨usubaBoundCoordinateName θ i f.val j, usubaBoundCoordinateName_isName _ _ _ _⟩
        A.check (usubaQuotientBoundRec θ i p f.val j) ∈ A.projectionQuotient ((T).P j) ((T).projection i j) ∧
          ∀ a ∈ A.check α,
            ⟨A.check (usubaQuotientBoundRec θ i p f.val j), (A.ofName μ) ‘ a⟩ₖ ∈
              forcingSeparativeOrder (A.projectionQuotient ((T).P j) ((T).projection i j))
                (A.projectionQuotientOrder ((T).P j) ((T).R j) ((T).projection i j)) := by
  let μ : ForcingName ((T).P i) :=
    ⟨usubaBoundCoordinateName θ i f.val j, usubaBoundCoordinateName_isName _ _ _ _⟩
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro G hG hpG
    exact (usubaStageContext i hG).projectionQuotient_bound_of_forced
      ((T).splitProjection hij).projection ((T).order j inferInstance) μ hpG (h.2 hij)
  · rintro ⟨hm, hb⟩
    exact ⟨hm, fun _ ↦ projectionQuotient_bound_forced_of_generics
      ((T).order i inferInstance) ((T).top_spec i inferInstance)
      ((T).splitProjection hij).projection ((T).order j inferInstance) hp μ hb⟩

end ZFVP
