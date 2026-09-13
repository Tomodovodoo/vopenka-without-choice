import ZFVP.ModelTheory.EmbeddingCofinality
import ZFVP.ModelTheory.InternalZFModel

/-! The full rank criterion has a parameter-free Pi-one definition. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def limitAboveOmegaFormula : SetTheorySemisentence 1 :=
  “θ. !IsOrdinal.dfn θ ∧ (∃ w ∈ θ, !boundedOmegaFormula w) ∧
    ∀ x ∈ θ, ∃ y ∈ θ, !boundedSuccFormula y x”

theorem limitAboveOmegaFormula_bounded : IsBoundedSetFormula limitAboveOmegaFormula :=
  .and (isOrdinalFormula_bounded.subst _) (.and
    (.exs (.bvar 0) (boundedOmegaFormula_bounded.subst _))
    (.all (.bvar 0) (.exs (.bvar 1) (boundedSuccFormula_bounded.subst ![.bvar 0, .bvar 1]))))

def noLowRankCofinalMapsFormula : SetTheorySemisentence 1 :=
  “θ. ∀ a f r, (!sigmaOneRankFormula r a ∧ r ∈ θ) → ¬!boundedCofinalMapFormula θ a f”

theorem noLowRankCofinalMapsFormula_piOne : IsPiFormula 1 noLowRankCofinalMapsFormula :=
  .all (.all (.all (.or
    (IsLevyFormula.and (sigmaOneRankFormula_sigmaOne.subst ![.bvar 0, .bvar 2]) (.bounded (.rel _ _))).neg
    (.bounded (boundedCofinalMapFormula_bounded.subst ![.bvar 3, .bvar 2, .bvar 1]).neg))))

def rankCriterionFormula : SetTheorySemisentence 1 :=
  limitAboveOmegaFormula.and noLowRankCofinalMapsFormula

theorem rankCriterionFormula_piOne : IsPiFormula 1 rankCriterionFormula :=
  .and (.bounded limitAboveOmegaFormula_bounded) noLowRankCofinalMapsFormula_piOne

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsRankCriterionHeight (θ : V) : Prop :=
  IsOrdinal θ ∧ (ω : V) ∈ θ ∧ (∀ β ∈ θ, succ β ∈ θ) ∧ NoLowRankCofinalMaps θ

theorem eval_limitAboveOmegaFormula (θ : V) : limitAboveOmegaFormula.Evalb ![θ] ↔
    IsOrdinal θ ∧ (ω : V) ∈ θ ∧ ∀ β ∈ θ, succ β ∈ θ := by
  simp [limitAboveOmegaFormula]

theorem eval_noLowRankCofinalMapsFormula (θ : V) [IsOrdinal θ] :
    noLowRankCofinalMapsFormula.Evalb ![θ] ↔ NoLowRankCofinalMaps θ := by
  simp [noLowRankCofinalMapsFormula, NoLowRankCofinalMaps, mem_hierarchy_iff_rank_mem]
  exact ⟨fun h a ha f ↦ h a f ha, fun h a f ha ↦ h a ha f⟩

theorem eval_rankCriterionFormula (θ : V) : rankCriterionFormula.Evalb ![θ] ↔ IsRankCriterionHeight θ := by
  change (limitAboveOmegaFormula.Evalb ![θ] ∧ noLowRankCofinalMapsFormula.Evalb ![θ]) ↔ _
  rw [eval_limitAboveOmegaFormula]
  constructor
  · rintro ⟨⟨ho, hω, hs⟩, hn⟩
    let := ho
    exact ⟨ho, hω, hs, (eval_noLowRankCofinalMapsFormula θ).mp hn⟩
  · rintro ⟨ho, hω, hs, hn⟩
    let := ho
    exact ⟨⟨ho, hω, hs⟩, (eval_noLowRankCofinalMapsFormula θ).mpr hn⟩

instance rankCriterionFormula_defined : ℒₛₑₜ-predicate[V] IsRankCriterionHeight via rankCriterionFormula :=
  ⟨fun v ↦ by
    have hv : ![v 0] = v := by funext i; exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
    change rankCriterionFormula.Evalb v ↔ IsRankCriterionHeight (v 0)
    rw [← hv]
    exact eval_rankCriterionFormula (v 0)⟩

instance isRankCriterionHeight_definable : ℒₛₑₜ-predicate[V] IsRankCriterionHeight :=
  rankCriterionFormula_defined.to_definable

theorem IsRankCriterionHeight.internalZFModel {θ : V} (hθ : IsRankCriterionHeight θ) :
    IsInternalZFModel (hierarchy θ) := by
  let := hθ.1
  exact rank_isInternalZFModel hθ.2.1 hθ.2.2.1 hθ.2.2.2

theorem IsRankCriterionHeight.models_zf {θ : V} [Nonempty (SetDomain (hierarchy θ))]
    (hθ : IsRankCriterionHeight θ) : (SetDomain (hierarchy θ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  let := hθ.1
  exact rankDomain_models_zf hθ.2.1 hθ.2.2.1 hθ.2.2.2

end ZFVP
