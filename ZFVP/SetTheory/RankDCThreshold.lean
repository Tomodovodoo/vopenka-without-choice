import ZFVP.SetTheory.BoundedDomainUnary
import ZFVP.SetTheory.OrdinalDependentChoice
import ZFVP.SetTheory.ChoicelessInaccessibleRank
import ZFVP.SetTheory.UniformLeastOrdinalChoice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def rankDCThresholdFormula : SetTheorySemisentence 2 :=
  f“γ η. γ ∈ η ∧ ∀ ξ, η ∈ ξ → !choicelessInaccessibleFormula ξ →
    ∀ κ ∈ γ, κ ∈ !hierarchyFormula ξ →
      (!(boundedDomainUnaryFormula dependentChoiceAtFormula) (!hierarchyFormula ξ) κ ↔
        !dependentChoiceAtFormula κ)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsRankDCThreshold (γ η : V) : Prop := γ ∈ η ∧
  ∀ ξ, η ∈ ξ → IsChoicelessInaccessible ξ → ∀ κ ∈ γ, κ ∈ hierarchy ξ →
    ((boundedDomainUnaryFormula dependentChoiceAtFormula).Evalb ![hierarchy ξ, κ] ↔
      InternalDependentChoiceAt κ)

instance rankDCThresholdFormula_defined :
    ℒₛₑₜ-relation[V] IsRankDCThreshold via rankDCThresholdFormula :=
  ⟨fun v ↦ by simp [rankDCThresholdFormula, IsRankDCThreshold]⟩

instance rankDCThreshold_definable : ℒₛₑₜ-relation[V] IsRankDCThreshold :=
  rankDCThresholdFormula_defined.to_definable

theorem rankDCThreshold_iff (γ η : V) : IsRankDCThreshold γ η ↔ γ ∈ η ∧
    ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      ∀ κ : SetDomain (hierarchy ξ), κ.val ∈ γ →
        (InternalDependentChoiceAt κ ↔ InternalDependentChoiceAt κ.val) := by
  constructor
  · rintro ⟨hγη, h⟩
    refine ⟨hγη, ?_⟩
    intro ξ hηξ hξ
    let := hξ.1
    let := rankDomain_nonempty hξ.2.1
    let := hξ.rankCriterion.models_zf
    intro κ hκ
    have he := eval_boundedDomainUnaryFormula dependentChoiceAtFormula (hierarchy ξ) κ
    have he' : (boundedDomainUnaryFormula dependentChoiceAtFormula).Evalb ![hierarchy ξ, κ.val] ↔
        InternalDependentChoiceAt κ := by simpa using he
    exact he'.symm.trans (h ξ hηξ hξ κ.val hκ κ.property)
  · rintro ⟨hγη, h⟩
    refine ⟨hγη, ?_⟩
    intro ξ hηξ hξ κ hκ hκξ
    let := hξ.1
    let := rankDomain_nonempty hξ.2.1
    let := hξ.rankCriterion.models_zf
    let k : SetDomain (hierarchy ξ) := ⟨κ, hκξ⟩
    have he := eval_boundedDomainUnaryFormula dependentChoiceAtFormula (hierarchy ξ) k
    have he' : (boundedDomainUnaryFormula dependentChoiceAtFormula).Evalb ![hierarchy ξ, κ] ↔
        InternalDependentChoiceAt k := by simpa using he
    exact he'.trans (h ξ hηξ hξ k hκ)

theorem IsRankDCThreshold.mono {γ η β : V} [IsOrdinal β]
    (h : IsRankDCThreshold γ η) (hηβ : η ∈ β) : IsRankDCThreshold γ β := by
  refine ⟨IsOrdinal.toIsTransitive.mem_trans h.1 hηβ, ?_⟩
  intro ξ hβξ hξ κ hκ hκξ
  let := hξ.1
  exact h.2 ξ (IsOrdinal.toIsTransitive.mem_trans hηβ hβξ) hξ κ hκ hκξ

noncomputable def leastRankDCThreshold (γ : V) : V :=
  leastOrdinalOrZero IsRankDCThreshold (by definability) γ

def leastRankDCThresholdFormula : SetTheorySemisentence 2 :=
  leastOrdinalOrZeroFormula rankDCThresholdFormula

theorem eval_leastRankDCThresholdFormula (η γ : V) :
    leastRankDCThresholdFormula.Evalb ![η, γ] ↔ η = leastRankDCThreshold γ := by
  exact eval_leastOrdinalOrZeroFormula rankDCThresholdFormula IsRankDCThreshold
    (by definability) (fun x y ↦ by simp) η γ

theorem leastRankDCThreshold_spec {δ γ η : V} [IsOrdinal δ]
    (hη : η ∈ δ) (ht : IsRankDCThreshold γ η) :
    leastRankDCThreshold γ ∈ δ ∧ IsRankDCThreshold γ (leastRankDCThreshold γ) := by
  let := IsOrdinal.of_mem hη
  have hs := leastOrdinalOrZero_spec IsRankDCThreshold (by definability) γ ⟨η, inferInstance, ht⟩
  let : IsOrdinal (leastRankDCThreshold γ) := hs.1
  exact ⟨ordinal_mem_of_subset_mem (hs.2.2 η inferInstance ht) hη, hs.2.1⟩

end ZFVP
