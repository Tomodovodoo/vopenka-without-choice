import ZFVP.ModelTheory.WoodinSuccessorStepRankAgreement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinSuccessorRankThresholdFormula : SetTheorySemisentence 2 :=
  f“X η. ∀ ξ, η ∈ ξ → !choicelessInaccessibleFormula ξ →
    ∀ U, U = !hierarchyFormula ξ → X ∈ U → ∀ z ∈ U,
      (!(boundedDomainParametersFormula woodinSuccessorStepFormula) U z X ↔
        !woodinSuccessorStepFormula z X)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsWoodinSuccessorRankThreshold (X η : V) : Prop :=
  ∀ ξ, η ∈ ξ → IsChoicelessInaccessible ξ → ∀ U, U = hierarchy ξ →
    X ∈ U → ∀ z ∈ U,
      ((boundedDomainParametersFormula woodinSuccessorStepFormula).Evalb ![U, z, X] ↔
        z = woodinSuccessorStep X)

instance woodinSuccessorRankThresholdFormula_defined :
    ℒₛₑₜ-relation[V] IsWoodinSuccessorRankThreshold via woodinSuccessorRankThresholdFormula :=
  ⟨fun v ↦ by simp [woodinSuccessorRankThresholdFormula, IsWoodinSuccessorRankThreshold]⟩

instance woodinSuccessorRankThreshold_definable : ℒₛₑₜ-relation[V] IsWoodinSuccessorRankThreshold :=
  woodinSuccessorRankThresholdFormula_defined.to_definable

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_domain_woodinSuccessorStep (U : V) [Nonempty (SetDomain U)]
    [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (z x : SetDomain U) :
    (boundedDomainParametersFormula woodinSuccessorStepFormula).Evalb ![U, z.val, x.val] ↔
      z = woodinSuccessorStep x := by
  have hv : (fun i : Fin 2 ↦ ((![z, x] : Fin 2 → SetDomain U) i).val) = ![z.val, x.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
  have he := eval_boundedDomainParametersFormula woodinSuccessorStepFormula U ![z, x]
  rw [hv] at he
  exact he.trans (Defined.eval_iff (φ := woodinSuccessorStepFormula) ![z, x])

theorem IsWoodinSuccessorRankThreshold.mono {X η β : V} [IsOrdinal β]
    (h : IsWoodinSuccessorRankThreshold X η) (hηβ : η ∈ β) :
    IsWoodinSuccessorRankThreshold X β := by
  intro ξ hβξ hξ
  let := hξ.1
  exact h ξ (IsOrdinal.toIsTransitive.mem_trans hηβ hβξ) hξ

theorem IsWoodinSupercompact.woodinSuccessorRankThreshold_exists {δ X : V}
    (hδ : IsWoodinSupercompact δ) (hX : IsWoodinStage X) (hsmall : IsWoodinStageSmall X)
    (hκδ : woodinStageCardinal X ∈ δ) :
    ∃ η ∈ δ, IsWoodinSuccessorRankThreshold X η := by
  obtain ⟨η, hηδ, _, hall⟩ := hδ.eventually_rank_woodinSuccessorStep_eq hX hsmall hκδ
  refine ⟨η, hηδ, ?_⟩
  intro ξ hηξ hξ U hU hXU z hzU
  subst U
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  let x : SetDomain (hierarchy ξ) := ⟨X, hXU⟩
  let w : SetDomain (hierarchy ξ) := ⟨z, hzU⟩
  have he := hall ξ hηξ hξ x rfl
  apply (eval_domain_woodinSuccessorStep (hierarchy ξ) w x).trans
  constructor
  · intro hh
    exact (congrArg Subtype.val hh).trans he
  · intro hh
    exact Subtype.ext (hh.trans he.symm)

theorem IsWoodinSuccessorRankThreshold.agreement {X η ξ : V}
    (h : IsWoodinSuccessorRankThreshold X η) (hηξ : η ∈ ξ)
    (hξ : IsChoicelessInaccessible ξ) :
    letI := hξ.1
    letI := rankDomain_nonempty hξ.2.1
    letI := hξ.rankCriterion.models_zf
    ∀ x : SetDomain (hierarchy ξ), x.val = X →
      (woodinSuccessorStep x).val = woodinSuccessorStep X := by
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  intro x hx
  have he := eval_domain_woodinSuccessorStep (hierarchy ξ) (woodinSuccessorStep x) x
  rw [hx] at he
  exact (h ξ hηξ hξ (hierarchy ξ) rfl (hx ▸ x.property)
    (woodinSuccessorStep x).val (woodinSuccessorStep x).property).mp (he.mpr rfl)

theorem IsWoodinSupercompact.bounded_woodinSuccessorRankThreshold {δ A : V}
    (hδ : IsWoodinSupercompact δ) (hA : A ∈ hierarchy δ)
    (hstage : ∀ X ∈ A, IsWoodinStage X)
    (hsmall : ∀ X ∈ A, IsWoodinStageSmall X)
    (hκ : ∀ X ∈ A, woodinStageCardinal X ∈ δ) :
    ∃ η ∈ δ, ∀ X ∈ A, IsWoodinSuccessorRankThreshold X η := by
  let := hδ.1.1
  let T : V → V → Prop := fun X η ↦ IsOrdinal η ∧ IsWoodinSuccessorRankThreshold X η
  have hT : ℒₛₑₜ-relation T := by unfold T; definability
  have hex : ∀ X ∈ A, ∃ η ∈ hierarchy δ, T X η := by
    intro X hXA
    obtain ⟨η, hη, ht⟩ := hδ.woodinSuccessorRankThreshold_exists
      (hstage X hXA) (hsmall X hXA) (hκ X hXA)
    let := IsOrdinal.of_mem hη
    exact ⟨η, ordinal_mem_hierarchy_iff.mpr hη, inferInstance, ht⟩
  obtain ⟨b, hb, hall⟩ := hδ.inaccessible.rankCriterion.2.2.2.collection
    (fun _ hx ↦ regularCardinal_succ_closed hδ.inaccessible.regular hx) hA T hT hex
  refine ⟨rank b, (mem_hierarchy_iff_rank_mem _ _).mp hb, ?_⟩
  intro X hXA
  obtain ⟨η, hηb, hord, ht⟩ := hall X hXA
  let := hord
  have hη : η ∈ rank b := ordinal_mem_hierarchy_iff.mp
    ((mem_hierarchy_iff_rank_mem _ _).mpr (rank_mem hηb))
  exact ht.mono hη

end ZFVP
