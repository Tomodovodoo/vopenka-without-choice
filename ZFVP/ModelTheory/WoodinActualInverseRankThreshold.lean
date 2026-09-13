import ZFVP.ModelTheory.WoodinActualInverseRankAgreement
import ZFVP.ModelTheory.WoodinSuccessorRankThreshold
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinActualInverseRankThresholdFormula : SetTheorySemisentence 2 :=
  f“θ η. θ ≠ !isEmpty → (∀ i ∈ θ, !succ.dfn i ∈ θ) →
    ∀ s, s = !woodinIterationPrefixFormula θ →
    ∀ K, K = !woodinIterationCardinalPrefixFormula θ →
    ¬!choicelessInaccessibleFormula (!woodinLimitCardinalFormula K) →
    ∀ ξ, η ∈ ξ → !choicelessInaccessibleFormula ξ →
    ∀ U, U = !hierarchyFormula ξ → θ ∈ U → s ∈ U → K ∈ U → ∀ z ∈ U,
      (!(boundedDomainParametersFormula woodinInverseSourceCodeFormula) U z θ s K ↔
        !woodinInverseSourceCodeFormula z θ s K) ∧
      (!(boundedDomainParametersFormula woodinInverseCardinalNextFormula) U z θ s K ↔
        !woodinInverseCardinalNextFormula z θ s K)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A threshold applies only to completed inverse branches, with the supplied actual
prefixes contained in the comparison rank. It makes no recursion-absoluteness claim. -/
def IsWoodinActualInverseRankThreshold (θ η : V) : Prop :=
  θ ≠ ∅ → (∀ i ∈ θ, succ i ∈ θ) →
    ∀ s, s = woodinIterationPrefix θ → ∀ K, K = woodinIterationCardinalPrefix θ →
    ¬IsChoicelessInaccessible (woodinLimitCardinal K) →
    ∀ ξ, η ∈ ξ → IsChoicelessInaccessible ξ → ∀ U, U = hierarchy ξ →
    θ ∈ U → s ∈ U → K ∈ U → ∀ z ∈ U,
      ((boundedDomainParametersFormula woodinInverseSourceCodeFormula).Evalb ![U, z, θ, s, K] ↔
        z = woodinInverseSourceCode θ s K) ∧
      ((boundedDomainParametersFormula woodinInverseCardinalNextFormula).Evalb ![U, z, θ, s, K] ↔
        z = woodinInverseCardinalNext θ s K)

instance woodinActualInverseRankThresholdFormula_defined :
    ℒₛₑₜ-relation[V] IsWoodinActualInverseRankThreshold via woodinActualInverseRankThresholdFormula :=
  ⟨fun v ↦ by simp [woodinActualInverseRankThresholdFormula, IsWoodinActualInverseRankThreshold]⟩

instance woodinActualInverseRankThreshold_definable :
    ℒₛₑₜ-relation[V] IsWoodinActualInverseRankThreshold :=
  woodinActualInverseRankThresholdFormula_defined.to_definable

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_domain_woodinInverseSourceCode (U : V) [Nonempty (SetDomain U)]
    [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (z t u C : SetDomain U) :
    (boundedDomainParametersFormula woodinInverseSourceCodeFormula).Evalb ![U, z.val, t.val, u.val, C.val] ↔
      z = woodinInverseSourceCode t u C := by
  have hv : (fun i : Fin 4 ↦ ((![z, t, u, C] : Fin 4 → SetDomain U) i).val) =
      ![z.val, t.val, u.val, C.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.elim0 m) l) k) j) i
  have he := eval_boundedDomainParametersFormula woodinInverseSourceCodeFormula U ![z, t, u, C]
  rw [hv] at he
  exact he.trans (Defined.eval_iff (φ := woodinInverseSourceCodeFormula) ![z, t, u, C])

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_domain_woodinInverseCardinalNext (U : V) [Nonempty (SetDomain U)]
    [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (z t u C : SetDomain U) :
    (boundedDomainParametersFormula woodinInverseCardinalNextFormula).Evalb ![U, z.val, t.val, u.val, C.val] ↔
      z = woodinInverseCardinalNext t u C := by
  have hv : (fun i : Fin 4 ↦ ((![z, t, u, C] : Fin 4 → SetDomain U) i).val) =
      ![z.val, t.val, u.val, C.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.elim0 m) l) k) j) i
  have he := eval_boundedDomainParametersFormula woodinInverseCardinalNextFormula U ![z, t, u, C]
  rw [hv] at he
  exact he.trans (Defined.eval_iff (φ := woodinInverseCardinalNextFormula) ![z, t, u, C])

theorem IsWoodinActualInverseRankThreshold.mono {θ η β : V} [IsOrdinal β]
    (h : IsWoodinActualInverseRankThreshold θ η) (hηβ : η ∈ β) :
    IsWoodinActualInverseRankThreshold θ β := by
  intro hz hl s hs K hK hn ξ hβξ hξ
  let := hξ.1
  exact h hz hl s hs K hK hn ξ (IsOrdinal.toIsTransitive.mem_trans hηβ hβξ) hξ

theorem woodinActualInverseRankThreshold_exists {δ θ : V} [IsOrdinal θ]
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (hθ : θ ∈ δ) :
    ∃ η ∈ δ, IsWoodinActualInverseRankThreshold θ η := by
  classical
  by_cases hb : θ ≠ ∅ ∧ (∀ i ∈ θ, succ i ∈ θ) ∧
      ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))
  · have h0 : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left
      (fun he ↦ hb.1 he.symm)
    obtain ⟨η, hηδ, _, hall⟩ :=
      woodinIteration_eventually_rank_inverseSourceCode_eq hδ hAC hθ h0 hb.2.1 hb.2.2
    refine ⟨η, hηδ, ?_⟩
    intro _ _ s hs K hK _ ξ hηξ hξ U hU hθU hsU hKU z hzU
    subst U
    let := hξ.1
    let := rankDomain_nonempty hξ.2.1
    let := hξ.rankCriterion.models_zf
    let t : SetDomain (hierarchy ξ) := ⟨θ, hθU⟩
    let u : SetDomain (hierarchy ξ) := ⟨s, hsU⟩
    let C : SetDomain (hierarchy ξ) := ⟨K, hKU⟩
    let w : SetDomain (hierarchy ξ) := ⟨z, hzU⟩
    have he := hall ξ hηξ hξ t u C rfl hs hK
    rw [← hs, ← hK] at he
    constructor
    · apply (eval_domain_woodinInverseSourceCode (hierarchy ξ) w t u C).trans
      constructor
      · intro hh
        exact (congrArg Subtype.val hh).trans he.1
      · intro hh
        exact Subtype.ext (hh.trans he.1.symm)
    · apply (eval_domain_woodinInverseCardinalNext (hierarchy ξ) w t u C).trans
      constructor
      · intro hh
        exact (congrArg Subtype.val hh).trans he.2
      · intro hh
        exact Subtype.ext (hh.trans he.2.symm)
  · refine ⟨θ, hθ, ?_⟩
    intro hz hl s hs K hK hn
    exact (hb ⟨hz, hl, hK ▸ hn⟩).elim


theorem IsWoodinActualInverseRankThreshold.agreement {θ η ξ : V}
    (h : IsWoodinActualInverseRankThreshold θ η) (h0 : θ ≠ ∅)
    (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hηξ : η ∈ ξ) (hξ : IsChoicelessInaccessible ξ) :
    letI := hξ.1
    letI := rankDomain_nonempty hξ.2.1
    letI := hξ.rankCriterion.models_zf
    ∀ t u C : SetDomain (hierarchy ξ), t.val = θ →
      u.val = woodinIterationPrefix θ → C.val = woodinIterationCardinalPrefix θ →
      (woodinInverseSourceCode t u C).val =
        woodinInverseSourceCode θ (woodinIterationPrefix θ) (woodinIterationCardinalPrefix θ) ∧
      (woodinInverseCardinalNext t u C).val =
        woodinInverseCardinalNext θ (woodinIterationPrefix θ) (woodinIterationCardinalPrefix θ) := by
  let := hξ.1
  let := rankDomain_nonempty hξ.2.1
  let := hξ.rankCriterion.models_zf
  intro t u C ht hu hC
  have hf := h h0 hlim u.val hu C.val hC (hC ▸ hn) ξ hηξ hξ
    (hierarchy ξ) rfl (ht ▸ t.property) u.property C.property
  constructor
  · have he := eval_domain_woodinInverseSourceCode (hierarchy ξ) (woodinInverseSourceCode t u C) t u C
    rw [ht] at he
    have hh := (hf _ (woodinInverseSourceCode t u C).property).1.mp (he.mpr rfl)
    simpa only [hu, hC] using hh
  · have he := eval_domain_woodinInverseCardinalNext (hierarchy ξ) (woodinInverseCardinalNext t u C) t u C
    rw [ht] at he
    have hh := (hf _ (woodinInverseCardinalNext t u C).property).2.mp (he.mpr rfl)
    simpa only [hu, hC] using hh

/-- One ordinal bounds all completed inverse branch thresholds below a fixed
length. Collection is applied to a definable relation, without choosing thresholds. -/
theorem woodinActualInverseRankThreshold_bounded {δ α : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) (hα : α ∈ δ) :
    ∃ η ∈ δ, ∀ θ ∈ α, IsWoodinActualInverseRankThreshold θ η := by
  let := hδ.inaccessible.1
  let := IsOrdinal.of_mem hα
  let R : V → V → Prop := fun θ η ↦ IsOrdinal η ∧ IsWoodinActualInverseRankThreshold θ η
  have hR : ℒₛₑₜ-relation R := by unfold R; definability
  have hex : ∀ θ ∈ α, ∃ η ∈ hierarchy δ, R θ η := by
    intro θ hθα
    let := IsOrdinal.of_mem hθα
    obtain ⟨η, hη, ht⟩ := woodinActualInverseRankThreshold_exists hδ hAC
      (IsOrdinal.toIsTransitive.mem_trans hθα hα)
    let := IsOrdinal.of_mem hη
    exact ⟨η, ordinal_mem_hierarchy_iff.mpr hη, inferInstance, ht⟩
  obtain ⟨b, hb, hall⟩ := hδ.inaccessible.rankCriterion.2.2.2.collection
    (fun _ hx ↦ regularCardinal_succ_closed hδ.inaccessible.regular hx)
    (ordinal_mem_hierarchy_iff.mpr hα) R hR hex
  refine ⟨rank b, (mem_hierarchy_iff_rank_mem _ _).mp hb, ?_⟩
  intro θ hθα
  obtain ⟨η, hηb, hord, ht⟩ := hall θ hθα
  let := hord
  have hη : η ∈ rank b := ordinal_mem_hierarchy_iff.mp
    ((mem_hierarchy_iff_rank_mem _ _).mpr (rank_mem hηb))
  exact ht.mono hη

end ZFVP
