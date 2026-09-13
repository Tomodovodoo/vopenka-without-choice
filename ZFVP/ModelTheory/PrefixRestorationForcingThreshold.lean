import ZFVP.ModelTheory.PrefixRestorationForcingAgreement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsPrefixRestorationForcingThreshold (P R one κ γ β : V) : Prop := γ ∈ β ∧
  ∀ ξ, β ∈ ξ → IsChoicelessInaccessible ξ → P ∈ hierarchy ξ →
    checkName one κ ∈ hierarchy ξ → checkName one γ ∈ hierarchy ξ →
    prefixRestorationForcingAgreementFormula.Evalb ![P, R, one, κ, γ, ξ]

private theorem threshold_relation_definable (F : V → V → Prop) (hF : ℒₛₑₜ-relation F)
    (P one κ : V) : ℒₛₑₜ-relation[V] (fun γ β ↦ γ ∈ β ∧
      ∀ ξ, β ∈ ξ → IsChoicelessInaccessible ξ → P ∈ hierarchy ξ →
        checkName one κ ∈ hierarchy ξ → checkName one γ ∈ hierarchy ξ → F γ ξ) := by
  definability

instance prefixRestorationForcingThreshold_definable (P R one κ : V) :
    ℒₛₑₜ-relation[V] (IsPrefixRestorationForcingThreshold P R one κ) := by
  have hφ : Language.Definable ℒₛₑₜ (fun v : Fin 6 → V ↦
      prefixRestorationForcingAgreementFormula.Evalb v) :=
    (show Defined (fun v : Fin 6 → V ↦ prefixRestorationForcingAgreementFormula.Evalb v)
      prefixRestorationForcingAgreementFormula from ⟨fun _ ↦ Iff.rfl⟩).to_definable
  have hF : ℒₛₑₜ-relation[V] (fun γ ξ ↦
      prefixRestorationForcingAgreementFormula.Evalb ![P, R, one, κ, γ, ξ]) := by
    apply Language.Definable.substitution hφ
      (f := fun i v ↦ (![P, R, one, κ, v 0, v 1] : Fin 6 → V) i)
    intro i
    exact Fin.cases (by definability) (fun j ↦ Fin.cases (by definability)
      (fun k ↦ Fin.cases (by definability) (fun l ↦ Fin.cases (by definability)
        (fun m ↦ Fin.cases (by definability) (fun n ↦ Fin.cases (by definability)
          (fun z ↦ Fin.elim0 z) n) m) l) k) j) i
  exact threshold_relation_definable _ hF P one κ

theorem IsPrefixRestorationForcingThreshold.forcing_eq {P R one κ γ β ξ : V}
    (h : IsPrefixRestorationForcingThreshold P R one κ γ β) (hβ : β ∈ ξ)
    (hξ : IsChoicelessInaccessible ξ) (hP : P ∈ hierarchy ξ)
    (hk : checkName one κ ∈ hierarchy ξ) (hg : checkName one γ ∈ hierarchy ξ) :
    classForcingFormula P R (IsLowRankForcingName P ξ) (by definability)
      woodinLocalRestorationFormula (standardTuple ![checkName one κ, checkName one γ]) =
    forcingFormula P R woodinLocalRestorationFormula
      (standardTuple ![checkName one κ, checkName one γ]) :=
  (Defined.eval_iff (φ := prefixRestorationForcingAgreementFormula) ![P, R, one, κ, γ, ξ]).mp
    (h.2 ξ hβ hξ hP hk hg)

theorem IsPrefixRestorationForcingThreshold.mono {P R one κ γ β η : V} [IsOrdinal η]
    (h : IsPrefixRestorationForcingThreshold P R one κ γ β) (hβη : β ∈ η) :
    IsPrefixRestorationForcingThreshold P R one κ γ η := by
  refine ⟨IsOrdinal.toIsTransitive.mem_trans h.1 hβη, ?_⟩
  intro ξ hηξ hξ hP hk hg
  let := hξ.1
  exact h.2 ξ (IsOrdinal.toIsTransitive.mem_trans hβη hηξ) hξ hP hk hg

theorem IsWoodinSupercompact.prefixRestorationForcingThreshold_exists {δ κ γ P R one : V}
    (hδ : IsWoodinSupercompact δ) (hP : P ∈ hierarchy δ) (hκδ : κ ∈ δ) (hγδ : γ ∈ δ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![checkName one κ])) :
    ∃ β ∈ δ, IsPrefixRestorationForcingThreshold P R one κ γ β := by
  obtain ⟨β, hβ, hγβ, hall⟩ := eventually_prefixRestoration_forcing_eq hδ hP hκδ hγδ hR ht hκ
  refine ⟨β, hβ, hγβ, ?_⟩
  intro ξ hβξ hξ hPξ hkξ hgξ
  exact (Defined.eval_iff (φ := prefixRestorationForcingAgreementFormula) _).mpr
    (hall ξ hβξ hξ hPξ hkξ hgξ)

theorem IsWoodinSupercompact.bounded_prefixRestorationForcingThreshold {δ κ θ P R one : V}
    (hδ : IsWoodinSupercompact δ) (hP : P ∈ hierarchy δ) (hκδ : κ ∈ δ) (hθδ : θ ∈ δ)
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![checkName one κ])) :
    ∃ η ∈ δ, ∀ γ ∈ θ, IsPrefixRestorationForcingThreshold P R one κ γ η := by
  let := hδ.1.1
  let := IsOrdinal.of_mem hθδ
  let T : V → V → Prop := fun γ η ↦ IsOrdinal η ∧ IsPrefixRestorationForcingThreshold P R one κ γ η
  have hT : ℒₛₑₜ-relation T := by unfold T; definability
  have hex : ∀ γ ∈ θ, ∃ η ∈ hierarchy δ, T γ η := by
    intro γ hγ
    obtain ⟨η, hη, hηT⟩ := hδ.prefixRestorationForcingThreshold_exists hP hκδ
      (IsOrdinal.toIsTransitive.mem_trans hγ hθδ) hR ht hκ
    let := IsOrdinal.of_mem hη
    exact ⟨η, ordinal_mem_hierarchy_iff.mpr hη, inferInstance, hηT⟩
  obtain ⟨b, hb, hall⟩ := hδ.inaccessible.rankCriterion.2.2.2.collection
    (fun _ hx ↦ regularCardinal_succ_closed hδ.inaccessible.regular hx)
    (ordinal_mem_hierarchy_iff.mpr hθδ) T hT hex
  refine ⟨rank b, (mem_hierarchy_iff_rank_mem _ _).mp hb, ?_⟩
  intro γ hγ
  obtain ⟨η, hηb, hηord, hηT⟩ := hall γ hγ
  let := hηord
  have hη : η ∈ rank b := ordinal_mem_hierarchy_iff.mp
    ((mem_hierarchy_iff_rank_mem _ _).mpr (rank_mem hηb))
  exact hηT.mono hη

end ZFVP
