import ZFVP.SetTheory.BoundedDomainParameters
import ZFVP.ModelTheory.WoodinLocalRestorationRankAgreement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def localRestorationRankThresholdFormula : SetTheorySemisentence 3 :=
  f“κ γ η. κ ∈ η ∧ γ ∈ η ∧ ∀ ξ, η ∈ ξ → !choicelessInaccessibleFormula ξ →
    (!(boundedDomainParametersFormula woodinLocalRestorationFormula) (!hierarchyFormula ξ) κ γ ↔
      !woodinLocalRestorationFormula κ γ)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsLocalRestorationRankThreshold (κ γ η : V) : Prop := κ ∈ η ∧ γ ∈ η ∧
  ∀ ξ, η ∈ ξ → IsChoicelessInaccessible ξ →
    ((boundedDomainParametersFormula woodinLocalRestorationFormula).Evalb ![hierarchy ξ, κ, γ] ↔
      IsWoodinLocalRestoration κ γ)

instance localRestorationRankThresholdFormula_defined :
    ℒₛₑₜ-relation₃[V] IsLocalRestorationRankThreshold via localRestorationRankThresholdFormula :=
  ⟨fun v ↦ by simp [localRestorationRankThresholdFormula, IsLocalRestorationRankThreshold]⟩

instance localRestorationRankThreshold_definable : ℒₛₑₜ-relation₃[V] IsLocalRestorationRankThreshold :=
  localRestorationRankThresholdFormula_defined.to_definable

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_domain_localRestoration (U : V) [Nonempty (SetDomain U)]
    [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (k d : SetDomain U) :
    (boundedDomainParametersFormula woodinLocalRestorationFormula).Evalb ![U, k.val, d.val] ↔
      IsWoodinLocalRestoration k d := by
  have hv : (fun i : Fin 2 ↦ ((![k, d] : Fin 2 → SetDomain U) i).val) = ![k.val, d.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun z ↦ Fin.elim0 z) j) i
  have he := eval_boundedDomainParametersFormula woodinLocalRestorationFormula U ![k, d]
  rw [hv] at he
  exact he.trans (Defined.eval_iff (φ := woodinLocalRestorationFormula) ![k, d])

theorem localRestorationRankThreshold_iff (κ γ η : V) : IsLocalRestorationRankThreshold κ γ η ↔
    κ ∈ η ∧ γ ∈ η ∧ ∀ ξ, η ∈ ξ → ∀ hξ : IsChoicelessInaccessible ξ,
      letI := hξ.1
      letI := rankDomain_nonempty hξ.2.1
      letI := hξ.rankCriterion.models_zf
      ∀ k d : SetDomain (hierarchy ξ), k.val = κ → d.val = γ →
        (IsWoodinLocalRestoration k d ↔ IsWoodinLocalRestoration κ γ) := by
  constructor
  · rintro ⟨hκη, hγη, h⟩
    refine ⟨hκη, hγη, ?_⟩
    intro ξ hηξ hξ
    let := hξ.1
    let := rankDomain_nonempty hξ.2.1
    let := hξ.rankCriterion.models_zf
    intro k d hk hd
    have he := eval_domain_localRestoration (hierarchy ξ) k d
    rw [hk, hd] at he
    exact he.symm.trans (h ξ hηξ hξ)
  · rintro ⟨hκη, hγη, h⟩
    refine ⟨hκη, hγη, ?_⟩
    intro ξ hηξ hξ
    let := hξ.1
    let := rankDomain_nonempty hξ.2.1
    let := hξ.rankCriterion.models_zf
    have hkξ := IsOrdinal.toIsTransitive.mem_trans hκη hηξ
    have hdξ := IsOrdinal.toIsTransitive.mem_trans hγη hηξ
    let := IsOrdinal.of_mem hkξ
    let := IsOrdinal.of_mem hdξ
    let k : SetDomain (hierarchy ξ) := ⟨κ, ordinal_mem_hierarchy_iff.mpr hkξ⟩
    let d : SetDomain (hierarchy ξ) := ⟨γ, ordinal_mem_hierarchy_iff.mpr hdξ⟩
    exact (eval_domain_localRestoration (hierarchy ξ) k d).trans (h ξ hηξ hξ k d rfl rfl)

theorem IsLocalRestorationRankThreshold.mono {κ γ η β : V} [IsOrdinal β]
    (h : IsLocalRestorationRankThreshold κ γ η) (hηβ : η ∈ β) :
    IsLocalRestorationRankThreshold κ γ β := by
  refine ⟨IsOrdinal.toIsTransitive.mem_trans h.1 hηβ,
    IsOrdinal.toIsTransitive.mem_trans h.2.1 hηβ, ?_⟩
  intro ξ hβξ hξ
  let := hξ.1
  exact h.2.2 ξ (IsOrdinal.toIsTransitive.mem_trans hηβ hβξ) hξ

theorem IsWoodinSupercompact.localRestorationRankThreshold_exists {δ κ γ : V}
    (hδ : IsWoodinSupercompact δ) (hκ : IsRegularCardinal κ) (hκδ : κ ∈ δ) (hγδ : γ ∈ δ) :
    ∃ η ∈ δ, IsLocalRestorationRankThreshold κ γ η := by
  obtain ⟨η, hη, h⟩ := hδ.eventually_rank_localRestoration_iff hκ hκδ hγδ
  exact ⟨η, hη, (localRestorationRankThreshold_iff κ γ η).mpr h⟩

end ZFVP
