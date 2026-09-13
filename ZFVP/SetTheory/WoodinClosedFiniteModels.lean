import ZFVP.SetTheory.BoundedDomainRelativization
import ZFVP.SetTheory.WoodinClosedContainers
import ZFVP.ModelTheory.InternalZFExternal

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def finiteModelContainerFormula (φ : SetTheorySentence) : SetTheorySemisentence 2 :=
  “a b. a ∈ b ∧ !IsTransitive.dfn b ∧ !(boundedDomainSentenceFormula φ) b”

theorem finiteModelContainerFormula_bounded (φ : SetTheorySentence) :
    IsBoundedSetFormula (finiteModelContainerFormula φ) :=
  .and (.rel _ _) (.and (isTransitiveFormula_bounded.subst _)
    ((boundedDomainSentenceFormula_bounded φ).subst _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinSupercompact.inaccessible_above {δ η : V}
    (hδ : IsWoodinSupercompact δ) (hη : η ∈ δ) :
    ∃ κ ∈ δ, η ∈ κ ∧ IsChoicelessInaccessible κ := by
  let := hδ.1.1
  obtain ⟨γ, hδγ, hγ⟩ := sigmaOneStarCorrect_unbounded δ
  let := hγ.1.ordinal
  have h0γ : (∅ : V) ∈ hierarchy γ := (hierarchy_transitive γ).mem_trans empty_mem_ω
    (ordinal_mem_hierarchy_iff.mpr hγ.1.omega_lt)
  obtain ⟨_, ρ, _, hρ, _, _, e, he, κ, hc, heκ, _, hηκ⟩ :=
    hδ.highCritical.2.2 γ hδγ hγ ∅ h0γ η hη
  let := hρ.1.ordinal
  let := hc.ordinal
  let := hierarchy_transitive (succ ρ)
  let := hierarchy_transitive (succ γ)
  have hκρ := successorRankEmbedding_criticalPoint_lt_height he hc (heκ.symm ▸ hδγ)
  have hωρ : (ω : V) ∈ hierarchy (succ ρ) :=
    hierarchy_mono (by intro z hz; exact mem_succ_iff.mpr (Or.inr hz)) _
      (ordinal_mem_hierarchy_iff.mpr hρ.1.omega_lt)
  refine ⟨κ, heκ ▸ hc.lt_value he, hηκ, hc.ordinal, hc.omega_lt_of_omega_mem he hωρ, ?_⟩
  intro α hα g
  exact successorRankEmbedding_criticalPoint_no_rank_cofinalMap hρ.1 hγ.1 he hc hκρ
    (hierarchy_mem hα)

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_finiteModelContainerFormula (φ : SetTheorySentence) (a b : V) :
    (finiteModelContainerFormula φ).Evalb ![a, b] ↔
      a ∈ b ∧ IsTransitive b ∧ φ.Evalb (![] : Fin 0 → SetDomain b) := by
  simp [finiteModelContainerFormula, eval_boundedDomainSentenceFormula]

theorem IsWoodinSupercompact.exists_rankClosed_model {δ : V}
    (hδ : IsWoodinSupercompact δ) (φ : SetTheorySentence)
    (hφ : φ.Evalb (![] : Fin 0 → SetDomain (hierarchy δ))) (α a : V) [IsOrdinal α] :
    ∃ b : V, IsRankFunctionClosed α b ∧ a ∈ b ∧ IsTransitive b ∧
      φ.Evalb (![] : Fin 0 → SetDomain b) := by
  let := hδ.1.1
  obtain ⟨b, hc, hb⟩ := hδ.exists_functionClosed_spec (finiteModelContainerFormula_bounded φ)
    (fun u hu ↦ (eval_finiteModelContainerFormula φ u (hierarchy δ)).mpr
      ⟨hu, hierarchy_transitive δ, hφ⟩) α a
  exact ⟨b, hc, (eval_finiteModelContainerFormula φ a b).mp hb⟩

theorem IsSigmaOneStarCorrect.reflect_rankClosed_model {γ α a : V}
    (hγ : IsSigmaOneStarCorrect γ) (hα : α ∈ γ) (ha : a ∈ hierarchy γ)
    (φ : SetTheorySentence)
    (hex : ∃ b : V, IsRankFunctionClosed α b ∧ a ∈ b ∧ IsTransitive b ∧
      φ.Evalb (![] : Fin 0 → SetDomain b)) :
    ∃ b ∈ hierarchy γ, IsRankFunctionClosed α b ∧ a ∈ b ∧ IsTransitive b ∧
      φ.Evalb (![] : Fin 0 → SetDomain b) := by
  obtain ⟨b, hb, hc, ht⟩ := hγ.reflect hα ha (finiteModelContainerFormula_bounded φ) (by
    obtain ⟨b, hc, ht⟩ := hex
    exact ⟨b, hc, (eval_finiteModelContainerFormula φ a b).mpr ht⟩)
  exact ⟨b, hb, hc, (eval_finiteModelContainerFormula φ a b).mp ht⟩

theorem IsWoodinSupercompact.exists_rankClosed_zfConsequence {δ : V}
    (hδ : IsWoodinSupercompact δ) (φ : SetTheorySentence) (hφ : 𝗭𝗙 ⊢ φ)
    (α a : V) [IsOrdinal α] :
    ∃ b : V, IsRankFunctionClosed α b ∧ a ∈ b ∧ IsTransitive b ∧
      φ.Evalb (![] : Fin 0 → SetDomain b) := by
  let := hδ.1.1
  have hω : (ω : V) ∈ hierarchy δ := ordinal_mem_hierarchy_iff.mpr hδ.inaccessible.2.1
  let : Nonempty (SetDomain (hierarchy δ)) := ⟨⟨ω, hω⟩⟩
  let := hδ.inaccessible.internalZFModel.models_zf
  apply hδ.exists_rankClosed_model φ _ α a
  have hh := models_of_provable (M := SetDomain (hierarchy δ)) inferInstance hφ
  simpa [models_iff] using hh

end ZFVP
