import ZFVP.SetTheory.WoodinSupercompact
import ZFVP.ModelTheory.SupportStageEmbeddingAction
import ZFVP.ModelTheory.CriticalPointRestriction

/-! Magidor's step for Woodin's small-embedding supercompactness: a coded membership embedding
of a support stage `V_{lam+ω}` restricts to a small embedding witnessing
`WoodinSupercompactWitness` at the image point. Every clause is read off in `V`, so no
absoluteness or reflection is used. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Restricting an embedding of `V_{lam+ω}` to `V_{γ+1}` witnesses Woodin supercompactness at
the image triple: the inner ordinal is `γ` itself, which is `Sigma-one-star` correct in `V` and
sits below the critical value `f ‘ κ`. -/
theorem woodinSupercompactWitness_value_of_supportEmbedding {lam lam' f κ γ a : V}
    [IsOrdinal lam] [IsOrdinal lam']
    (hω : (ω : V) ∈ lam) (hsucc : ∀ ξ ∈ lam, succ ξ ∈ lam)
    (hω' : (ω : V) ∈ lam') (hsucc' : ∀ ξ ∈ lam', succ ξ ∈ lam')
    (hFlam : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy lam)
    (hf : IsCodedMembershipEmbedding (hierarchy (ordinalAdd lam ω))
      (hierarchy (ordinalAdd lam' ω)) f)
    (hκ : IsCriticalPoint (hierarchy (ordinalAdd lam ω)) f κ)
    (hγ : IsSigmaOneStarCorrect γ) (hκγ : κ ∈ γ) (hγlam : γ ∈ lam)
    (hγfκ : γ ∈ f ‘ κ) (ha : a ∈ hierarchy γ) :
    WoodinSupercompactWitness (f ‘ κ) (f ‘ γ) (f ‘ a) := by
  let := hγ.1.ordinal
  let := hierarchy_transitive (ordinalAdd lam ω)
  let := hierarchy_transitive (ordinalAdd lam' ω)
  let := hierarchy_transitive (succ γ)
  let := IsFunction.of_mem hf.function
  -- the source stage is a support stage
  have hωθ : (ω : V) ∈ ordinalAdd lam ω := subset_ordinalAdd lam (ω : V) _ hω
  have hsθ : ∀ ξ ∈ ordinalAdd lam ω, succ ξ ∈ ordinalAdd lam ω :=
    fun _ hξ ↦ ordinalAdd_omega_succ_closed lam hξ
  have hωθ' : (ω : V) ∈ ordinalAdd lam' ω := subset_ordinalAdd lam' (ω : V) _ hω'
  have hsθ' : ∀ ξ ∈ ordinalAdd lam' ω, succ ξ ∈ ordinalAdd lam' ω :=
    fun _ hξ ↦ ordinalAdd_omega_succ_closed lam' hξ
  have hlamθ : lam ∈ ordinalAdd lam ω := ordinalAdd_omega_gt lam
  have hsγlam : succ γ ∈ lam := hsucc γ hγlam
  have hγθ : γ ∈ ordinalAdd lam ω :=
    IsOrdinal.toIsTransitive.mem_trans hγlam hlamθ
  have hsγθ : succ γ ∈ ordinalAdd lam ω :=
    IsOrdinal.toIsTransitive.mem_trans hsγlam hlamθ
  have hγV : γ ∈ hierarchy (ordinalAdd lam ω) :=
    ordinal_subset_hierarchy (ordinalAdd lam ω) γ hγθ
  have hsγV : succ γ ∈ hierarchy (ordinalAdd lam ω) :=
    ordinal_subset_hierarchy (ordinalAdd lam ω) (succ γ) hsγθ
  have haθ : a ∈ hierarchy (ordinalAdd lam ω) :=
    (hierarchy_transitive (ordinalAdd lam ω)).mem_trans ha (hierarchy_mem hγθ)
  have hAV : hierarchy (succ γ) ∈ hierarchy (ordinalAdd lam ω) := hierarchy_mem hsγθ
  have hκA : κ ∈ hierarchy (succ γ) :=
    ordinal_subset_hierarchy (succ γ) κ (mem_succ_iff.mpr (Or.inr hκγ))
  have haA : a ∈ hierarchy (succ γ) :=
    hierarchy_mono (fun z hz ↦ mem_succ_iff.mpr (Or.inr hz)) _ ha
  have hκθ : κ ∈ hierarchy (ordinalAdd lam ω) := hκ.mem_domain
  -- restrict the embedding to `V_{γ+1}`
  have hne : IsNonempty (succ γ) := isNonempty_def.mpr ⟨γ, mem_succ_self γ⟩
  have hr := supportEmbedding_restrict_hierarchy hωθ hsθ hωθ' hsθ' hf hω hsucc hlamθ hFlam
    (show IsOrdinal (succ γ) from inferInstance) hne hsγlam
  rw [hf.value_succ hγV hsγV] at hr
  -- restrict the critical point
  have hcr := hκ.restrict hf.function
    ((hierarchy_transitive (ordinalAdd lam ω)).transitive _ hAV) hκA
  refine ⟨hf.value_ordinal hγ.1.ordinal hγV, γ, hγfκ, hγ, a, ha,
    f ↾ (hierarchy (succ γ)), hr, κ, hcr, ?_, ?_⟩
  · exact value_restrict (by rw [domain_eq_of_mem_function hf.function]; exact hκθ) hκA
  · exact value_restrict (by rw [domain_eq_of_mem_function hf.function]; exact haθ) haA

/-- The packaged form: every `Sigma-one-star` correct `γ` between the critical point and `lam`
that stays below the critical value transfers to a Woodin supercompactness witness. -/
theorem woodinSupercompactWitness_value_of_supportEmbedding_all {lam lam' f κ : V}
    [IsOrdinal lam] [IsOrdinal lam']
    (hω : (ω : V) ∈ lam) (hsucc : ∀ ξ ∈ lam, succ ξ ∈ lam)
    (hω' : (ω : V) ∈ lam') (hsucc' : ∀ ξ ∈ lam', succ ξ ∈ lam')
    (hFlam : (formulaFamily membershipLanguageCode ∅ : V) ∈ hierarchy lam)
    (hf : IsCodedMembershipEmbedding (hierarchy (ordinalAdd lam ω))
      (hierarchy (ordinalAdd lam' ω)) f)
    (hκ : IsCriticalPoint (hierarchy (ordinalAdd lam ω)) f κ) :
    ∀ γ : V, IsSigmaOneStarCorrect γ → κ ∈ γ → γ ∈ lam → γ ∈ f ‘ κ →
      ∀ a ∈ hierarchy γ, WoodinSupercompactWitness (f ‘ κ) (f ‘ γ) (f ‘ a) :=
  fun _ hγ hκγ hγlam hγfκ _ ha ↦ woodinSupercompactWitness_value_of_supportEmbedding
    hω hsucc hω' hsucc' hFlam hf hκ hγ hκγ hγlam hγfκ ha

end ZFVP
