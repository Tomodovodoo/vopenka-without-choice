import ZFVP.ModelTheory.EmbeddingStructureAction
import ZFVP.ModelTheory.CriticalPoint

/-! Full internal elementarity in arbitrary coded languages below the critical point. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankEmbedding_generic_restrict {k : ℕ} {δ ε f κ L M : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (k + 1) ε)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) (hk : coreSyntaxDictionaryBound ≤ k + 1)
    (hLκ : L ∈ hierarchy κ) (hsyntax : syntaxUniverse L ∅ ⊆ hierarchy κ)
    (hM : IsStructureCode L M) (hMδ : M ∈ hierarchy δ) :
    IsCodedElementaryEmbedding L M (f ‘ M) (f ↾ (structureDomain M)) := by
  let := hδ.ordinal
  let := hε.ordinal
  let := hκ.ordinal
  let := hierarchy_transitive δ
  let := hierarchy_transitive ε
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff k δ).mp hδ).2.support
  have hVκ := hδ.hierarchy_closed hκ.ordinal hκ.mem_domain
  have hinc : hierarchy κ ⊆ hierarchy δ := (hierarchy_transitive δ).transitive _ hVκ
  have hfix := rankEmbedding_fixed_below_criticalPoint hδ hε h hκ
  have hLδ := hinc L hLκ
  have hLfix := hfix L hLκ
  have htarget : IsStructureCode L (f ‘ M) := by
    have ht := (rankEmbedding_structureCode_iff hδ hε h hk hLδ hMδ).mp hM
    simpa only [hLfix] using ht
  have hD := hM.domain_mem_transitive hMδ
  have hsub : structureDomain M ⊆ hierarchy δ := (hierarchy_transitive δ).transitive _ hD
  have hfun : f ↾ (structureDomain M) ∈ structureDomain (f ‘ M) ^ structureDomain M := by
    rw [← h.value_structureDomain hM hMδ]
    exact h.restriction_function hD
  refine ⟨hM, htarget, hfun, ?_⟩
  intro n hn φ hφ b hb
  have hφU : φ ∈ syntaxUniverse L ∅ := (kpair_components_mem_transitive
    (formulaFamily_subset_syntaxUniverse L ∅ _ ((mem_formulaSet_iff _ _ _ _).mp hφ))).2
  have hφκ := hsyntax φ hφU
  have hφδ := hinc φ hφκ
  have hbδ := function_mem_sequenceSupport hsub hn hb
  have h0 : (∅ : V) ∈ hierarchy δ := IsCodingSupport.empty_mem
  have hnδ : n ∈ hierarchy δ := IsCodingSupport.natural_mem hn
  have he := rankEmbedding_coreDictionary_iff hδ hε h hk
    (show ⟨7, satisfiesFormula⟩ ∈ coreSyntaxDictionary by simp [coreSyntaxDictionary])
    (fun v ↦ Satisfies (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    ![L, ∅, M, ∅, n, φ, b]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hLδ, h0, hMδ, hnδ, hφδ, hbδ])
  change Satisfies L ∅ M ∅ n φ b ↔
    Satisfies (f ‘ L) (f ‘ ∅) (f ‘ M) (f ‘ ∅) (f ‘ n) (f ‘ φ) (f ‘ b) at he
  rw [hLfix, h.value_empty h0, h.value_natural hn, hfix φ hφκ,
    h.value_assignment hn hbδ (mem_function_of_mem_function_of_subset hb hsub),
    ← graph_compose_restrict hb f] at he
  exact he

end ZFVP
