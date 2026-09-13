import ZFVP.ModelTheory.LastPoint
import ZFVP.ModelTheory.EmbeddingCofinality
import ZFVP.SetTheory.ClubSets

/-! The last point has no cofinal graph on a set below the critical point. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankEmbedding_lastPoint_no_cofinalMap {k l : ℕ} {θ η f κ A g : V}
    (hθ : Cn (k + 1) θ) (hη : Cn (l + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f)
    (hc : IsCriticalPoint (hierarchy θ) f κ) (hγθ : lastPoint θ f ∈ θ)
    (hA : A ∈ hierarchy κ) : ¬IsCofinalMap (lastPoint θ f) A g := by
  let := hθ.ordinal
  let := hη.ordinal
  let := hc.ordinal
  let := hierarchy_transitive θ
  let := hierarchy_transitive η
  let := hierarchy_transitive κ
  let γ := lastPoint θ f
  let := lastPoint_ordinal θ f
  let C := fixedOrdinals θ f
  have hC : IsUnboundedIn C γ := by
    constructor
    · intro ξ hξ
      obtain ⟨hξθ, hfix⟩ := mem_fixedOrdinals.mp hξ
      exact rankEmbedding_fixed_mem_lastPoint hθ hη hf hξθ hfix
    · intro ξ hξ
      obtain ⟨ζ, hζ, hξζ, hfix⟩ := rankEmbedding_fixed_cofinal_lastPoint hθ hη hf hξ
      exact ⟨ζ, mem_fixedOrdinals.mpr ⟨lastPoint_subset θ f _ hζ, hfix⟩, hξζ⟩
  intro hg
  let F := fun x : V ↦ nextIn C (g ‘ x)
  have hF : ℒₛₑₜ-function₁[V] F := by unfold F; definability
  let G := definableGraph A F hF
  have hFspec : ∀ x ∈ A, F x ∈ γ ∧ g ‘ x ∈ F x ∧ f ‘ (F x) = F x := by
    intro x hx
    obtain ⟨hnext, hlt⟩ := nextIn_spec hC (function_value_mem hg.1 hx)
    exact ⟨hC.1 _ hnext, hlt, (mem_fixedOrdinals.mp hnext).2⟩
  have hG : G ∈ γ ^ A := definableGraph_mem_function_of_mapsTo A γ F hF
    (fun x hx ↦ (hFspec x hx).1)
  have hGcof : IsCofinalMap γ A G := by
    refine ⟨hG, ?_⟩
    intro ξ hξ
    obtain ⟨x, hx, hle⟩ := hg.2 ξ hξ
    refine ⟨x, hx, ?_⟩
    rw [value_definableGraph A F hF hx]
    have hn := (hFspec x hx).1
    let : IsOrdinal (F x) := IsOrdinal.of_mem hn
    exact subset_trans hle (IsOrdinal.toIsTransitive.transitive _ (hFspec x hx).2.1)
  have hAV := (hierarchy_transitive θ).mem_trans hA (hθ.hierarchy_closed hc.ordinal hc.mem_domain)
  have hγV := ordinal_subset_hierarchy θ γ hγθ
  have hGV := (hierarchy_transitive θ).mem_trans hG
    (function_mem_hierarchy_limit hθ.successor_closed hAV hγV)
  have hmap := hf.value_cofinalMap hGV hAV hγV hGcof
  have hfixA := rankEmbedding_fixed_below_criticalPoint hθ hη hf hc A hA
  rw [hfixA] at hmap
  have hγmove := rankEmbedding_lastPoint_lt_image hθ hη hf hγθ
  obtain ⟨x, hx, hle⟩ := hmap.2 γ hγmove
  have hxκ := (hierarchy_transitive κ).mem_trans hx hA
  have hfixx := rankEmbedding_fixed_below_criticalPoint hθ hη hf hc x hxκ
  have hv := hf.value_apply hGV hAV (IsFunction.of_mem hG) (domain_eq_of_mem_function hG) hx
  have hfixG : f ‘ (G ‘ x) = G ‘ x := by
    rw [value_definableGraph A F hF hx]
    exact (hFspec x hx).2.2
  rw [hfixx, hfixG] at hv
  rw [hv] at hle
  exact mem_irrefl (G ‘ x) (hle _ (function_value_mem hG hx))

end ZFVP
