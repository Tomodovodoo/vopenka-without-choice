import ZFVP.ModelTheory.LastPoint
import ZFVP.ModelTheory.EmbeddingNextCnFixed
import ZFVP.SetTheory.CnCofinal

/-! Correct rank heights occur cofinally below the last point and its
image when that image still lies in the source. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankEmbedding_lastPoint_cnCofinal {n : ℕ} {θ η f : V}
    (hθ : Cn (n + 2) θ) (hη : Cn (n + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f)
    (hlim : CnCofinal (n + 2) θ) : CnCofinal (n + 2) (lastPoint θ f) := by
  let := hθ.ordinal
  let := lastPoint_ordinal θ f
  intro β hβ
  obtain ⟨ξ, hξγ, hβξ, hfix⟩ := rankEmbedding_fixed_cofinal_lastPoint hθ hη hf hβ
  have hξθ := lastPoint_subset θ f _ hξγ
  obtain ⟨ζ, hζθ, hξζ, hζ⟩ := hlim ξ hξθ
  obtain ⟨δ, hδ, _⟩ := leastOrdinal_existsUnique (fun δ ↦ ξ ∈ δ ∧ Cn (n + 2) δ)
    (by definability) ⟨ζ, hζ.ordinal, hξζ, hζ⟩
  let := hδ.1
  let := hζ.ordinal
  have hδθ := ordinal_mem_of_subset_mem (hδ.2.2 ζ hζ.ordinal ⟨hξζ, hζ⟩) hζθ
  have hδfix := rankEmbedding_nextCn_fixed hθ hη hf hδ hδθ hfix
  have hδγ := rankEmbedding_fixed_mem_lastPoint hθ hη hf hδθ hδfix
  exact ⟨δ, hδγ, IsOrdinal.toIsTransitive.mem_trans hβξ hδ.2.1.1, hδ.2.1.2⟩

theorem rankEmbedding_lastPoint_nonempty {k l : ℕ} {θ η f : V}
    (hθ : Cn (k + 1) θ) (hη : Cn (l + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f) :
    IsNonempty (lastPoint θ f) := by
  let := hθ.ordinal
  let := hη.ordinal
  let := hierarchy_transitive θ
  let := hierarchy_transitive η
  have hω := hθ.omega_lt
  have hfix := hf.value_omega (ordinal_subset_hierarchy θ (ω : V) hω)
  exact ⟨ω, rankEmbedding_fixed_mem_lastPoint hθ hη hf hω hfix⟩

theorem rankEmbedding_lastPoint_cn {n : ℕ} {θ η f : V}
    (hθ : Cn (n + 2) θ) (hη : Cn (n + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f)
    (hlim : CnCofinal (n + 2) θ) : Cn (n + 2) (lastPoint θ f) := by
  let := hθ.ordinal
  let := lastPoint_ordinal θ f
  exact cn_closed _ (rankEmbedding_lastPoint_nonempty hθ hη hf)
    (rankEmbedding_lastPoint_cnCofinal hθ hη hf hlim)

theorem rankEmbedding_cnCofinal_image {n : ℕ} {θ η f γ : V}
    (hθ : Cn (n + 2) θ) (hη : Cn (n + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f)
    (hlim : CnCofinal (n + 2) θ) [IsOrdinal γ] (hγθ : γ ∈ θ)
    (hγ : CnCofinal (n + 2) γ) (himg : f ‘ γ ∈ θ) : CnCofinal (n + 2) (f ‘ γ) := by
  let := hθ.ordinal
  let := hη.ordinal
  have hγV := ordinal_subset_hierarchy θ γ hγθ
  have ht := rankEmbedding_cnCofinal_image_eval (hθ.of_le (by omega : n + 1 ≤ n + 2)) hf hγV hγ
  obtain ⟨β, hβθ, hγβ, hβ⟩ := hlim _ himg
  let := hβ.ordinal
  exact hη.cnCofinal_of_eval (hf.toFunction ⟨γ, hγV⟩) hβ
    (IsOrdinal.toIsTransitive.transitive _ hγβ)
    ((rankEmbedding_height_subset hθ hη hf) _ hβθ) ht

end ZFVP
