import ZFVP.SetTheory.ChoicelessSupercompactWitnessInRank
import ZFVP.ModelTheory.CriticalPointRestriction

/-! The first interval of the last-point supercompactness argument. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankEmbedding_supercompactWitness_below_image {n : ℕ} {θ η f κ α γ μ a : V}
    (hθ : Cn (n + 2) θ) (hη : Cn (n + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f)
    (hc : IsCriticalPoint (hierarchy θ) f κ) (hακ : α ∈ κ)
    [IsOrdinal γ] (hκγ : κ ⊆ γ) (hγμ : γ ∈ μ)
    (hμimage : μ ∈ f ‘ γ) (hμθ : μ ∈ θ) (hμ : Cn (n + 2) μ) (ha : a ∈ hierarchy μ) :
    ChoicelessSupercompactWitness (n + 2) α γ μ a := by
  let := hθ.ordinal
  let := hη.ordinal
  let := hμ.ordinal
  let := hc.ordinal
  let := hierarchy_transitive θ
  let := hierarchy_transitive η
  let := hierarchy_transitive μ
  let := IsFunction.of_mem hf.function
  have hγθ := IsOrdinal.toIsTransitive.mem_trans hγμ hμθ
  have hμV := ordinal_subset_hierarchy θ μ hμθ
  have hγV := ordinal_subset_hierarchy θ γ hγθ
  have hAV := hierarchy_mem hμθ
  have haV := (hierarchy_transitive θ).mem_trans ha hAV
  have hαV := (hierarchy_transitive θ).mem_trans hακ hc.mem_domain
  have hκμ : κ ∈ μ := ordinal_mem_of_subset_mem hκγ hγμ
  have hκA := ordinal_subset_hierarchy μ κ hκμ
  have hr := rankEmbedding_restrict hθ hη hf hAV ⟨ω, ordinal_subset_hierarchy μ _ hμ.omega_lt⟩
  rw [(rankEmbedding_value_hierarchy hθ hη hf hμ.ordinal hμV).2] at hr
  have hcr := hc.restrict hf.function ((hierarchy_transitive θ).transitive _ hAV) hκA
  have hw : ChoicelessSupercompactWitness (n + 2) (f ‘ α) (f ‘ γ) (f ‘ μ) (f ‘ a) := by
    refine ⟨hf.value_ordinal hμ.ordinal hμV, μ, a, f ↾ (hierarchy μ), κ,
      hμimage, hμ, ha, hr, hcr, ?_, ?_⟩
    · rwa [hc.fixed_below hακ]
    · exact value_restrict (by rw [domain_eq_of_mem_function hf.function]; exact haV) ha
  let aa : SetDomain (hierarchy θ) := ⟨α, hαV⟩
  let gg : SetDomain (hierarchy θ) := ⟨γ, hγV⟩
  let mm : SetDomain (hierarchy θ) := ⟨μ, hμV⟩
  let xx : SetDomain (hierarchy θ) := ⟨a, haV⟩
  have ht := hη.supercompactWitness_into_rank
    (hf.toFunction aa) (hf.toFunction gg) (hf.toFunction mm) (hf.toFunction xx) hw
  have hv : hf.toFunction ∘ ![aa, gg, mm, xx] =
      ![hf.toFunction aa, hf.toFunction gg, hf.toFunction mm, hf.toFunction xx] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) l) k) j) i
  rw [← hv] at ht
  have hs := (hf.eval_semisentence (choicelessSupercompactWitnessFormula (n + 2))
    ![aa, gg, mm, xx]).mpr ht
  exact ((hθ.of_le (by omega : n + 1 ≤ n + 2)).choicelessSupercompactWitness_absolute
    aa gg mm xx hμ hγμ).mp hs

end ZFVP
