import ZFVP.ModelTheory.OmegaJonssonPiTwo
import ZFVP.ModelTheory.EmbeddingPointwiseImage
import ZFVP.ModelTheory.CriticalSequenceFixedPoint
import ZFVP.ModelTheory.FixedStageSelfRestriction
import ZFVP.SetTheory.CnSequenceNames

/-! Kunen's contradiction with the stage only assumed to be in `C(2)`.

`ZFVP.ModelTheory.KunenFromJonsson` runs the same argument, but it transfers the omega-Jonsson
predicate along the embedding through the crude syntactic bound `omegaJonssonBound`, so it needs a
stage in `C(43)`. Here the transfer is `IsOmegaJonsson.value_cn_two`, which uses the Pi-two form of
the predicate, and every other step of the argument already goes through at `C(2)`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Enlarging the codomain of an internal function. -/
private theorem mem_function_mono' {g X Y Y' : V} (hg : g ∈ Y ^ X) (hY : Y ⊆ Y') : g ∈ Y' ^ X := by
  refine mem_function_iff.mpr ⟨fun p hp ↦ ?_, (mem_function_iff.mp hg).2⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp ((mem_function_iff.mp hg).1 p hp)
  exact kpair_mem_iff.mpr ⟨hx, hY y hy⟩

/-- Kunen's contradiction at a `C(2)` rank stage: a coded self-embedding whose critical limit sits
inside the stage rules out an omega-Jonsson function for that limit inside the stage. -/
theorem false_of_omegaJonsson_criticalLimit_two {δ f κ F : V} (hδ : Cn 2 δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ)
    (hlim : criticalLimit f κ ∈ hierarchy δ)
    (hF : F ∈ hierarchy δ) (hJ : IsOmegaJonsson F (criticalLimit f κ)) : False := by
  let := hδ.ordinal
  let := hierarchy_transitive δ
  set lam : V := criticalLimit f κ with hlamdef
  have hω : (ω : V) ∈ hierarchy δ := ((cn_successor_iff 1 δ).mp hδ).2.support.omega_mem
  have hlamord : IsOrdinal lam := CriticalSequence.limit_ordinal hδ h hκ
  have hfix : f ‘ lam = lam := CriticalSequence.limit_fixed hδ h hκ hlim
  have hκlam : κ ∈ lam := by
    simpa using CriticalSequence.iterate_mem_limit hδ h hκ (by simp : (0 : V) ∈ ω)
  -- the pointwise image of the fixed limit
  set A : V := imageSet f lam with hAdef
  have hAsub : A ⊆ lam := h.imageSet_subset_of_value_eq hlim hfix
  have hAcard : lam ≤# A := h.cardLE_imageSet hlim
  -- the restriction of `f` to `lam` and its inverse
  have hr : f ↾ lam ∈ A ^ lam := h.restrict_mem_function hlim
  have hrinj : Injective (f ↾ lam) := h.restrict_injective
  have hrange : range (f ↾ lam) = A := rfl
  have hc : converseGraph (f ↾ lam) ∈ lam ^ A := by
    simpa only [hrange] using converseGraph_mem_function hr hrinj
  set c : V := converseGraph (f ↾ lam) with hcdef
  have hlamdom : lam ⊆ domain f := h.subset_domain hlim
  have hrval : ∀ ξ ∈ lam, (f ↾ lam) ‘ ξ = f ‘ ξ := by
    let := IsFunction.of_mem h.function
    exact fun ξ hξ ↦ value_restrict (hlamdom ξ hξ) hξ
  -- the image function is omega-Jonsson for the same limit
  have hJ' : IsOmegaJonsson (f ‘ F) lam := by
    have := hJ.value_cn_two hδ h hF hlim
    rwa [hfix] at this
  obtain ⟨u, hu, huA, ⟨e, he, hre⟩, hval⟩ := hJ'.2.2 A hAsub hAcard κ hκlam
  -- pull the enumeration of `u` back along the inverse of `f ↾ lam`
  let := IsFunction.of_mem he
  have heA : e ∈ A ^ (ω : V) := mem_function_mono' he huA
  have hgb : compose e c ∈ lam ^ (ω : V) := compose_function heA hc
  let := IsFunction.of_mem hgb
  set b : V := range (compose e c) with hbdef
  have hbfun : compose e c ∈ b ^ (ω : V) :=
    function_mem_of_isFunction' (domain_eq_of_mem_function hgb) rfl
  have hblam : b ⊆ lam := range_subset_of_mem_function hgb
  have hbδ : b ∈ hierarchy δ := subset_mem_hierarchy_limit hδ.successor_closed hlim hblam
  have hgbδ : compose e c ∈ hierarchy δ :=
    (hierarchy_transitive δ).mem_trans hbfun
      (function_mem_hierarchy_limit hδ.successor_closed hω hbδ)
  -- values of the pulled back enumeration
  have hgbval : ∀ n ∈ (ω : V), (compose e c) ‘ n = c ‘ (e ‘ n) :=
    fun n hn ↦ value_compose_of_mem_function heA hc hn
  -- `f` maps `b` onto `u` pointwise
  have himg : imageSet f b = u := by
    apply SetTheory.subset_antisymm
    · intro y hy
      obtain ⟨ξ, hξ, rfl⟩ := (h.mem_imageSet_value_iff hbδ y).mp hy
      obtain ⟨n, hn⟩ := mem_range_iff.mp hξ
      have hnω : n ∈ (ω : V) := by
        simpa [domain_eq_of_mem_function hgb] using mem_domain_of_kpair_mem hn
      have hξv : ξ = c ‘ (e ‘ n) := by
        have := (value_eq_of_kpair_mem hn).symm.trans (hgbval n hnω)
        exact this
      have hen : e ‘ n ∈ u := function_value_mem he hnω
      have hrec : (f ↾ lam) ‘ (c ‘ (e ‘ n)) = e ‘ n :=
        value_converseGraph_value hr hrinj (by rw [hrange]; exact huA _ hen)
      rw [hξv, ← hrval _ (function_value_mem hc (huA _ hen)), hrec]
      exact hen
    · intro y hy
      obtain ⟨n, hn⟩ := mem_range_iff.mp (hre.symm ▸ hy)
      have hnω : n ∈ (ω : V) := by
        simpa [domain_eq_of_mem_function he] using mem_domain_of_kpair_mem hn
      have hyv : e ‘ n = y := value_eq_of_kpair_mem hn
      have hcy : c ‘ y ∈ lam := function_value_mem hc (huA _ (hyv ▸ function_value_mem he hnω))
      refine (h.mem_imageSet_value_iff hbδ y).mpr ⟨c ‘ y, ?_, ?_⟩
      · rw [hbdef, ← hyv, ← hgbval n hnω]
        exact value_mem_range hgb (by simpa [domain_eq_of_mem_function hgb] using hnω)
      · rw [← hrval _ hcy]
        exact value_converseGraph_value hr hrinj
          (by rw [hrange, ← hyv]; exact huA _ (function_value_mem he hnω))
  have hvb : f ‘ b = u := by
    rw [h.value_eq_imageSet_of_omega_surjection hω hbδ hgbδ hbfun rfl]
    exact himg
  -- transfer membership in the domain back through `f`
  have hFfun : IsFunction F := hJ.1
  have hdomF : domain F ∈ hierarchy δ := Cn.domain_closed (hδ.of_le (by omega)) hF
  have hdomval := h.value_function_domain hF hdomF hFfun rfl
  have hbdom : b ∈ domain F := by
    have : f ‘ b ∈ f ‘ (domain F) := by rw [hvb]; rw [hdomval.2] at hu; exact hu
    exact (h.value_mem_iff hbδ hdomF).mp this
  -- the critical point lands in the pointwise image of the limit
  have happ : (f ‘ F) ‘ (f ‘ b) = f ‘ (F ‘ b) :=
    h.value_apply hF hdomF hFfun rfl hbdom
  have hκv : f ‘ (F ‘ b) = κ := by rw [← happ, hvb]; exact hval
  have hFb : F ‘ b ∈ lam := (hJ.2.1 b hbdom).2
  exact criticalPoint_not_mem_imageSet h hκ hlamord hlim
    ((h.mem_imageSet_value_iff hlim κ).mpr ⟨F ‘ b, hFb, hκv⟩)

/-- Packaged form at `C(2)`: no member of the stage is an omega-Jonsson function for the critical
limit. -/
theorem no_omegaJonsson_selfEmbedding_two {δ f κ : V} (hδ : Cn 2 δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) (hlim : criticalLimit f κ ∈ hierarchy δ)
    (hJ : ∃ F ∈ hierarchy δ, IsOmegaJonsson F (criticalLimit f κ)) : False := by
  obtain ⟨F, hF, hFJ⟩ := hJ
  exact false_of_omegaJonsson_criticalLimit_two hδ h hκ hlim hF hFJ

/-- An embedding between rank stages that fixes a `C(2)` ordinal `η` above its critical point,
with the critical limit below `η`, admits no omega-Jonsson function for that limit in
`hierarchy η`. -/
theorem false_of_fixed_stage_embedding_two {k l : ℕ} {δ ε f η κ : V}
    (hδ : Cn (k + 1) δ) (hε : Cn (l + 1) ε) (hηc : Cn 2 η)
    (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy ε) f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ)
    (hη : IsOrdinal η) (hηδ : η ∈ hierarchy δ) (hfix : f ‘ η = η) (hκη : κ ∈ η)
    (hlimη : criticalLimit f κ ∈ η)
    (hJ : ∃ F ∈ hierarchy η, IsOmegaJonsson F (criticalLimit f κ)) : False := by
  let := hη
  have hg : IsCodedMembershipEmbedding (hierarchy η) (hierarchy η) (f ↾ (hierarchy η)) :=
    selfRestriction_of_fixed_ordinal hδ hε h hκ hη hηδ hfix hκη
  have hκg : IsCriticalPoint (hierarchy η) (f ↾ (hierarchy η)) κ :=
    criticalPoint_selfRestriction hδ hε h hκ hη hηδ hfix hκη
  have heq : criticalLimit (f ↾ (hierarchy η)) κ = criticalLimit f κ :=
    criticalLimit_selfRestriction hδ hε h hκ hη hηδ hfix hκη
  let := CriticalSequence.limit_ordinal hηc hg hκg
  have hlim : criticalLimit (f ↾ (hierarchy η)) κ ∈ hierarchy η :=
    ordinal_mem_hierarchy_iff.mpr (by rw [heq]; exact hlimη)
  exact no_omegaJonsson_selfEmbedding_two hηc hg hκg hlim (by rw [heq]; exact hJ)

end ZFVP
