import ZFVP.ModelTheory.EmbeddingSetOperations
import ZFVP.ModelTheory.LimitCriticalPoint

/-! The internal ultrafilter derived from a critical point of a rank embedding. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def derivedUltrafilter (κ f : V) : V := {X ∈ ℘ κ ; κ ∈ f ‘ X}

instance derivedUltrafilter_definable : ℒₛₑₜ-function₂[V] derivedUltrafilter := by
  have hd : ℒₛₑₜ-relation₃[V] (fun U κ f ↦ ∀ X, X ∈ U ↔ X ⊆ κ ∧ κ ∈ f ‘ X) := by
    definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = derivedUltrafilter (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp [derivedUltrafilter]

@[simp] theorem mem_derivedUltrafilter_iff (X κ f : V) :
    X ∈ derivedUltrafilter κ f ↔ X ⊆ κ ∧ κ ∈ f ‘ X := by simp [derivedUltrafilter]

theorem limitRankEmbedding_criticalPoint_initial {δ B f κ : V}
    [IsOrdinal δ] [IsTransitive B] (hδ : ∀ β ∈ δ, succ β ∈ δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) B f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) : IsInitialOrdinal κ := by
  let := hκ.ordinal
  let := hierarchy_transitive δ
  refine ⟨hκ.ordinal, ?_⟩
  intro α hα hinj
  obtain ⟨g, hg, hr⟩ := surjection_of_injection hinj ⟨α, hα⟩
  have hαδ := (hierarchy_transitive δ).mem_trans hα hκ.mem_domain
  have hgδ := (hierarchy_transitive δ).mem_trans hg
    (function_mem_hierarchy_limit hδ hαδ hκ.mem_domain)
  have hmap := h.value_surjection hgδ hαδ hκ.mem_domain hg hr
  rw [hκ.fixed_below hα] at hmap
  let := IsFunction.of_mem hmap.1
  have hκr : κ ∈ range (f ‘ g) := hmap.2.symm ▸ hκ.lt_value h
  obtain ⟨x, hxp⟩ := mem_range_iff.mp hκr
  have hxα := (mem_of_mem_functions hmap.1 hxp).1
  have hxκ := IsOrdinal.toIsTransitive.mem_trans hxα hα
  have hgxκ := function_value_mem hg hxα
  have hv := h.value_apply hgδ hαδ (IsFunction.of_mem hg) (domain_eq_of_mem_function hg) hxα
  rw [hκ.fixed_below hxκ, hκ.fixed_below hgxκ] at hv
  have he : κ = g ‘ x := (value_eq_of_kpair_mem hxp).symm.trans hv
  exact mem_irrefl κ (he.symm ▸ hgxκ)

theorem derivedUltrafilter_isUltrafilter {δ B f κ : V}
    [IsOrdinal δ] [IsTransitive B] (hδ : ∀ β ∈ δ, succ β ∈ δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) B f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) : IsSetUltrafilter κ (derivedUltrafilter κ f) := by
  classical
  let := hierarchy_transitive δ
  have hmem {X : V} (hs : X ⊆ κ) : X ∈ hierarchy δ :=
    subset_mem_hierarchy_limit hδ hκ.mem_domain hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X hX
    exact mem_power_iff.mpr ((mem_derivedUltrafilter_iff _ _ _).mp hX).1
  · exact (mem_derivedUltrafilter_iff _ _ _).mpr ⟨subset_refl κ, hκ.lt_value h⟩
  · intro h0
    have hm := ((mem_derivedUltrafilter_iff _ _ _).mp h0).2
    rw [h.value_empty (hmem (by simp))] at hm
    exact not_mem_empty hm
  · intro X hX Y hY hXY
    obtain ⟨hs, hm⟩ := (mem_derivedUltrafilter_iff _ _ _).mp hX
    exact (mem_derivedUltrafilter_iff _ _ _).mpr
      ⟨hY, h.value_subset (hmem hs) (hmem hY) hXY κ hm⟩
  · intro X hX Y hY
    obtain ⟨hsX, hmX⟩ := (mem_derivedUltrafilter_iff _ _ _).mp hX
    obtain ⟨hsY, hmY⟩ := (mem_derivedUltrafilter_iff _ _ _).mp hY
    have hs : X ∩ Y ⊆ κ := fun z hz ↦ hsX z (mem_inter_iff.mp hz).1
    refine (mem_derivedUltrafilter_iff _ _ _).mpr ⟨hs, ?_⟩
    rw [h.value_intersection (hmem hsX) (hmem hsY) (hmem hs)]
    exact mem_inter_iff.mpr ⟨hmX, hmY⟩
  · intro X hX
    by_cases hm : κ ∈ f ‘ X
    · exact Or.inl ((mem_derivedUltrafilter_iff _ _ _).mpr ⟨hX, hm⟩)
    · have hc : relativeComplement κ X ⊆ κ :=
        fun z hz ↦ (mem_relativeComplement_iff _ _ _ |>.mp hz).1
      refine Or.inr ((mem_derivedUltrafilter_iff _ _ _).mpr ⟨hc, ?_⟩)
      rw [h.value_relativeComplement hκ.mem_domain (hmem hX) (hmem hc)]
      exact (mem_relativeComplement_iff _ _ _).mpr ⟨hκ.lt_value h, hm⟩

theorem derivedUltrafilter_nonprincipal {δ B f κ : V}
    [IsOrdinal δ] [IsTransitive B] (hδ : ∀ β ∈ δ, succ β ∈ δ)
    (h : IsCodedMembershipEmbedding (hierarchy δ) B f)
    (hκ : IsCriticalPoint (hierarchy δ) f κ) :
    IsNonprincipalSetUltrafilter κ (derivedUltrafilter κ f) := by
  let := hierarchy_transitive δ
  refine ⟨derivedUltrafilter_isUltrafilter hδ h hκ, ?_⟩
  intro x hx hX
  have hxδ := (hierarchy_transitive δ).mem_trans hx hκ.mem_domain
  have hs : ({x} : V) ∈ hierarchy δ := by
    simpa using pair_mem_hierarchy_limit hδ hxδ hxδ
  have he : f ‘ ({x} : V) = ({x} : V) := by
    have hd : doubleton x x = ({x} : V) := by ext z; simp [← pair_eq_doubleton]
    simpa only [hκ.fixed_below hx, hd] using h.value_doubleton hxδ hxδ hs
  have hm := ((mem_derivedUltrafilter_iff _ _ _).mp hX).2
  rw [he] at hm
  have hxe : κ = x := by simpa using hm
  exact mem_irrefl κ (hxe.symm ▸ hx)

end ZFVP
