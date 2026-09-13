import ZFVP.ModelTheory.SchmerlNamedUpperRealization
import ZFVP.ModelTheory.InternalJointNamedConjunction

/-! Finite upper-bound requirements can be imposed together with a finite
named condition. A full upper-name assignment can retain prescribed values. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

noncomputable def namedUpperRelevantIndices (M k n : V) : V :=
  {i ∈ codedDirectedPosetIndex M ; k ‘ i ∈ n}

instance namedUpperRelevantIndices_definable : ℒₛₑₜ-function₃[V] namedUpperRelevantIndices := by
  have h : ℒₛₑₜ-relation₄[V] (fun J M k n ↦ ∀ i, i ∈ J ↔ i ∈ codedDirectedPosetIndex M ∧ k ‘ i ∈ n) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [namedUpperRelevantIndices, mem_sep_iff]
  rfl

theorem namedUpperRelevantIndices_finite {M k n : V}
    (hk : k ∈ (ω : V) ^ codedDirectedPosetIndex M) (hki : Injective k) (hn : IsInternallyFinite n) :
    IsInternallyFinite (namedUpperRelevantIndices M k n) := by
  apply internallyFinite_of_cardLE hn
  apply cardLE_of_injective_map (fun i ↦ k ‘ i) (by definability)
  · exact fun _ hi ↦ (mem_sep_iff.mp hi).2
  · intro i hi l hl he
    exact injective_value_eq hk hki (mem_sep_iff.mp hi).1 (mem_sep_iff.mp hl).1 he

theorem exists_upperAssignment_agree (hAC : InternalChoice V) {M k f J : V}
    (hJ : J ⊆ codedDirectedPosetIndex M)
    (hfix : ∀ i ∈ J, f ‘ (k ‘ i) ∈ (codedDirectedPosetDomains M) ‘ i) :
    ∃ c ∈ structureDomain M ^ codedDirectedPosetIndex M,
      (∀ i ∈ codedDirectedPosetIndex M, c ‘ i ∈ (codedDirectedPosetDomains M) ‘ i) ∧
      ∀ i ∈ J, c ‘ i = f ‘ (k ‘ i) := by
  classical
  let F : V → V := fun i ↦ {z ∈ (codedDirectedPosetDomains M) ‘ i ; i ∈ J → z = f ‘ (k ‘ i)}
  have hF : ℒₛₑₜ-function₁ F := by
    have h : ℒₛₑₜ-relation[V] (fun Z i ↦ ∀ z, z ∈ Z ↔ z ∈ (codedDirectedPosetDomains M) ‘ i ∧
        (i ∈ J → z = f ‘ (k ‘ i))) := by definability
    apply Language.Definable.of_iff h
    intro v
    rw [mem_ext_iff]
    simp only [F, mem_sep_iff]
    rfl
  have hne : ∀ i ∈ codedDirectedPosetIndex M, IsNonempty (F i) := by
    intro i hi
    by_cases hiJ : i ∈ J
    · exact ⟨_, mem_sep_iff.mpr ⟨hfix i hiJ, fun _ ↦ rfl⟩⟩
    · obtain ⟨z, hz⟩ := (codedDirectedPosetFamily_directed hi).1
      exact ⟨z, mem_sep_iff.mpr ⟨hz, fun h ↦ False.elim (hiJ h)⟩⟩
  obtain ⟨c, hc, hdom, hchoice⟩ := choice_for_definable_family hAC (codedDirectedPosetIndex M) F hF hne
  let : IsFunction c := hc
  have hvalues : ∀ i ∈ codedDirectedPosetIndex M,
      c ‘ i ∈ (codedDirectedPosetDomains M) ‘ i ∧ (i ∈ J → c ‘ i = f ‘ (k ‘ i)) :=
    fun i hi ↦ mem_sep_iff.mp (hchoice i hi)
  have hrange : range c ⊆ structureDomain M := by
    intro z hz
    obtain ⟨i, hiz⟩ := mem_range_iff.mp hz
    have hi : i ∈ codedDirectedPosetIndex M := hdom ▸ mem_domain_of_kpair_mem hiz
    have hm := (hvalues i hi).1
    rw [value_eq_of_kpair_mem hiz] at hm
    exact mem_power_iff.mp (function_value_mem (codedDirectedPosetDomains_mem M) hi) z hm
  exact ⟨c, by simpa only [hdom] using
    mem_function_of_mem_function_of_subset (IsFunction.mem_function c) hrange,
    fun i hi ↦ (hvalues i hi).1, fun i hi ↦ (hvalues i (hJ i hi)).2 hi⟩

theorem upper_fragment_realization {M j k A J H : V}
    (hj : j ∈ (ω : V) ^ structureDomain M) (hk : k ∈ (ω : V) ^ codedDirectedPosetIndex M)
    (h : FinitelySourceRealized membershipLanguageCode M j (namedUpperBackground M j k ∪ A))
    (hA : IsInternallyFinite A) (hJ : IsInternallyFinite J) (hJI : J ⊆ codedDirectedPosetIndex M)
    (hH : IsInternallyFinite H) (hHD : H ⊆ namedUpperDemands M) :
    ∃ f, ZFVP.SourceNaming M j f ∧ (∀ p ∈ A, NamedHolds membershipLanguageCode M f p) ∧
      (∀ i ∈ J, f ‘ (k ‘ i) ∈ (codedDirectedPosetDomains M) ‘ i) ∧
      ∀ i x, ⟨i, x⟩ₖ ∈ H → ⟨x, f ‘ (k ‘ i)⟩ₖ ∈ (codedDirectedPosetRelations M) ‘ i := by
  let JM := repl (namedUpperMember j k) (by definability) J
  let HO := repl (fun p ↦ namedUpperOrder j k (kpair.π₁ p) (kpair.π₂ p)) (by definability) H
  have hfin : IsInternallyFinite (A ∪ (JM ∪ HO)) :=
    internallyFinite_union hA (internallyFinite_union (internallyFinite_repl _ _ hJ) (internallyFinite_repl _ _ hH))
  have hsub : A ∪ (JM ∪ HO) ⊆ namedUpperBackground M j k ∪ A := by
    intro p hp
    rcases mem_union_iff.mp hp with hpA | hp
    · exact mem_union_iff.mpr (Or.inr hpA)
    · apply mem_union_iff.mpr ∘ Or.inl
      rcases mem_union_iff.mp hp with hp | hp
      · obtain ⟨i, hi, rfl⟩ := (repl_spec _).mp hp
        exact namedUpperMember_mem (hJI i hi)
      · obtain ⟨r, hr, rfl⟩ := (repl_spec _).mp hp
        obtain ⟨i, hi, x, _, rfl⟩ := mem_prod_iff.mp (namedUpperDemands_subset M r (hHD r hr))
        have hx := ((pair_mem_namedUpperDemands M i x).mp (hHD _ hr)).2
        simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using (namedUpperOrder_mem hi hx (j := j) (k := k))
  obtain ⟨f, hf, hs⟩ := h.2 _ hfin hsub
  refine ⟨f, hf, fun p hp ↦ hs p (mem_union_iff.mpr (Or.inl hp)), ?_, ?_⟩
  · intro i hi
    rw [codedDirectedPosetDomains_value (hJI i hi)]
    apply (SourceNaming.upperMember_iff hf (codedDirectedPosetIndex_spec (hJI i hi)).1 hj hk (hJI i hi)).mp
    exact hs _ (mem_union_iff.mpr (Or.inr (mem_union_iff.mpr (Or.inl ((repl_spec _).mpr ⟨i, hi, rfl⟩)))))
  · intro i x hix
    obtain ⟨hi, hx⟩ := (pair_mem_namedUpperDemands M i x).mp (hHD _ hix)
    have hxD := mem_power_iff.mp (function_value_mem (codedDirectedPosetDomains_mem M) hi) x hx
    rw [codedDirectedPosetRelations_value hi]
    apply (SourceNaming.upperOrder_iff hf (codedDirectedPosetIndex_spec hi).2.1 hj hk hi hxD).mp
    exact hs _ (mem_union_iff.mpr (Or.inr (mem_union_iff.mpr (Or.inr
      ((repl_spec _).mpr ⟨⟨i, x⟩ₖ, hix, by simp⟩)))))

end ZFVP.Schmerl
