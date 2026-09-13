import ZFVP.SetTheory.SparseFunctionUnion
import ZFVP.SetTheory.ForcingInverseLimit
import ZFVP.SetTheory.ForcingIsomorphism

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def sparseRestrictionThreads (θ b P U : V) : V :=
  {t ∈ U ^ θ; (∀ i ∈ θ, IsSparseFunctionOn (b ‘ i) (t ‘ i) ∧ t ‘ i ∈ P ‘ i) ∧
    ∀ i ∈ θ, ∀ j ∈ θ, (t ‘ i) ↾ (b ‘ j) = (t ‘ j) ↾ (b ‘ i)}

instance sparseRestrictionThreads_definable : ℒₛₑₜ-function₄[V] sparseRestrictionThreads := by
  have h : ℒₛₑₜ-relation₅[V] (fun C θ b P U ↦ ∀ t, t ∈ C ↔ t ∈ U ^ θ ∧
      (∀ i ∈ θ, IsSparseFunctionOn (b ‘ i) (t ‘ i) ∧ t ‘ i ∈ P ‘ i) ∧
      ∀ i ∈ θ, ∀ j ∈ θ, (t ‘ i) ↾ (b ‘ j) = (t ‘ j) ↾ (b ‘ i)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = sparseRestrictionThreads (v 1) (v 2) (v 3) (v 4) ↔ _
  rw [mem_ext_iff]
  simp only [sparseRestrictionThreads, mem_sep_iff]

theorem mem_sparseRestrictionThreads_iff {θ b P U t : V} :
    t ∈ sparseRestrictionThreads θ b P U ↔ t ∈ U ^ θ ∧
      (∀ i ∈ θ, IsSparseFunctionOn (b ‘ i) (t ‘ i) ∧ t ‘ i ∈ P ‘ i) ∧
      ∀ i ∈ θ, ∀ j ∈ θ, (t ‘ i) ↾ (b ‘ j) = (t ‘ j) ↾ (b ‘ i) := mem_sep_iff

theorem sparseRestrictionThread_range {θ b P U t q : V}
    (ht : t ∈ sparseRestrictionThreads θ b P U) (hq : q ∈ range t) :
    ∃ i ∈ θ, t ‘ i = q := by
  have hf := (mem_sparseRestrictionThreads_iff.mp ht).1
  let := IsFunction.of_mem hf
  obtain ⟨i, hi⟩ := mem_range_iff.mp hq
  exact ⟨i, domain_eq_of_mem_function hf ▸ mem_domain_of_kpair_mem hi,
    value_eq_of_kpair_mem hi⟩

theorem sparseRestrictionThread_compatible {θ b P U t : V}
    (ht : t ∈ sparseRestrictionThreads θ b P U) : CompatibleFunctionFamily (range t) := by
  have hh := mem_sparseRestrictionThreads_iff.mp ht
  intro p hp q hq x y z hxy hxz
  obtain ⟨i, hi, rfl⟩ := sparseRestrictionThread_range ht hp
  obtain ⟨j, hj, rfl⟩ := sparseRestrictionThread_range ht hq
  let := (hh.2.1 j hj).1.1
  have hres := kpair_mem_restrict_iff.mpr
    ⟨hxy, (hh.2.1 j hj).1.2.1 x (mem_domain_of_kpair_mem hxz)⟩
  rw [hh.2.2 i hi j hj] at hres
  exact IsFunction.unique (kpair_mem_restrict_iff.mp hres).1 hxz

theorem sparseRestrictionThread_union_sparse {θ A b P U t : V}
    (ht : t ∈ sparseRestrictionThreads θ b P U) (hb : ∀ i ∈ θ, b ‘ i ⊆ A) :
    IsSparseFunctionOn A (⋃ˢ range t) := by
  apply isSparseFunctionOn_sUnion ?_ (sparseRestrictionThread_compatible ht)
  intro p hp
  obtain ⟨i, hi, rfl⟩ := sparseRestrictionThread_range ht hp
  have hs := ((mem_sparseRestrictionThreads_iff.mp ht).2.1 i hi).1
  exact ⟨hs.1, subset_trans hs.2.1 (hb i hi), hs.2.2⟩

theorem sparseRestrictionThread_union_restrict {θ b P U t i : V}
    (ht : t ∈ sparseRestrictionThreads θ b P U) (hi : i ∈ θ) :
    (⋃ˢ range t) ↾ (b ‘ i) = t ‘ i := by
  have hh := mem_sparseRestrictionThreads_iff.mp ht
  have hF : ∀ p ∈ range t, IsFunction p := by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := sparseRestrictionThread_range ht hp
    exact (hh.2.1 j hj).1.1
  apply function_sUnion_restrict_of_coverage hF (sparseRestrictionThread_compatible ht)
    (value_mem_range hh.1 hi) (hh.2.1 i hi).1.2.1
  intro x hx
  obtain ⟨hxu, hxi⟩ := mem_inter_iff.mp hx
  obtain ⟨p, hp, hxp⟩ := (mem_domain_sUnion_iff (range t) x).mp hxu
  obtain ⟨j, hj, rfl⟩ := sparseRestrictionThread_range ht hp
  have hxr : x ∈ domain ((t ‘ j) ↾ (b ‘ i)) := by
    rw [domain_restrict_eq]
    exact mem_inter_iff.mpr ⟨hxp, hxi⟩
  rw [hh.2.2 j hj i hi, domain_restrict_eq] at hxr
  exact (mem_inter_iff.mp hxr).1

noncomputable def sparseThreadCarrier (θ A b P U : V) : V :=
  {q ∈ ℘ (⋃ˢ U); IsSparseFunctionOn A q ∧ ∀ i ∈ θ, q ↾ (b ‘ i) ∈ P ‘ i}

theorem sparseThreadCarrier_subset (θ A b P U : V) : sparseThreadCarrier θ A b P U ⊆ ℘ (⋃ˢ U) := sep_subset

theorem sparseThreadCarrier_isSparse {θ A b P U q : V} (hq : q ∈ sparseThreadCarrier θ A b P U) :
    IsSparseFunctionOn A q := (mem_sep_iff.mp hq).2.1

instance sparseThreadCarrier_definable : Language.DefinableFunction₅ ℒₛₑₜ (sparseThreadCarrier (V := V)) := by
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun C θ A b P U : V ↦ ∀ q, q ∈ C ↔
      q ⊆ ⋃ˢ U ∧ IsSparseFunctionOn A q ∧ ∀ i ∈ θ, q ↾ (b ‘ i) ∈ P ‘ i) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = sparseThreadCarrier (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  rw [mem_ext_iff]
  simp only [sparseThreadCarrier, mem_sep_iff, mem_power_iff]

theorem mem_sparseThreadCarrier_iff {θ A b P U q : V}
    (hU : ∀ i ∈ θ, P ‘ i ⊆ U) (hcover : ∀ x ∈ A, ∃ i ∈ θ, x ∈ b ‘ i) :
    q ∈ sparseThreadCarrier θ A b P U ↔
      IsSparseFunctionOn A q ∧ ∀ i ∈ θ, q ↾ (b ‘ i) ∈ P ‘ i := by
  constructor
  · intro hq
    exact (mem_sep_iff.mp hq).2
  · rintro ⟨hq, hrow⟩
    let := hq.1
    refine mem_sep_iff.mpr ⟨mem_power_iff.mpr ?_, hq, hrow⟩
    intro z hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    obtain ⟨i, hi, hxi⟩ := hcover x (hq.2.1 x (mem_domain_of_kpair_mem hz))
    exact mem_sUnion_iff.mpr ⟨q ↾ (b ‘ i), hU i hi _ (hrow i hi),
      kpair_mem_restrict_iff.mpr ⟨hz, hxi⟩⟩

theorem sparseRestrictionThread_union_mem {θ A b P U t : V}
    (ht : t ∈ sparseRestrictionThreads θ b P U) (hb : ∀ i ∈ θ, b ‘ i ⊆ A) :
    ⋃ˢ range t ∈ sparseThreadCarrier θ A b P U := by
  have hh := mem_sparseRestrictionThreads_iff.mp ht
  refine mem_sep_iff.mpr ⟨mem_power_iff.mpr ?_, sparseRestrictionThread_union_sparse ht hb, ?_⟩
  · intro z hz
    obtain ⟨p, hp, hz⟩ := mem_sUnion_iff.mp hz
    exact mem_sUnion_iff.mpr ⟨p, range_subset_of_mem_function hh.1 p hp, hz⟩
  · intro i hi
    rw [sparseRestrictionThread_union_restrict ht hi]
    exact (hh.2.1 i hi).2

noncomputable def sparseThreadDecodeValue (θ b q : V) : V :=
  definableGraph θ (fun i ↦ q ↾ (b ‘ i)) (by definability)

instance sparseThreadDecodeValue_definable : ℒₛₑₜ-function₃[V] sparseThreadDecodeValue := by
  have h : ℒₛₑₜ-relation₄[V] (fun t θ b q ↦ ∀ z, z ∈ t ↔
      ∃ i ∈ θ, z = ⟨i, q ↾ (b ‘ i)⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = sparseThreadDecodeValue (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [sparseThreadDecodeValue, mem_definableGraph_iff]

theorem sparseThreadDecodeValue_apply {θ b q i : V} (hi : i ∈ θ) :
    (sparseThreadDecodeValue θ b q) ‘ i = q ↾ (b ‘ i) := value_definableGraph _ _ _ hi

theorem sparseThreadDecodeValue_mem {θ A b P U q : V}
    (hq : q ∈ sparseThreadCarrier θ A b P U) (hU : ∀ i ∈ θ, P ‘ i ⊆ U) :
    sparseThreadDecodeValue θ b q ∈ sparseRestrictionThreads θ b P U := by
  have hh := (mem_sep_iff.mp hq).2
  apply mem_sparseRestrictionThreads_iff.mpr
  refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ (fun i hi ↦ hU i hi _ (hh.2 i hi)), ?_, ?_⟩
  · intro i hi
    rw [sparseThreadDecodeValue_apply hi]
    exact ⟨hh.1.restrict _, hh.2 i hi⟩
  · intro i hi j hj
    rw [sparseThreadDecodeValue_apply hi, sparseThreadDecodeValue_apply hj,
      restrict_restrict_eq_restrict_inter, restrict_restrict_eq_restrict_inter,
      inter_comm (b ‘ i) (b ‘ j)]

theorem sparseThreadDecodeValue_union {θ b P U t : V}
    (ht : t ∈ sparseRestrictionThreads θ b P U) :
    sparseThreadDecodeValue θ b (⋃ˢ range t) = t := by
  let := IsFunction.of_mem (mem_sparseRestrictionThreads_iff.mp ht).1
  unfold sparseThreadDecodeValue
  apply functions_eq_of_domain_values
  · rw [domain_definableGraph, domain_eq_of_mem_function (mem_sparseRestrictionThreads_iff.mp ht).1]
  · intro i hi
    rw [domain_definableGraph] at hi
    rw [value_definableGraph _ _ _ hi, sparseRestrictionThread_union_restrict ht hi]

theorem sparseThread_union_decodeValue {θ A b q : V}
    (hq : IsSparseFunctionOn A q) (hcover : ∀ x ∈ A, ∃ i ∈ θ, x ∈ b ‘ i) :
    ⋃ˢ range (sparseThreadDecodeValue θ b q) = q := by
  let := hq.1
  apply mem_ext
  intro z
  rw [sparseThreadDecodeValue, range_definableGraph]
  constructor
  · intro hz
    obtain ⟨p, hp, hzp⟩ := mem_sUnion_iff.mp hz
    obtain ⟨i, _, rfl⟩ := (repl_spec (show ℒₛₑₜ-function₁ (fun i ↦ q ↾ (b ‘ i)) by definability)).mp hp
    exact restrict_subset q (b ‘ i) z hzp
  · intro hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    obtain ⟨i, hi, hxi⟩ := hcover x (hq.2.1 x (mem_domain_of_kpair_mem hz))
    exact mem_sUnion_iff.mpr ⟨q ↾ (b ‘ i),
      (repl_spec (show ℒₛₑₜ-function₁ (fun i ↦ q ↾ (b ‘ i)) by definability)).mpr ⟨i, hi, rfl⟩,
      kpair_mem_restrict_iff.mpr ⟨hz, hxi⟩⟩

noncomputable def sparseThreadDecode (θ A b P U : V) : V :=
  definableGraph (sparseThreadCarrier θ A b P U) (sparseThreadDecodeValue θ b) (by definability)

noncomputable def sparseThreadEncode (θ b P U : V) : V :=
  definableGraph (sparseRestrictionThreads θ b P U) (fun t ↦ ⋃ˢ range t) (by definability)

instance sparseThreadDecode_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (sparseThreadDecode (V := V)) := by
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun f θ A b P U : V ↦ ∀ z, z ∈ f ↔
      ∃ q ∈ sparseThreadCarrier θ A b P U, z = ⟨q, sparseThreadDecodeValue θ b q⟩ₖ) := by
    simp only [sparseThreadCarrier, mem_sep_iff, mem_power_iff]
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = sparseThreadDecode (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  rw [mem_ext_iff]
  simp only [sparseThreadDecode, mem_definableGraph_iff]

instance sparseThreadEncode_definable : ℒₛₑₜ-function₄[V] sparseThreadEncode := by
  have h : ℒₛₑₜ-relation₅[V] (fun f θ b P U ↦ ∀ z, z ∈ f ↔
      ∃ t ∈ sparseRestrictionThreads θ b P U, z = ⟨t, ⋃ˢ range t⟩ₖ) := by
    simp only [sparseRestrictionThreads, mem_sep_iff]
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = sparseThreadEncode (v 1) (v 2) (v 3) (v 4) ↔ _
  rw [mem_ext_iff]
  simp only [sparseThreadEncode, mem_definableGraph_iff]

theorem sparseThreadDecode_value {θ A b P U q : V} (hq : q ∈ sparseThreadCarrier θ A b P U) :
    (sparseThreadDecode θ A b P U) ‘ q = sparseThreadDecodeValue θ b q := value_definableGraph _ _ _ hq

theorem sparseThreadEncode_value {θ b P U t : V} (ht : t ∈ sparseRestrictionThreads θ b P U) :
    (sparseThreadEncode θ b P U) ‘ t = ⋃ˢ range t := value_definableGraph _ _ _ ht

theorem sparseThreadEncode_decode {θ A b P U q : V}
    (hq : q ∈ sparseThreadCarrier θ A b P U) (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hcover : ∀ x ∈ A, ∃ i ∈ θ, x ∈ b ‘ i) :
    (sparseThreadEncode θ b P U) ‘ ((sparseThreadDecode θ A b P U) ‘ q) = q := by
  rw [sparseThreadDecode_value hq, sparseThreadEncode_value (sparseThreadDecodeValue_mem hq hU)]
  exact sparseThread_union_decodeValue (mem_sep_iff.mp hq).2.1 hcover

theorem sparseThreadDecode_encode {θ A b P U t : V}
    (ht : t ∈ sparseRestrictionThreads θ b P U) (hb : ∀ i ∈ θ, b ‘ i ⊆ A) :
    (sparseThreadDecode θ A b P U) ‘ ((sparseThreadEncode θ b P U) ‘ t) = t := by
  rw [sparseThreadEncode_value ht, sparseThreadDecode_value (sparseRestrictionThread_union_mem ht hb)]
  exact sparseThreadDecodeValue_union ht

noncomputable def sparseThreadOrder (θ b R C : V) : V :=
  {z ∈ C ×ˢ C; ∀ i ∈ θ, ⟨(kpair.π₁ z) ↾ (b ‘ i), (kpair.π₂ z) ↾ (b ‘ i)⟩ₖ ∈ R ‘ i}

instance sparseThreadOrder_definable : ℒₛₑₜ-function₄[V] sparseThreadOrder := by
  have h : ℒₛₑₜ-relation₅[V] (fun S θ b R C ↦ ∀ z, z ∈ S ↔ z ∈ C ×ˢ C ∧
      ∀ i ∈ θ, ⟨(kpair.π₁ z) ↾ (b ‘ i), (kpair.π₂ z) ↾ (b ‘ i)⟩ₖ ∈ R ‘ i) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = sparseThreadOrder (v 1) (v 2) (v 3) (v 4) ↔ _
  rw [mem_ext_iff]
  simp only [sparseThreadOrder, mem_sep_iff]

theorem mem_sparseThreadOrder_iff {θ b R C q r : V} :
    ⟨q, r⟩ₖ ∈ sparseThreadOrder θ b R C ↔ q ∈ C ∧ r ∈ C ∧
      ∀ i ∈ θ, ⟨q ↾ (b ‘ i), r ↾ (b ‘ i)⟩ₖ ∈ R ‘ i := by
  simp only [sparseThreadOrder, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  tauto

theorem sparseThreadDecode_isomorphism {θ A b P U R : V}
    (hU : ∀ i ∈ θ, P ‘ i ⊆ U) (hb : ∀ i ∈ θ, b ‘ i ⊆ A)
    (hcover : ∀ x ∈ A, ∃ i ∈ θ, x ∈ b ‘ i) :
    IsForcingIsomorphism (sparseThreadCarrier θ A b P U)
      (sparseThreadOrder θ b R (sparseThreadCarrier θ A b P U))
      (sparseRestrictionThreads θ b P U) (forcingThreadOrder θ R (sparseRestrictionThreads θ b P U))
      (sparseThreadDecode θ A b P U) := by
  have hf : sparseThreadDecode θ A b P U ∈
      (sparseRestrictionThreads θ b P U) ^ sparseThreadCarrier θ A b P U :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun q hq ↦ sparseThreadDecodeValue_mem hq hU)
  refine ⟨hf, ?_, ?_, ?_⟩
  · intro q r z hqz hrz
    obtain ⟨hq, hzq⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hqz
    obtain ⟨hr, hzr⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hrz
    have he := congrArg (fun t : V ↦ ⋃ˢ range t) (hzq.symm.trans hzr)
    simpa only [sparseThread_union_decodeValue (mem_sep_iff.mp hq).2.1 hcover,
      sparseThread_union_decodeValue (mem_sep_iff.mp hr).2.1 hcover] using he
  · apply SetTheory.subset_antisymm (range_subset_of_mem_function hf)
    intro t ht
    have hq := sparseRestrictionThread_union_mem ht hb
    have he : (sparseThreadDecode θ A b P U) ‘ (⋃ˢ range t) = t := by
      rw [sparseThreadDecode_value hq, sparseThreadDecodeValue_union ht]
    exact he ▸ value_mem_range hf hq
  · intro q hq r hr
    rw [sparseThreadDecode_value hq, sparseThreadDecode_value hr]
    simp only [mem_sparseThreadOrder_iff, mem_forcingThreadOrder_iff, hq, hr,
      sparseThreadDecodeValue_mem hq hU, sparseThreadDecodeValue_mem hr hU, true_and]
    constructor <;> intro h i hi <;> simpa only [sparseThreadDecodeValue_apply hi] using h i hi

theorem sparseThreadEncode_isomorphism {θ A b P U R : V}
    (hU : ∀ i ∈ θ, P ‘ i ⊆ U) (hb : ∀ i ∈ θ, b ‘ i ⊆ A)
    (hcover : ∀ x ∈ A, ∃ i ∈ θ, x ∈ b ‘ i) :
    IsForcingIsomorphism (sparseRestrictionThreads θ b P U)
      (forcingThreadOrder θ R (sparseRestrictionThreads θ b P U))
      (sparseThreadCarrier θ A b P U) (sparseThreadOrder θ b R (sparseThreadCarrier θ A b P U))
      (sparseThreadEncode θ b P U) := by
  have hf : sparseThreadEncode θ b P U ∈
      (sparseThreadCarrier θ A b P U) ^ sparseRestrictionThreads θ b P U :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun t ht ↦ sparseRestrictionThread_union_mem ht hb)
  refine ⟨hf, ?_, ?_, ?_⟩
  · intro t s z htz hsz
    obtain ⟨ht, hzt⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp htz
    obtain ⟨hs, hzs⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hsz
    have he := congrArg (sparseThreadDecodeValue θ b) (hzt.symm.trans hzs)
    simpa only [sparseThreadDecodeValue_union ht, sparseThreadDecodeValue_union hs] using he
  · apply SetTheory.subset_antisymm (range_subset_of_mem_function hf)
    intro q hq
    have ht := sparseThreadDecodeValue_mem hq hU
    have he : (sparseThreadEncode θ b P U) ‘ (sparseThreadDecodeValue θ b q) = q := by
      rw [sparseThreadEncode_value ht]
      exact sparseThread_union_decodeValue (mem_sep_iff.mp hq).2.1 hcover
    exact he ▸ value_mem_range hf ht
  · intro t ht s hs
    rw [sparseThreadEncode_value ht, sparseThreadEncode_value hs]
    simp only [mem_forcingThreadOrder_iff, mem_sparseThreadOrder_iff, ht, hs,
      sparseRestrictionThread_union_mem ht hb, sparseRestrictionThread_union_mem hs hb, true_and]
    constructor <;> intro h i hi <;>
      simpa only [sparseRestrictionThread_union_restrict ht hi, sparseRestrictionThread_union_restrict hs hi] using h i hi

end ZFVP
