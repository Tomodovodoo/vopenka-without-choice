import ZFVP.ModelTheory.NameTwoStepOrderDefinability
import ZFVP.ModelTheory.NormalizedIsomorphismDefinability
import ZFVP.ModelTheory.SparsePairPresentation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def sparseNormalizedTwoStep (a A B top δ U : V) : V :=
  sparsePairCarrier a A (normalizedNamePool A B top δ U)

noncomputable def sparseNormalizedTwoStepOrder (a A B top δ U S : V) : V :=
  forcingPullbackOrder (sparseNormalizedTwoStep a A B top δ U)
    (nameTwoStepOrderOn A B S (normalizedNameTwoStep A B top δ U))
    (sparsePairDecode a A (normalizedNamePool A B top δ U))

noncomputable def sparseNormalizedTwoStepMap (a P R one δ U A B top f : V) : V :=
  compose (normalizedTwoStepIsoMap P R one δ U A B top f)
    (sparsePairEncode a A (normalizedNamePool A B top δ (nameAction f U)))

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₅.comp

instance sparseNormalizedTwoStep_uniform_definable :
    Language.DefinableFunction ℒₛₑₜ (fun v : Fin 6 → V ↦
      sparseNormalizedTwoStep (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) := by
  unfold sparseNormalizedTwoStep
  apply Language.DefinableFunction₃.comp
  · definability
  · definability
  · apply Language.DefinableFunction₅.comp <;> definability

theorem sparseNormalizedTwoStep_comp {n : ℕ} {a b c d e f : (Fin n → V) → V}
    (ha : Language.DefinableFunction ℒₛₑₜ a) (hb : Language.DefinableFunction ℒₛₑₜ b)
    (hc : Language.DefinableFunction ℒₛₑₜ c) (hd : Language.DefinableFunction ℒₛₑₜ d)
    (he : Language.DefinableFunction ℒₛₑₜ e) (hf : Language.DefinableFunction ℒₛₑₜ f) :
    Language.DefinableFunction ℒₛₑₜ (fun v ↦ sparseNormalizedTwoStep (a v) (b v) (c v) (d v) (e v) (f v)) :=
  Language.DefinableFunction.substitution (f := ![a, b, c, d, e, f])
    sparseNormalizedTwoStep_uniform_definable
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, ha, hb, hc, hd, he, hf])

instance sparseNormalizedTwoStepMap_uniform_definable :
    Language.DefinableFunction ℒₛₑₜ (fun v : Fin 10 → V ↦
      sparseNormalizedTwoStepMap (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)) := by
  unfold sparseNormalizedTwoStepMap
  apply Language.DefinableFunction₂.comp
  · apply normalizedTwoStepIsoMap_comp <;> definability
  · apply Language.DefinableFunction₃.comp
    · definability
    · definability
    · apply Language.DefinableFunction₅.comp <;> definability

instance forcingPullbackOrder_uniform_definable : ℒₛₑₜ-function₃[V] forcingPullbackOrder := by
  have h : ℒₛₑₜ-relation₄[V] (fun T Q R π ↦ ∀ z, z ∈ T ↔
      z ∈ Q ×ˢ Q ∧ ⟨π ‘ (kpair.π₁ z), π ‘ (kpair.π₂ z)⟩ₖ ∈ R) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingPullbackOrder (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingPullbackOrder, mem_sep_iff]

theorem forcingPullbackOrder_subset (Q R π : V) : forcingPullbackOrder Q R π ⊆ Q ×ˢ Q := sep_subset

instance sparseNormalizedTwoStepOrder_uniform_definable :
    Language.DefinableFunction ℒₛₑₜ (fun v : Fin 7 → V ↦
      sparseNormalizedTwoStepOrder (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) := by
  unfold sparseNormalizedTwoStepOrder
  apply Language.DefinableFunction₃.comp
  · apply sparseNormalizedTwoStep_comp <;> definability
  · apply Language.DefinableFunction₄.comp (hF := nameTwoStepOrderOnFormula_defined.to_definable)
    · definability
    · definability
    · definability
    · apply Language.DefinableFunction₅.comp <;> definability
  · apply Language.DefinableFunction₃.comp
    · definability
    · definability
    · apply Language.DefinableFunction₅.comp <;> definability

theorem mem_sparseNormalizedTwoStep_iff {a A B top δ U q : V} :
    q ∈ sparseNormalizedTwoStep a A B top δ U ↔
      IsSparseFunctionOn (succ a) q ∧ q ↾ a ∈ A ∧ q ‘ a ∈ normalizedNamePool A B top δ U :=
  mem_sparsePairCarrier_iff

theorem pair_mem_sparseNormalizedTwoStepOrder {a A B top δ U S p q : V} :
    ⟨p, q⟩ₖ ∈ sparseNormalizedTwoStepOrder a A B top δ U S ↔
      p ∈ sparseNormalizedTwoStep a A B top δ U ∧ q ∈ sparseNormalizedTwoStep a A B top δ U ∧
      ⟨p ↾ a, q ↾ a⟩ₖ ∈ B ∧
      p ↾ a ∈ forcingFormula A B boundedPairMemberFormula (standardTuple ![S, p ‘ a, q ‘ a]) := by
  rw [sparseNormalizedTwoStepOrder, mem_forcingPullbackOrder_iff]
  constructor
  · rintro ⟨hp, hq, hpq⟩
    rw [sparsePairDecode_value hp, sparsePairDecode_value hq, pair_mem_nameTwoStepOrderOn] at hpq
    exact ⟨hp, hq, hpq.2.2⟩
  · rintro ⟨hp, hq, hpq⟩
    refine ⟨hp, hq, ?_⟩
    rw [sparsePairDecode_value hp, sparsePairDecode_value hq, pair_mem_nameTwoStepOrderOn]
    exact ⟨kpair_mem_iff.mpr (mem_sparseNormalizedTwoStep_iff.mp hp).2,
      kpair_mem_iff.mpr (mem_sparseNormalizedTwoStep_iff.mp hq).2, hpq⟩

theorem sparseNormalizedTwoStep_subset_hierarchy {a A B top δ U : V} [IsOrdinal δ]
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (ha : a ∈ hierarchy δ) (hA : A ⊆ hierarchy δ) :
    sparseNormalizedTwoStep a A B top δ U ⊆ hierarchy δ :=
  sparsePairCarrier_subset_hierarchy hδ ha hA sep_subset

theorem sparseNormalizedTwoStepMap_isomorphism {a P R A B one top δ U S f : V}
    (hf : IsForcingIsomorphism P R A B f) (hR : IsForcingPreorder P R) (hB : IsForcingPreorder A B)
    (ho : one ∈ P) (ht : IsForcingTop A B top) (hft : f ‘ one = top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hA : A ∈ hierarchy δ)
    (hU : IsForcingName P U) (hS : IsForcingName P S)
    (hsp : ∀ p ∈ A, IsSparseFunctionOn a p) :
    IsForcingIsomorphism (normalizedNameTwoStep P R one δ U)
      (nameTwoStepOrderOn P R S (normalizedNameTwoStep P R one δ U))
      (sparseNormalizedTwoStep a A B top δ (nameAction f U))
      (sparseNormalizedTwoStepOrder a A B top δ (nameAction f U) (nameAction f S))
      (sparseNormalizedTwoStepMap a P R one δ U A B top f) :=
  (normalizedTwoStepIsoMap_isomorphism hf hR hB ho ht hft hδ hP hA hU hS).comp
    (sparsePairEncode_isomorphism hsp)

theorem sparseNormalizedTwoStepMap_value {a P R A B one top δ U f z : V}
    (hf : IsForcingIsomorphism P R A B f) (hR : IsForcingPreorder P R) (hB : IsForcingPreorder A B)
    (ho : one ∈ P) (ht : IsForcingTop A B top) (hft : f ‘ one = top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hA : A ∈ hierarchy δ)
    (hU : IsForcingName P U) (hsp : ∀ p ∈ A, IsSparseFunctionOn a p)
    (hz : z ∈ normalizedNameTwoStep P R one δ U) :
    (sparseNormalizedTwoStepMap a P R one δ U A B top f) ‘ z =
      sparseAppend a (f ‘ (kpair.π₁ z)) (normalizedIsomorphismName A B top f (kpair.π₂ z)) := by
  have hi := normalizedTwoStepIsoMap_isomorphism hf hR hB ho ht hft hδ hP hA hU hU
  have he := sparsePairEncode_isomorphism (W := normalizedNamePool A B top δ (nameAction f U))
    (R := nameTwoStepOrderOn A B (nameAction f U) (normalizedNameTwoStep A B top δ (nameAction f U))) hsp
  have hm := normalizedTwoStepIsoValue_mem hf hB ht.1 hft hδ hP hA hU hz
  change ⟨_, _⟩ₖ ∈ A ×ˢ normalizedNamePool A B top δ (nameAction f U) at hm
  rw [sparseNormalizedTwoStepMap, value_compose_of_mem_function hi.1 he.1 hz,
    normalizedTwoStepIsoMap_value hz]
  exact sparsePairEncode_value hsp (kpair_mem_iff.mp hm).1 (kpair_mem_iff.mp hm).2

theorem sparseNormalizedTwoStepMap_restrict {a P R A B one top δ U f z : V}
    (hf : IsForcingIsomorphism P R A B f) (hR : IsForcingPreorder P R) (hB : IsForcingPreorder A B)
    (ho : one ∈ P) (ht : IsForcingTop A B top) (hft : f ‘ one = top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hA : A ∈ hierarchy δ)
    (hU : IsForcingName P U) (hsp : ∀ p ∈ A, IsSparseFunctionOn a p)
    (hz : z ∈ normalizedNameTwoStep P R one δ U) :
    ((sparseNormalizedTwoStepMap a P R one δ U A B top f) ‘ z) ↾ a = f ‘ (kpair.π₁ z) := by
  obtain ⟨p, hp, τ, hτ, rfl⟩ := mem_prod_iff.mp hz
  have hs := hsp _ (function_value_mem hf.1 hp)
  let := hs.1
  rw [sparseNormalizedTwoStepMap_value hf hR hB ho ht hft hδ hP hA hU hsp (kpair_mem_iff.mpr ⟨hp, hτ⟩)]
  simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using sparseAppend_restrict (τ := normalizedIsomorphismName A B top f τ) hs.2.1

theorem sparseNormalizedTwoStepMap_tail {a P R A B one top δ U f z : V}
    (hf : IsForcingIsomorphism P R A B f) (hR : IsForcingPreorder P R) (hB : IsForcingPreorder A B)
    (ho : one ∈ P) (ht : IsForcingTop A B top) (hft : f ‘ one = top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hA : A ∈ hierarchy δ)
    (hU : IsForcingName P U) (hsp : ∀ p ∈ A, IsSparseFunctionOn a p)
    (hz : z ∈ normalizedNameTwoStep P R one δ U) :
    ((sparseNormalizedTwoStepMap a P R one δ U A B top f) ‘ z) ‘ a =
      normalizedIsomorphismName A B top f (kpair.π₂ z) := by
  obtain ⟨p, hp, τ, hτ, rfl⟩ := mem_prod_iff.mp hz
  have hs := hsp _ (function_value_mem hf.1 hp)
  let := hs.1
  rw [sparseNormalizedTwoStepMap_value hf hR hB ho ht hft hδ hP hA hU hsp (kpair_mem_iff.mpr ⟨hp, hτ⟩)]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  exact sparseAppend_value_new hs.2.1

theorem sparseNormalizedTwoStepMap_empty_tail {a P R A B one top δ U f p : V}
    (hf : IsForcingIsomorphism P R A B f) (hR : IsForcingPreorder P R) (hB : IsForcingPreorder A B)
    (ho : one ∈ P) (ht : IsForcingTop A B top) (hft : f ‘ one = top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hA : A ∈ hierarchy δ)
    (hU : IsForcingName P U) (hsp : ∀ p ∈ A, IsSparseFunctionOn a p)
    (hz : ⟨p, ∅⟩ₖ ∈ normalizedNameTwoStep P R one δ U) :
    (sparseNormalizedTwoStepMap a P R one δ U A B top f) ‘ ⟨p, ∅⟩ₖ = f ‘ p := by
  rw [sparseNormalizedTwoStepMap_value hf hR hB ho ht hft hδ hP hA hU hsp hz]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair, normalizedIsomorphismName_empty hB ht.1, sparseAppend_empty]

end ZFVP
