import ZFVP.SetTheory.LebesgueNull
import ZFVP.SetTheory.FiniteCardinalArithmetic
import ZFVP.SetTheory.BaireCore

/-! Level counting for the coded Lebesgue measure: the shadow of a family of finite sequences at a
level `M`, its behaviour under passing to higher levels, and subadditivity of `SmallMeasure`:
two families of measure at most `2^{-(m+1)}` have union of measure at most `2^{-m}`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Induction upward from a natural `M`. -/
theorem natural_induction_from {M : V} (hM : M ∈ (ω : V)) (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (hbase : P M) (hstep : ∀ M' ∈ (ω : V), M ⊆ M' → P M' → P (succ M')) :
    ∀ M' ∈ (ω : V), M ⊆ M' → P M' := by
  have : IsOrdinal M := IsOrdinal.nat hM
  apply naturalNumber_induction (fun M' ↦ M ⊆ M' → P M') (by have := hP; definability)
  · intro h
    have hM0 : M = ∅ := by
      apply mem_ext
      intro x
      simp only [not_mem_empty, iff_false]
      exact fun hx ↦ not_mem_empty (h x hx)
    have : P ∅ := hM0 ▸ hbase
    exact this
  · intro M' hM' ih h
    have : IsOrdinal M' := IsOrdinal.nat hM'
    have : IsOrdinal (succ M') := IsOrdinal.nat (ω_succ_closed hM')
    rcases (IsOrdinal.subset_iff (α := M) (β := succ M')).mp h with heq | hmem
    · rw [← heq]
      exact hbase
    · have hsub : M ⊆ M' := by
        rcases mem_succ_iff.mp hmem with rfl | hmem
        · exact fun x hx ↦ hx
        · exact IsOrdinal.toIsTransitive.transitive M hmem
      exact hstep M' hM' hsub (ih hsub)

theorem shadow_mono_family {F F' M : V} (h : F ⊆ F') : shadow F M ⊆ shadow F' M := by
  intro t ht
  obtain ⟨htM, s, hs, hst⟩ := (mem_shadow_iff _ _ _).mp ht
  exact (mem_shadow_iff _ _ _).mpr ⟨htM, s, h s hs, hst⟩

theorem shadow_union (F F' M : V) : shadow (F ∪ F') M = shadow F M ∪ shadow F' M := by
  apply mem_ext
  intro t
  rw [mem_union_iff, mem_shadow_iff, mem_shadow_iff, mem_shadow_iff]
  constructor
  · rintro ⟨htM, s, hs, hst⟩
    rcases mem_union_iff.mp hs with hs | hs
    · exact Or.inl ⟨htM, s, hs, hst⟩
    · exact Or.inr ⟨htM, s, hs, hst⟩
  · rintro (⟨htM, s, hs, hst⟩ | ⟨htM, s, hs, hst⟩)
    · exact ⟨htM, s, mem_union_iff.mpr (Or.inl hs), hst⟩
    · exact ⟨htM, s, mem_union_iff.mpr (Or.inr hs), hst⟩

theorem shadow_subset_power (F M : V) : shadow F M ⊆ ((2 : ℕ) : V) ^ M :=
  fun t ht ↦ ((mem_shadow_iff _ _ _).mp ht).1

theorem shadow_empty (M : V) : shadow (∅ : V) M = ∅ := by
  apply mem_ext
  intro t
  simp only [not_mem_empty, iff_false]
  intro ht
  obtain ⟨_, s, hs, _⟩ := (mem_shadow_iff _ _ _).mp ht
  exact not_mem_empty hs

theorem shadow_finite {F M : V} (hM : M ∈ (ω : V)) : IsInternallyFinite (shadow F M) :=
  internallyFinite_subset (internallyFinite_two_pow hM) (shadow_subset_power F M)

/-- Passing to the next level at most doubles the shadow. -/
theorem shadow_succ_cardLE {F M : V} (hdom : ∀ s ∈ F, domain s ⊆ M) :
    shadow F (succ M) ≤# shadow F M ×ˢ ((2 : ℕ) : V) := by
  refine cardLE_of_injective_map (fun t ↦ ⟨t ↾ M, t ‘ M⟩ₖ) (by definability) ?_ ?_
  · intro t ht
    obtain ⟨htM, s, hs, hst⟩ := (mem_shadow_iff _ _ _).mp ht
    have : IsFunction t := IsFunction.of_mem htM
    refine kpair_mem_iff.mpr ⟨(mem_shadow_iff _ _ _).mpr
      ⟨function_restrict_mem htM (fun x hx ↦ mem_succ_iff.mpr (Or.inr hx)), s, hs, ?_⟩,
      function_value_mem htM (mem_succ_self M)⟩
    intro p hp
    have hpt : p ∈ t := hst p hp
    obtain ⟨a, ha, b, -, rfl⟩ := mem_prod_iff.mp ((mem_function_iff.mp htM).1 p hpt)
    exact kpair_mem_restrict_iff.mpr ⟨hpt, hdom s hs a (mem_domain_of_kpair_mem hp)⟩
  · intro t ht t' ht' h
    obtain ⟨htM, -⟩ := (mem_shadow_iff _ _ _).mp ht
    obtain ⟨ht'M, -⟩ := (mem_shadow_iff _ _ _).mp ht'
    have : IsFunction t := IsFunction.of_mem htM
    have : IsFunction t' := IsFunction.of_mem ht'M
    obtain ⟨h1, h2⟩ := kpair_inj h
    apply functions_eq_of_domain_values ((domain_eq_of_mem_function htM).trans (domain_eq_of_mem_function ht'M).symm)
    intro x hx
    rw [domain_eq_of_mem_function htM] at hx
    rcases mem_succ_iff.mp hx with rfl | hx
    · exact h2
    · have := congrArg (fun f ↦ f ‘ x) h1
      rw [value_restrict (by rw [domain_eq_of_mem_function htM]; exact mem_succ_iff.mpr (Or.inr hx)) hx,
        value_restrict (by rw [domain_eq_of_mem_function ht'M]; exact mem_succ_iff.mpr (Or.inr hx)) hx] at this
      exact this

theorem function_power_cardLE_succ (n : V) : ((2 : ℕ) : V) ^ n ≤# ((2 : ℕ) : V) ^ succ n := by
  refine CardLE.trans ?_ (prod_two_cardLE_function_power_succ n)
  refine cardLE_of_injective_map (fun u ↦ ⟨u, ∅⟩ₖ) (by definability) ?_ ?_
  · intro u hu
    exact kpair_mem_iff.mpr ⟨hu, (mem_two_iff _).mpr (Or.inl rfl)⟩
  · intro u _ u' _ h
    exact (kpair_inj h).1

theorem function_power_cardLE_of_subset {m m' : V} (hm : m ∈ (ω : V)) (hm' : m' ∈ (ω : V)) (h : m ⊆ m') :
    ((2 : ℕ) : V) ^ m ≤# ((2 : ℕ) : V) ^ m' := by
  refine natural_induction_from hm (fun m' ↦ ((2 : ℕ) : V) ^ m ≤# ((2 : ℕ) : V) ^ m') (by definability)
    (CardLE.refl _) ?_ m' hm' h
  intro M' _ _ ih
  exact ih.trans (function_power_cardLE_succ M')

/-- Small measure at a level persists to all higher levels. -/
theorem smallMeasure_levels {F m : V} (h : SmallMeasure F m) :
    ∃ M ∈ (ω : V), (∀ s ∈ F, domain s ⊆ M) ∧
      ∀ M' ∈ (ω : V), M ⊆ M' → shadow F M' ×ˢ (((2 : ℕ) : V) ^ m) ≤# ((2 : ℕ) : V) ^ M' := by
  obtain ⟨M, hM, hdom, hsmall⟩ := h
  refine ⟨M, hM, hdom, ?_⟩
  refine natural_induction_from hM
    (fun M' ↦ shadow F M' ×ˢ (((2 : ℕ) : V) ^ m) ≤# ((2 : ℕ) : V) ^ M') (by definability) hsmall ?_
  intro M' _ hMM' ih
  have hdom' : ∀ s ∈ F, domain s ⊆ M' := fun s hs x hx ↦ hMM' x (hdom s hs x hx)
  have h1 : shadow F (succ M') ×ˢ (((2 : ℕ) : V) ^ m) ≤#
      (shadow F M' ×ˢ ((2 : ℕ) : V)) ×ˢ (((2 : ℕ) : V) ^ m) :=
    prod_cardLE_prod (shadow_succ_cardLE hdom') (CardLE.refl _)
  have h2 : (shadow F M' ×ˢ ((2 : ℕ) : V)) ×ˢ (((2 : ℕ) : V) ^ m) ≤#
      shadow F M' ×ˢ (((2 : ℕ) : V) ×ˢ (((2 : ℕ) : V) ^ m)) := prod_assoc_cardLE _ _ _
  have h3 : shadow F M' ×ˢ (((2 : ℕ) : V) ×ˢ (((2 : ℕ) : V) ^ m)) ≤#
      shadow F M' ×ˢ ((((2 : ℕ) : V) ^ m) ×ˢ ((2 : ℕ) : V)) :=
    prod_cardLE_prod (CardLE.refl _) (prod_comm_cardLE _ _)
  have h4 : shadow F M' ×ˢ ((((2 : ℕ) : V) ^ m) ×ˢ ((2 : ℕ) : V)) ≤#
      (shadow F M' ×ˢ (((2 : ℕ) : V) ^ m)) ×ˢ ((2 : ℕ) : V) := prod_assoc_cardLE' _ _ _
  have h5 : (shadow F M' ×ˢ (((2 : ℕ) : V) ^ m)) ×ˢ ((2 : ℕ) : V) ≤#
      (((2 : ℕ) : V) ^ M') ×ˢ ((2 : ℕ) : V) := prod_cardLE_prod ih (CardLE.refl _)
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (prod_two_cardLE_function_power_succ M')))))

theorem smallMeasure_mono_family {F F' m : V} (h : SmallMeasure F m) (hF' : F' ⊆ F) :
    SmallMeasure F' m := by
  obtain ⟨M, hM, hdom, hsmall⟩ := h
  exact ⟨M, hM, fun s hs ↦ hdom s (hF' s hs),
    (prod_cardLE_prod (cardLE_of_subset (shadow_mono_family hF')) (CardLE.refl _)).trans hsmall⟩

theorem smallMeasure_mono_precision {F m m' : V} (h : SmallMeasure F m) (hm : m ∈ (ω : V))
    (hm' : m' ∈ (ω : V)) (hmm' : m' ⊆ m) : SmallMeasure F m' := by
  obtain ⟨M, hM, hdom, hsmall⟩ := h
  exact ⟨M, hM, hdom,
    (prod_cardLE_prod (CardLE.refl _) (function_power_cardLE_of_subset hm' hm hmm')).trans hsmall⟩

theorem smallMeasure_empty (m : V) : SmallMeasure (∅ : V) m :=
  ⟨∅, zero_mem_ω, fun s hs ↦ (not_mem_empty hs).elim, by
    rw [shadow_empty]
    refine cardLE_of_subset (fun z hz ↦ ?_)
    obtain ⟨_, h, _, _, _⟩ := mem_prod_iff.mp hz
    exact (not_mem_empty h).elim⟩

/-- Subadditivity: two families of measure at most `2^{-(m+1)}` have union of measure at most
`2^{-m}`. -/
theorem smallMeasure_union {F F' m : V} (hm : m ∈ (ω : V))
    (h1 : SmallMeasure F (succ m)) (h2 : SmallMeasure F' (succ m)) : SmallMeasure (F ∪ F') m := by
  obtain ⟨M₁, hM₁, hdom₁, hlev₁⟩ := smallMeasure_levels h1
  obtain ⟨M₂, hM₂, hdom₂, hlev₂⟩ := smallMeasure_levels h2
  have : IsOrdinal M₁ := IsOrdinal.nat hM₁
  have : IsOrdinal M₂ := IsOrdinal.nat hM₂
  obtain ⟨M, hM, hM₁M, hM₂M⟩ : ∃ M ∈ (ω : V), M₁ ⊆ M ∧ M₂ ⊆ M := by
    rcases IsOrdinal.subset_or_supset (α := M₁) (β := M₂) with h | h
    · exact ⟨M₂, hM₂, h, fun x hx ↦ hx⟩
    · exact ⟨M₁, hM₁, fun x hx ↦ hx, h⟩
  refine ⟨M, hM, fun s hs ↦ ?_, ?_⟩
  · rcases mem_union_iff.mp hs with hs | hs
    · exact fun x hx ↦ hM₁M x (hdom₁ s hs x hx)
    · exact fun x hx ↦ hM₂M x (hdom₂ s hs x hx)
  · have hhalf : ∀ S : V, shadow S M ×ˢ (((2 : ℕ) : V) ^ succ m) ≤# ((2 : ℕ) : V) ^ M →
        (shadow S M ×ˢ (((2 : ℕ) : V) ^ m)) ×ˢ ((2 : ℕ) : V) ≤# ((2 : ℕ) : V) ^ M := by
      intro S hS
      have h1 : (shadow S M ×ˢ (((2 : ℕ) : V) ^ m)) ×ˢ ((2 : ℕ) : V) ≤#
          shadow S M ×ˢ ((((2 : ℕ) : V) ^ m) ×ˢ ((2 : ℕ) : V)) := prod_assoc_cardLE _ _ _
      have h2 : shadow S M ×ˢ ((((2 : ℕ) : V) ^ m) ×ˢ ((2 : ℕ) : V)) ≤#
          shadow S M ×ˢ (((2 : ℕ) : V) ^ succ m) :=
        prod_cardLE_prod (CardLE.refl _) (prod_two_cardLE_function_power_succ m)
      exact h1.trans (h2.trans hS)
    have hA : IsInternallyFinite (shadow F M ×ˢ (((2 : ℕ) : V) ^ m)) :=
      internallyFinite_prod (shadow_finite hM) (internallyFinite_two_pow hm)
    have hB : IsInternallyFinite (shadow F' M ×ˢ (((2 : ℕ) : V) ^ m)) :=
      internallyFinite_prod (shadow_finite hM) (internallyFinite_two_pow hm)
    have hu := union_cardLE_of_double hA hB (hhalf F (hlev₁ M hM hM₁M)) (hhalf F' (hlev₂ M hM hM₂M))
    refine CardLE.trans (cardLE_of_subset ?_) hu
    intro z hz
    obtain ⟨t, ht, u, hu', rfl⟩ := mem_prod_iff.mp hz
    rw [shadow_union] at ht
    rcases mem_union_iff.mp ht with ht | ht
    · exact mem_union_iff.mpr (Or.inl (kpair_mem_iff.mpr ⟨ht, hu'⟩))
    · exact mem_union_iff.mpr (Or.inr (kpair_mem_iff.mpr ⟨ht, hu'⟩))

end ZFVP
