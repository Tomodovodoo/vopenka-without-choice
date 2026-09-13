import ZFVP.ModelTheory.SchmerlNamedUpperEntries
import ZFVP.ModelTheory.SchmerlCodedDirectedPosetFamily
import ZFVP.ModelTheory.InternalJointSourceNaming
import ZFVP.SetTheory.FiniteCardinalArithmetic

/-! The actual Rubin cofinal background and the finite set of old-point
demands extracted from a finite fragment. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

noncomputable def namedUpperDemands (M : V) : V :=
  {p ∈ codedDirectedPosetIndex M ×ˢ structureDomain M ;
    kpair.π₂ p ∈ (codedDirectedPosetDomains M) ‘ (kpair.π₁ p)}

instance namedUpperDemands_definable : ℒₛₑₜ-function₁[V] namedUpperDemands := by
  have h : ℒₛₑₜ-relation[V] (fun A M ↦ ∀ p, p ∈ A ↔
      p ∈ codedDirectedPosetIndex M ×ˢ structureDomain M ∧
      kpair.π₂ p ∈ (codedDirectedPosetDomains M) ‘ (kpair.π₁ p)) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [namedUpperDemands, mem_sep_iff]
  rfl

theorem namedUpperDemands_subset (M : V) : namedUpperDemands M ⊆ codedDirectedPosetIndex M ×ˢ structureDomain M :=
  fun _ hp ↦ (mem_sep_iff.mp hp).1

theorem pair_mem_namedUpperDemands (M i x : V) :
    ⟨i, x⟩ₖ ∈ namedUpperDemands M ↔ i ∈ codedDirectedPosetIndex M ∧ x ∈ (codedDirectedPosetDomains M) ‘ i := by
  simp only [namedUpperDemands, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  constructor
  · rintro ⟨⟨hi, _⟩, hx⟩
    exact ⟨hi, hx⟩
  · rintro ⟨hi, hx⟩
    exact ⟨⟨hi, mem_power_iff.mp (function_value_mem (codedDirectedPosetDomains_mem M) hi) x hx⟩, hx⟩

noncomputable def namedUpperBackground (M j k : V) : V :=
  namedElementaryDiagram membershipLanguageCode M j ∪
    (repl (namedUpperMember j k) (by definability) (codedDirectedPosetIndex M) ∪
      repl (fun p ↦ namedUpperOrder j k (kpair.π₁ p) (kpair.π₂ p)) (by definability) (namedUpperDemands M))

theorem mem_namedUpperBackground (M j k p : V) : p ∈ namedUpperBackground M j k ↔
    p ∈ namedElementaryDiagram membershipLanguageCode M j ∨
      (∃ i ∈ codedDirectedPosetIndex M, p = namedUpperMember j k i) ∨
      ∃ i ∈ codedDirectedPosetIndex M, ∃ x ∈ (codedDirectedPosetDomains M) ‘ i, p = namedUpperOrder j k i x := by
  simp only [namedUpperBackground, mem_union_iff, repl_spec]
  apply or_congr Iff.rfl
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨i, hi, x, _, rfl⟩ := mem_prod_iff.mp (namedUpperDemands_subset M q hq)
    have hx := ((pair_mem_namedUpperDemands M i x).mp hq).2
    exact ⟨i, hi, x, hx, by simp⟩
  · rintro ⟨i, hi, x, hx, rfl⟩
    exact ⟨⟨i, x⟩ₖ, (pair_mem_namedUpperDemands M i x).mpr ⟨hi, hx⟩, by simp⟩

instance namedUpperBackground_definable : ℒₛₑₜ-function₃[V] namedUpperBackground := by
  have h : ℒₛₑₜ-relation₄[V] (fun B M j k ↦ ∀ p, p ∈ B ↔
      p ∈ namedElementaryDiagram membershipLanguageCode M j ∨
      (∃ i ∈ codedDirectedPosetIndex M, p = namedUpperMember j k i) ∨
      ∃ i ∈ codedDirectedPosetIndex M, ∃ x ∈ (codedDirectedPosetDomains M) ‘ i, p = namedUpperOrder j k i x) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_namedUpperBackground]
  rfl

theorem namedUpperBackground_diagram (M j k : V) :
    namedElementaryDiagram membershipLanguageCode M j ⊆ namedUpperBackground M j k :=
  fun p hp ↦ (mem_namedUpperBackground M j k p).mpr (Or.inl hp)

theorem namedUpperMember_mem {M j k i : V} (hi : i ∈ codedDirectedPosetIndex M) :
    namedUpperMember j k i ∈ namedUpperBackground M j k :=
  (mem_namedUpperBackground M j k _).mpr (Or.inr (Or.inl ⟨i, hi, rfl⟩))

theorem namedUpperOrder_mem {M j k i x : V} (hi : i ∈ codedDirectedPosetIndex M)
    (hx : x ∈ (codedDirectedPosetDomains M) ‘ i) : namedUpperOrder j k i x ∈ namedUpperBackground M j k :=
  (mem_namedUpperBackground M j k _).mpr (Or.inr (Or.inr ⟨i, hi, x, hx, rfl⟩))

theorem namedUpperBackground_valid {M j k A : V}
    (hj : j ∈ A ^ structureDomain M) (hk : k ∈ A ^ codedDirectedPosetIndex M) :
    namedUpperBackground M j k ⊆ namedFormulaSet membershipLanguageCode A := by
  intro p hp
  rcases (mem_namedUpperBackground M j k p).mp hp with hp | ⟨i, hi, rfl⟩ | ⟨i, hi, x, hx, rfl⟩
  · obtain ⟨n, _, φ, hφ, b, hb, rfl, _⟩ := namedElementaryDiagram_cases membershipLanguageCode_valid hp
    exact (pair_mem_namedFormulaSet_iff membershipLanguageCode_valid).mpr ⟨hφ, compose_function hb hj⟩
  · exact namedUpperMember_valid (codedDirectedPosetIndex_spec hi).1 hj hk hi
  · exact namedUpperOrder_valid (codedDirectedPosetIndex_spec hi).2.1 hj hk hi
      (mem_power_iff.mp (function_value_mem (codedDirectedPosetDomains_mem M) hi) x hx)

theorem namedUpperBackground_support {M j k : V}
    (hj : j ∈ (ω : V) ^ structureDomain M) (hk : k ∈ (ω : V) ^ codedDirectedPosetIndex M) :
    namedTheorySupport (namedUpperBackground M j k) ⊆ range j ∪ range k := by
  let : IsFunction j := IsFunction.of_mem hj
  let : IsFunction k := IsFunction.of_mem hk
  have hj' : j ∈ (range j ∪ range k) ^ structureDomain M := by
    simpa only [domain_eq_of_mem_function hj] using
      mem_function_of_mem_function_of_subset (IsFunction.mem_function j)
        (fun x hx ↦ mem_union_iff.mpr (Or.inl hx))
  have hk' : k ∈ (range j ∪ range k) ^ codedDirectedPosetIndex M := by
    simpa only [domain_eq_of_mem_function hk] using
      mem_function_of_mem_function_of_subset (IsFunction.mem_function k)
        (fun x hx ↦ mem_union_iff.mpr (Or.inr hx))
  exact namedTheorySupport_subset membershipLanguageCode_valid (namedUpperBackground_valid hj' hk')

noncomputable def namedUpperFragmentDemands (M j k S : V) : V :=
  {p ∈ namedUpperDemands M ; namedUpperOrder j k (kpair.π₁ p) (kpair.π₂ p) ∈ S}

instance namedUpperFragmentDemands_definable : ℒₛₑₜ-function₄[V] namedUpperFragmentDemands := by
  have h : ℒₛₑₜ-relation₅[V] (fun A M j k S ↦ ∀ p, p ∈ A ↔ p ∈ namedUpperDemands M ∧
      namedUpperOrder j k (kpair.π₁ p) (kpair.π₂ p) ∈ S) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [namedUpperFragmentDemands, mem_sep_iff]
  rfl

theorem pair_mem_namedUpperFragmentDemands (M j k S i x : V) :
    ⟨i, x⟩ₖ ∈ namedUpperFragmentDemands M j k S ↔
      (i ∈ codedDirectedPosetIndex M ∧ x ∈ (codedDirectedPosetDomains M) ‘ i) ∧ namedUpperOrder j k i x ∈ S := by
  simp only [namedUpperFragmentDemands, mem_sep_iff, pair_mem_namedUpperDemands, kpair.π₁_kpair, kpair.π₂_kpair]

theorem namedUpperFragmentDemands_subset (M j k S : V) :
    namedUpperFragmentDemands M j k S ⊆ codedDirectedPosetIndex M ×ˢ structureDomain M :=
  fun p hp ↦ namedUpperDemands_subset M p (mem_sep_iff.mp hp).1

theorem namedUpperFragmentDemands_finite {M j k S : V}
    (hj : j ∈ (ω : V) ^ structureDomain M) (hji : Injective j)
    (hk : k ∈ (ω : V) ^ codedDirectedPosetIndex M) (hki : Injective k) (hS : IsInternallyFinite S) :
    IsInternallyFinite (namedUpperFragmentDemands M j k S) := by
  apply internallyFinite_of_cardLE hS
  apply cardLE_of_injective_map (fun p ↦ namedUpperOrder j k (kpair.π₁ p) (kpair.π₂ p)) (by definability)
  · exact fun _ hp ↦ (mem_sep_iff.mp hp).2
  · intro p hp q hq he
    obtain ⟨i, hi, x, hx, rfl⟩ := mem_prod_iff.mp (namedUpperFragmentDemands_subset M j k S p hp)
    obtain ⟨l, hl, y, hy, rfl⟩ := mem_prod_iff.mp (namedUpperFragmentDemands_subset M j k S q hq)
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at he
    obtain ⟨hil, hxy⟩ := namedUpperOrder_injective (fun _ h ↦ (codedDirectedPosetIndex_spec h).2.1)
      hj hji hk hki hi hl hx hy he
    rw [hil, hxy]

end ZFVP.Schmerl
