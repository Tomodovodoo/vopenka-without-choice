import ZFVP.ModelTheory.SchmerlCodedCofinalOrdinals
import ZFVP.ModelTheory.SchmerlInternalBranchNames

/-! Select the actual class-tree levels indexed by the Rubin ordinal chain.
The resulting rank graph takes values in the ambient ordinal κ. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsInternalCofinalStrictChain.value_injective {κ P S c i j : V} [IsOrdinal κ]
    (h : IsInternalCofinalStrictChain κ P S c) (hi : i ∈ κ) (hj : j ∈ κ) (he : c ‘ i = c ‘ j) : i = j := by
  let : IsOrdinal i := IsOrdinal.of_mem hi
  let : IsOrdinal j := IsOrdinal.of_mem hj
  rcases IsOrdinal.mem_trichotomy (α := i) (β := j) with hij | rfl | hji
  · exact False.elim ((h.2.1 i hi j hj hij).2 he)
  · rfl
  · exact False.elim ((h.2.1 j hj i hi hji).2 he.symm)

theorem IsInternalCofinalStrictChain.index_mono {κ P S c i j : V} [IsOrdinal κ]
    (h : IsInternalCofinalStrictChain κ P S c) (hP : IsForcingPoset P S)
    (hi : i ∈ κ) (hj : j ∈ κ) (he : ⟨c ‘ i, c ‘ j⟩ₖ ∈ S) : i ⊆ j := by
  let : IsOrdinal i := IsOrdinal.of_mem hi
  let : IsOrdinal j := IsOrdinal.of_mem hj
  rcases IsOrdinal.mem_trichotomy (α := i) (β := j) with hij | rfl | hji
  · exact (show IsOrdinal j from inferInstance).transitive i hij
  · exact subset_refl _
  · have hji' := h.2.1 j hj i hi hji
    exact False.elim (hji'.2 (hP.2 _ (function_value_mem h.1 hj) _ (function_value_mem h.1 hi) hji'.1 he))

noncomputable def codedSelectedClassNodes (M κ c : V) : V :=
  {x ∈ codedClassNodes M ; ∃ i ∈ κ, (codedClassLevels M) ‘ x = c ‘ i}

theorem mem_codedSelectedClassNodes (M κ c x : V) :
    x ∈ codedSelectedClassNodes M κ c ↔ x ∈ codedClassNodes M ∧ ∃ i ∈ κ, (codedClassLevels M) ‘ x = c ‘ i :=
  mem_sep_iff

instance codedSelectedClassNodes_definable : ℒₛₑₜ-function₃[V] codedSelectedClassNodes := by
  have h : ℒₛₑₜ-relation₄[V] (fun T M κ c ↦ ∀ x, x ∈ T ↔
      x ∈ codedClassNodes M ∧ ∃ i ∈ κ, (codedClassLevels M) ‘ x = c ‘ i) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_codedSelectedClassNodes]
  rfl

noncomputable def codedSelectedClassOrder (M κ c : V) : V :=
  codedClassOrder M ∩ (codedSelectedClassNodes M κ c ×ˢ codedSelectedClassNodes M κ c)

theorem pair_mem_codedSelectedClassOrder (M κ c x y : V) :
    ⟨x, y⟩ₖ ∈ codedSelectedClassOrder M κ c ↔
      ⟨x, y⟩ₖ ∈ codedClassOrder M ∧ x ∈ codedSelectedClassNodes M κ c ∧ y ∈ codedSelectedClassNodes M κ c := by
  simp only [codedSelectedClassOrder, mem_inter_iff, kpair_mem_iff]

instance codedSelectedClassOrder_definable : ℒₛₑₜ-function₃[V] codedSelectedClassOrder := by
  unfold codedSelectedClassOrder
  definability

noncomputable def codedSelectedClassRank (M κ c : V) : V :=
  {p ∈ codedSelectedClassNodes M κ c ×ˢ κ ; (codedClassLevels M) ‘ (kpair.π₁ p) = c ‘ (kpair.π₂ p)}

theorem pair_mem_codedSelectedClassRank (M κ c x i : V) :
    ⟨x, i⟩ₖ ∈ codedSelectedClassRank M κ c ↔
      x ∈ codedSelectedClassNodes M κ c ∧ i ∈ κ ∧ (codedClassLevels M) ‘ x = c ‘ i := by
  simp only [codedSelectedClassRank, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

instance codedSelectedClassRank_definable : ℒₛₑₜ-function₃[V] codedSelectedClassRank := by
  have h : ℒₛₑₜ-relation₄[V] (fun r M κ c ↦ ∀ p, p ∈ r ↔
      p ∈ codedSelectedClassNodes M κ c ×ˢ κ ∧ (codedClassLevels M) ‘ (kpair.π₁ p) = c ‘ (kpair.π₂ p)) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [codedSelectedClassRank, mem_sep_iff]
  rfl

theorem codedSelectedClassRank_function {M κ P S c : V} [IsOrdinal κ]
    (hc : IsInternalCofinalStrictChain κ P S c) :
    codedSelectedClassRank M κ c ∈ κ ^ codedSelectedClassNodes M κ c := by
  apply mem_function_iff.mpr
  refine ⟨fun _ hp ↦ (mem_sep_iff.mp hp).1, ?_⟩
  intro x hx
  obtain ⟨i, hi, he⟩ := ((mem_codedSelectedClassNodes _ _ _ _).mp hx).2
  refine ⟨i, (pair_mem_codedSelectedClassRank _ _ _ _ _).mpr ⟨hx, hi, he⟩, ?_⟩
  intro j hj
  have hj' := (pair_mem_codedSelectedClassRank _ _ _ _ _).mp hj
  exact hc.value_injective hj'.2.1 hi (hj'.2.2.symm.trans he)

theorem codedSelectedClassRank_spec {M κ P S c x : V} [IsOrdinal κ]
    (hc : IsInternalCofinalStrictChain κ P S c) (hx : x ∈ codedSelectedClassNodes M κ c) :
    (codedSelectedClassRank M κ c) ‘ x ∈ κ ∧
      (codedClassLevels M) ‘ x = c ‘ ((codedSelectedClassRank M κ c) ‘ x) := by
  have hf := codedSelectedClassRank_function (M := M) hc
  let : IsFunction (codedSelectedClassRank M κ c) := IsFunction.of_mem hf
  have hp := kpair_value_mem ((domain_eq_of_mem_function hf).symm ▸ hx)
  exact ((pair_mem_codedSelectedClassRank _ _ _ _ _).mp hp).2

end ZFVP.Schmerl

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W)

theorem selectedClassOrder_poset (κ c : V) :
    IsForcingPoset (codedSelectedClassNodes R.code κ c) (codedSelectedClassOrder R.code κ c) := by
  have hsub {x : V} (hx : x ∈ codedSelectedClassNodes R.code κ c) : x ∈ codedClassNodes R.code :=
    ((mem_codedSelectedClassNodes _ _ _ _).mp hx).1
  refine ⟨⟨fun _ hp ↦ (mem_inter_iff.mp hp).2, ?_, ?_⟩, ?_⟩
  · intro x hx
    exact (pair_mem_codedSelectedClassOrder _ _ _ _ _).mpr ⟨R.classOrder_poset.1.2.1 x (hsub hx), hx, hx⟩
  · intro x hx y hy z hz hxy hyz
    exact (pair_mem_codedSelectedClassOrder _ _ _ _ _).mpr
      ⟨R.classOrder_poset.1.2.2 x (hsub hx) y (hsub hy) z (hsub hz)
        (mem_inter_iff.mp hxy).1 (mem_inter_iff.mp hyz).1, hx, hz⟩
  · intro x hx y hy hxy hyx
    exact R.classOrder_poset.2 x (hsub hx) y (hsub hy) (mem_inter_iff.mp hxy).1 (mem_inter_iff.mp hyx).1

theorem selectedClassTree {κ c : V} [IsOrdinal κ]
    (hc : IsInternalCofinalStrictChain κ (codedOrdinals R.code) (codedOrdinalOrder R.code) c) :
    InternalRankedTree (codedSelectedClassNodes R.code κ c) (codedSelectedClassOrder R.code κ c) κ
      (codedSelectedClassRank R.code κ c) := by
  have hsub {x : V} (hx : x ∈ codedSelectedClassNodes R.code κ c) : x ∈ codedClassNodes R.code :=
    ((mem_codedSelectedClassNodes _ _ _ _).mp hx).1
  refine ⟨codedSelectedClassRank_function hc, ?_, ?_⟩
  · intro x hx y hy hxy
    have hix := codedSelectedClassRank_spec hc hx
    have hiy := codedSelectedClassRank_spec hc hy
    have hlevels := R.classLevels_monotone (hsub hx) (hsub hy) (mem_inter_iff.mp hxy).1
    rw [hix.2, hiy.2] at hlevels
    exact hc.index_mono R.ordinalOrder_poset hix.1 hiy.1 hlevels
  · intro x hx y hy z hz hxz hyz
    exact (R.classOrder_below_linear (hsub hx) (hsub hy) (hsub hz)
      (mem_inter_iff.mp hxz).1 (mem_inter_iff.mp hyz).1).imp
      (fun h ↦ (pair_mem_codedSelectedClassOrder _ _ _ _ _).mpr ⟨h, hx, hy⟩)
      (fun h ↦ (pair_mem_codedSelectedClassOrder _ _ _ _ _).mpr ⟨h, hy, hx⟩)

theorem selectedClassRank_comparable_injective {κ c x y : V} [IsOrdinal κ]
    (hc : IsInternalCofinalStrictChain κ (codedOrdinals R.code) (codedOrdinalOrder R.code) c)
    (hx : x ∈ codedSelectedClassNodes R.code κ c) (hy : y ∈ codedSelectedClassNodes R.code κ c)
    (hxy : ⟨x, y⟩ₖ ∈ codedSelectedClassOrder R.code κ c)
    (he : (codedSelectedClassRank R.code κ c) ‘ x = (codedSelectedClassRank R.code κ c) ‘ y) : x = y := by
  apply R.classLevels_comparable_injective ((mem_codedSelectedClassNodes _ _ _ _).mp hx).1
    ((mem_codedSelectedClassNodes _ _ _ _).mp hy).1 (mem_inter_iff.mp hxy).1
  rw [(codedSelectedClassRank_spec hc hx).2, (codedSelectedClassRank_spec hc hy).2, he]

theorem selectedClassRank_onto {κ c i : V} [IsOrdinal κ]
    (hc : IsInternalCofinalStrictChain κ (codedOrdinals R.code) (codedOrdinalOrder R.code) c)
    (hi : i ∈ κ) : ∃ x ∈ codedSelectedClassNodes R.code κ c, (codedSelectedClassRank R.code κ c) ‘ x = i := by
  obtain ⟨x, hx, he⟩ := R.classLevels_onto (function_value_mem hc.1 hi)
  have hxT := (mem_codedSelectedClassNodes _ _ _ _).mpr ⟨hx, i, hi, he⟩
  let : IsFunction (codedSelectedClassRank R.code κ c) := IsFunction.of_mem (codedSelectedClassRank_function hc)
  exact ⟨x, hxT, value_eq_of_kpair_mem ((pair_mem_codedSelectedClassRank _ _ _ _ _).mpr ⟨hxT, hi, he⟩)⟩

theorem exists_selectedClassTree_of_codedRubin {κ : V} [IsOrdinal κ] (h : IsCodedRubin R.code κ) :
    ∃ c, IsInternalCofinalStrictChain κ (codedOrdinals R.code) (codedOrdinalOrder R.code) c ∧
      InternalRankedTree (codedSelectedClassNodes R.code κ c) (codedSelectedClassOrder R.code κ c) κ
        (codedSelectedClassRank R.code κ c) ∧
      IsForcingPoset (codedSelectedClassNodes R.code κ c) (codedSelectedClassOrder R.code κ c) ∧
      ∀ x ∈ codedSelectedClassNodes R.code κ c, ∀ y ∈ codedSelectedClassNodes R.code κ c,
        ⟨x, y⟩ₖ ∈ codedSelectedClassOrder R.code κ c →
        (codedSelectedClassRank R.code κ c) ‘ x = (codedSelectedClassRank R.code κ c) ‘ y → x = y := by
  obtain ⟨c, hc⟩ := R.exists_cofinal_ordinal_chain h
  exact ⟨c, hc, R.selectedClassTree hc, R.selectedClassOrder_poset κ c,
    fun _ hx _ hy hxy he ↦ R.selectedClassRank_comparable_injective hc hx hy hxy he⟩

end ZFVP.BinaryRelationRepresentation
