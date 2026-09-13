import ZFVP.ModelTheory.SchmerlCodedFunctionStructure
import ZFVP.ModelTheory.SchmerlCodedBranchSequence

/-! Selecting the finite-function domains along an actual internal chain. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
attribute [local aesop 5 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

theorem IsInternalCofinalStrictChain.values_total {κ P S c i j : V} [IsOrdinal κ]
    (hc : IsInternalCofinalStrictChain κ P S c) (hP : IsForcingPoset P S)
    (hi : i ∈ κ) (hj : j ∈ κ) :
    ⟨c ‘ i, c ‘ j⟩ₖ ∈ S ∨ ⟨c ‘ j, c ‘ i⟩ₖ ∈ S := by
  let : IsOrdinal i := IsOrdinal.of_mem hi
  let : IsOrdinal j := IsOrdinal.of_mem hj
  rcases IsOrdinal.mem_trichotomy (α := i) (β := j) with hij | rfl | hji
  · exact Or.inl (hc.2.1 i hi j hj hij).1
  · exact Or.inl (hP.1.2.1 _ (function_value_mem hc.1 hi))
  · exact Or.inr (hc.2.1 j hj i hi hji).1
noncomputable def codedSelectedFunctionNodes (M s κ c : V) : V :=
  {x ∈ codedFunctionNodes M s ; ∃ i ∈ κ, (codedFunctionDomains M s) ‘ x = c ‘ i}

theorem mem_codedSelectedFunctionNodes (M s κ c x : V) :
    x ∈ codedSelectedFunctionNodes M s κ c ↔ x ∈ codedFunctionNodes M s ∧ ∃ i ∈ κ, (codedFunctionDomains M s) ‘ x = c ‘ i :=
  mem_sep_iff

instance codedSelectedFunctionNodes_definable : ℒₛₑₜ-function₄[V] codedSelectedFunctionNodes := by
  have h : ℒₛₑₜ-relation₅[V] (fun T M s κ c ↦ ∀ x, x ∈ T ↔
      x ∈ codedFunctionNodes M s ∧ ∃ i ∈ κ, (codedFunctionDomains M s) ‘ x = c ‘ i) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_codedSelectedFunctionNodes]
  rfl

noncomputable def codedSelectedFunctionOrder (M s κ c : V) : V :=
  codedFunctionOrder M s ∩ (codedSelectedFunctionNodes M s κ c ×ˢ codedSelectedFunctionNodes M s κ c)

theorem pair_mem_codedSelectedFunctionOrder (M s κ c x y : V) :
    ⟨x, y⟩ₖ ∈ codedSelectedFunctionOrder M s κ c ↔
      ⟨x, y⟩ₖ ∈ codedFunctionOrder M s ∧ x ∈ codedSelectedFunctionNodes M s κ c ∧ y ∈ codedSelectedFunctionNodes M s κ c := by
  simp only [codedSelectedFunctionOrder, mem_inter_iff, kpair_mem_iff]

instance codedSelectedFunctionOrder_definable : ℒₛₑₜ-function₄[V] codedSelectedFunctionOrder := by
  unfold codedSelectedFunctionOrder
  definability

noncomputable def codedSelectedFunctionRank (M s κ c : V) : V :=
  {p ∈ codedSelectedFunctionNodes M s κ c ×ˢ κ ; (codedFunctionDomains M s) ‘ (kpair.π₁ p) = c ‘ (kpair.π₂ p)}

theorem pair_mem_codedSelectedFunctionRank (M s κ c x i : V) :
    ⟨x, i⟩ₖ ∈ codedSelectedFunctionRank M s κ c ↔
      x ∈ codedSelectedFunctionNodes M s κ c ∧ i ∈ κ ∧ (codedFunctionDomains M s) ‘ x = c ‘ i := by
  simp only [codedSelectedFunctionRank, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

instance codedSelectedFunctionRank_definable : ℒₛₑₜ-function₄[V] codedSelectedFunctionRank := by
  have h : ℒₛₑₜ-relation₅[V] (fun r M s κ c ↦ ∀ p, p ∈ r ↔
      p ∈ codedSelectedFunctionNodes M s κ c ×ˢ κ ∧ (codedFunctionDomains M s) ‘ (kpair.π₁ p) = c ‘ (kpair.π₂ p)) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [codedSelectedFunctionRank, mem_sep_iff]
  rfl

theorem codedSelectedFunctionRank_function {M s κ P S c : V} [IsOrdinal κ]
    (hc : IsInternalCofinalStrictChain κ P S c) :
    codedSelectedFunctionRank M s κ c ∈ κ ^ codedSelectedFunctionNodes M s κ c := by
  apply mem_function_iff.mpr
  refine ⟨fun _ hp ↦ (mem_sep_iff.mp hp).1, ?_⟩
  intro x hx
  obtain ⟨i, hi, he⟩ := ((mem_codedSelectedFunctionNodes _ _ _ _ _).mp hx).2
  refine ⟨i, (pair_mem_codedSelectedFunctionRank _ _ _ _ _ _).mpr ⟨hx, hi, he⟩, ?_⟩
  intro j hj
  have hj' := (pair_mem_codedSelectedFunctionRank _ _ _ _ _ _).mp hj
  exact hc.value_injective hj'.2.1 hi (hj'.2.2.symm.trans he)

theorem codedSelectedFunctionRank_spec {M s κ P S c x : V} [IsOrdinal κ]
    (hc : IsInternalCofinalStrictChain κ P S c) (hx : x ∈ codedSelectedFunctionNodes M s κ c) :
    (codedSelectedFunctionRank M s κ c) ‘ x ∈ κ ∧
      (codedFunctionDomains M s) ‘ x = c ‘ ((codedSelectedFunctionRank M s κ c) ‘ x) := by
  have hf := codedSelectedFunctionRank_function (M := M) (s := s) hc
  let : IsFunction (codedSelectedFunctionRank M s κ c) := IsFunction.of_mem hf
  have hp := kpair_value_mem ((domain_eq_of_mem_function hf).symm ▸ hx)
  exact ((pair_mem_codedSelectedFunctionRank _ _ _ _ _ _).mp hp).2

end ZFVP.Schmerl
namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W) (s : W)

theorem selectedFunctionOrder_poset (κ c : V) :
    IsForcingPoset (codedSelectedFunctionNodes R.code (R.equiv s).val κ c) (codedSelectedFunctionOrder R.code (R.equiv s).val κ c) := by
  have hsub {x : V} (hx : x ∈ codedSelectedFunctionNodes R.code (R.equiv s).val κ c) : x ∈ codedFunctionNodes R.code (R.equiv s).val :=
    ((mem_codedSelectedFunctionNodes _ _ _ _ _).mp hx).1
  refine ⟨⟨fun _ hp ↦ (mem_inter_iff.mp hp).2, ?_, ?_⟩, ?_⟩
  · intro x hx
    exact (pair_mem_codedSelectedFunctionOrder _ _ _ _ _ _).mpr ⟨(R.functionOrder_poset s).1.2.1 x (hsub hx), hx, hx⟩
  · intro x hx y hy z hz hxy hyz
    exact (pair_mem_codedSelectedFunctionOrder _ _ _ _ _ _).mpr
      ⟨(R.functionOrder_poset s).1.2.2 x (hsub hx) y (hsub hy) z (hsub hz)
        (mem_inter_iff.mp hxy).1 (mem_inter_iff.mp hyz).1, hx, hz⟩
  · intro x hx y hy hxy hyx
    exact (R.functionOrder_poset s).2 x (hsub hx) y (hsub hy) (mem_inter_iff.mp hxy).1 (mem_inter_iff.mp hyx).1

theorem selectedFunctionTree {κ c : V} [IsOrdinal κ]
    (hc : IsInternalCofinalStrictChain κ (codedFiniteDomains R.code (R.equiv s).val) (codedFiniteDomainOrder R.code (R.equiv s).val) c) :
    InternalRankedTree (codedSelectedFunctionNodes R.code (R.equiv s).val κ c) (codedSelectedFunctionOrder R.code (R.equiv s).val κ c) κ
      (codedSelectedFunctionRank R.code (R.equiv s).val κ c) := by
  have hsub {x : V} (hx : x ∈ codedSelectedFunctionNodes R.code (R.equiv s).val κ c) : x ∈ codedFunctionNodes R.code (R.equiv s).val :=
    ((mem_codedSelectedFunctionNodes _ _ _ _ _).mp hx).1
  refine ⟨codedSelectedFunctionRank_function hc, ?_, ?_⟩
  · intro x hx y hy hxy
    have hix := codedSelectedFunctionRank_spec hc hx
    have hiy := codedSelectedFunctionRank_spec hc hy
    have hlevels := R.functionDomains_monotone s (hsub hx) (hsub hy) (mem_inter_iff.mp hxy).1
    rw [hix.2, hiy.2] at hlevels
    exact hc.index_mono (R.finiteDomainOrder_poset s) hix.1 hiy.1 hlevels
  · intro x hx y hy z hz hxz hyz
    have hix := codedSelectedFunctionRank_spec hc hx
    have hiy := codedSelectedFunctionRank_spec hc hy
    have htotal := hc.values_total (R.finiteDomainOrder_poset s) hix.1 hiy.1
    rw [← hix.2, ← hiy.2] at htotal
    rcases htotal with hxy | hyx
    · exact Or.inl ((pair_mem_codedSelectedFunctionOrder _ _ _ _ _ _).mpr
        ⟨R.functionOrder_of_common_above_of_domains s (hsub hx) (hsub hy) (hsub hz)
          (mem_inter_iff.mp hxz).1 (mem_inter_iff.mp hyz).1 hxy, hx, hy⟩)
    · exact Or.inr ((pair_mem_codedSelectedFunctionOrder _ _ _ _ _ _).mpr
        ⟨R.functionOrder_of_common_above_of_domains s (hsub hy) (hsub hx) (hsub hz)
          (mem_inter_iff.mp hyz).1 (mem_inter_iff.mp hxz).1 hyx, hy, hx⟩)

theorem selectedFunctionRank_comparable_injective {κ c x y : V} [IsOrdinal κ]
    (hc : IsInternalCofinalStrictChain κ (codedFiniteDomains R.code (R.equiv s).val) (codedFiniteDomainOrder R.code (R.equiv s).val) c)
    (hx : x ∈ codedSelectedFunctionNodes R.code (R.equiv s).val κ c) (hy : y ∈ codedSelectedFunctionNodes R.code (R.equiv s).val κ c)
    (hxy : ⟨x, y⟩ₖ ∈ codedSelectedFunctionOrder R.code (R.equiv s).val κ c)
    (he : (codedSelectedFunctionRank R.code (R.equiv s).val κ c) ‘ x = (codedSelectedFunctionRank R.code (R.equiv s).val κ c) ‘ y) : x = y := by
  apply R.functionDomains_comparable_injective s ((mem_codedSelectedFunctionNodes _ _ _ _ _).mp hx).1
    ((mem_codedSelectedFunctionNodes _ _ _ _ _).mp hy).1 (mem_inter_iff.mp hxy).1
  rw [(codedSelectedFunctionRank_spec hc hx).2, (codedSelectedFunctionRank_spec hc hy).2, he]

theorem selectedFunctionRank_onto {κ c i : V} [IsOrdinal κ]
    (hc : IsInternalCofinalStrictChain κ (codedFiniteDomains R.code (R.equiv s).val) (codedFiniteDomainOrder R.code (R.equiv s).val) c)
    (hi : i ∈ κ) : ∃ x ∈ codedSelectedFunctionNodes R.code (R.equiv s).val κ c, (codedSelectedFunctionRank R.code (R.equiv s).val κ c) ‘ x = i := by
  obtain ⟨x, hx, he⟩ := R.functionDomains_onto s (function_value_mem hc.1 hi)
  have hxT := (mem_codedSelectedFunctionNodes _ _ _ _ _).mpr ⟨hx, i, hi, he⟩
  let : IsFunction (codedSelectedFunctionRank R.code (R.equiv s).val κ c) := IsFunction.of_mem (codedSelectedFunctionRank_function hc)
  exact ⟨x, hxT, value_eq_of_kpair_mem ((pair_mem_codedSelectedFunctionRank _ _ _ _ _ _).mpr ⟨hxT, hi, he⟩)⟩

theorem exists_selectedFunctionTree_of_codedRubin {κ : V} [IsOrdinal κ] (h : IsCodedRubin R.code κ) (hs : IsInternallyInfinite s) :
    ∃ c, IsInternalCofinalStrictChain κ (codedFiniteDomains R.code (R.equiv s).val) (codedFiniteDomainOrder R.code (R.equiv s).val) c ∧
      InternalRankedTree (codedSelectedFunctionNodes R.code (R.equiv s).val κ c) (codedSelectedFunctionOrder R.code (R.equiv s).val κ c) κ
        (codedSelectedFunctionRank R.code (R.equiv s).val κ c) ∧
      IsForcingPoset (codedSelectedFunctionNodes R.code (R.equiv s).val κ c) (codedSelectedFunctionOrder R.code (R.equiv s).val κ c) ∧
      ∀ x ∈ codedSelectedFunctionNodes R.code (R.equiv s).val κ c, ∀ y ∈ codedSelectedFunctionNodes R.code (R.equiv s).val κ c,
        ⟨x, y⟩ₖ ∈ codedSelectedFunctionOrder R.code (R.equiv s).val κ c →
        (codedSelectedFunctionRank R.code (R.equiv s).val κ c) ‘ x = (codedSelectedFunctionRank R.code (R.equiv s).val κ c) ‘ y → x = y := by
  obtain ⟨c, hc⟩ := R.exists_cofinal_finiteDomain_chain h hs
  exact ⟨c, hc, R.selectedFunctionTree s hc, R.selectedFunctionOrder_poset s κ c,
    fun _ hx _ hy hxy he ↦ R.selectedFunctionRank_comparable_injective s hc hx hy hxy he⟩

end ZFVP.BinaryRelationRepresentation

