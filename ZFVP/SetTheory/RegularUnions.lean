import ZFVP.SetTheory.WellOrderedSurjection
import ZFVP.SetTheory.WellOrderingChoice
import ZFVP.SetTheory.Hessenberg
import ZFVP.SetTheory.LevyCollapseSmallSets
import ZFVP.SetTheory.InternalChoice
import ZFVP.SetTheory.WitnessClosure

/-! Unions of small families are small: with choice, the union of a family indexed by `I` of
sets of size at most `ν` has size at most `|I × ν|`; below a regular cardinal `δ`, unions of
fewer than `δ` sets of size below `δ` have size below `δ`, and unions of at most `δ` sets of size
at most `δ` have size at most `δ`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The injections of the value of `f` at `i` into `ν`. -/
noncomputable def valueInjections (f ν i : V) : V := {g ∈ ν ^ (f ‘ i) ; Injective g}

theorem valueInjections_definable_one (f ν : V) : ℒₛₑₜ-function₁[V] (valueInjections f ν) := by
  have h : ℒₛₑₜ-relation[V] (fun S i ↦ ∀ g, g ∈ S ↔ g ∈ ν ^ (f ‘ i) ∧ Injective g) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = valueInjections f ν (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [valueInjections, mem_sep_iff]

theorem function_mem_of_isFunction' {g I X : V} [hg : IsFunction g] (hd : domain g = I) (hr : range g = X) :
    g ∈ X ^ I := by
  obtain ⟨X', Y', hg'⟩ := hg.mem_func
  rw [mem_function_iff]
  constructor
  · intro q hq
    obtain ⟨x, -, y, -, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hg' q hq)
    exact kpair_mem_iff.mpr ⟨by rw [← hd]; exact mem_domain_of_kpair_mem hq,
      by rw [← hr]; exact mem_range_of_kpair_mem hq⟩
  · intro x hx
    rw [← hd] at hx
    exact ⟨g ‘ x, kpair_value_mem hx, fun y hy ↦ (value_eq_of_kpair_mem hy).symm⟩

/-- `z` codes `x` as a member of the `i`-th set via the chosen injection. -/
def UnionCode (f g I x z : V) : Prop := ∃ i ∈ I, x ∈ f ‘ i ∧ z = ⟨i, (g ‘ i) ‘ x⟩ₖ

instance unionCode_definable (f g I : V) : ℒₛₑₜ-relation (UnionCode f g I) := by
  unfold UnionCode
  definability

/-- The union of a family of sets of size at most `ν` has size at most `|I × ν|`. -/
theorem sUnion_range_cardLE_prod (hAC : InternalChoice V) {I f ν : V} [IsFunction f]
    (hdom : domain f = I) (hsmall : ∀ i ∈ I, f ‘ i ≤# ν) : ⋃ˢ range f ≤# I ×ˢ ν := by
  have hne : ∀ i ∈ I, IsNonempty (valueInjections f ν i) := by
    intro i hi
    obtain ⟨g, hg, hginj⟩ := hsmall i hi
    exact ⟨⟨g, mem_sep_iff.mpr ⟨hg, hginj⟩⟩⟩
  obtain ⟨g, hgf, hgd, hgval⟩ := choice_for_definable_family hAC I _ (valueInjections_definable_one f ν) hne
  refine cardLE_of_separating_relation (wellOrderable_of_internalChoice hAC _)
    (UnionCode f g I) inferInstance ?_ ?_
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
    obtain ⟨i, hiy⟩ := mem_range_iff.mp hy
    have hi : i ∈ I := by rw [← hdom]; exact mem_domain_of_kpair_mem hiy
    have hyv : y = f ‘ i := (value_eq_of_kpair_mem hiy).symm
    rw [hyv] at hxy
    have hgi := mem_sep_iff.mp (hgval i hi)
    exact ⟨⟨i, (g ‘ i) ‘ x⟩ₖ, kpair_mem_iff.mpr ⟨hi, function_value_mem hgi.1 hxy⟩, i, hi, hxy, rfl⟩
  · intro x hx x' hx' z hz h1 h2
    obtain ⟨i, hi, hxi, rfl⟩ := h1
    obtain ⟨i', hi', hx'i, he⟩ := h2
    have hii : i = i' := (kpair_inj he).1
    subst hii
    have hval : (g ‘ i) ‘ x = (g ‘ i) ‘ x' := (kpair_inj he).2
    have hgi := mem_sep_iff.mp (hgval i hi)
    exact injective_value_eq hgi.1 hgi.2 hxi hx'i hval

theorem ordinal_union_omega_eq {ρ : V} [IsOrdinal ρ] (hω : (ω : V) ⊆ ρ) : ρ ∪ (ω : V) = ρ := by
  apply mem_ext
  intro x
  rw [mem_union_iff]
  exact ⟨fun h ↦ h.elim id (fun h ↦ hω x h), Or.inl⟩

/-- The union of at most `δ` sets of size at most `δ` has size at most `δ`. -/
theorem sUnion_range_cardLE_of_regular (hAC : InternalChoice V) {δ : V} (hreg : IsRegularCardinal δ)
    {I f : V} [IsFunction f] (hdom : domain f = I) (hI : I ≤# δ) (hsmall : ∀ i ∈ I, f ‘ i ≤# δ) :
    ⋃ˢ range f ≤# δ := by
  have : IsOrdinal δ := hreg.1.1
  have h1 : ⋃ˢ range f ≤# I ×ˢ δ := sUnion_range_cardLE_prod hAC hdom hsmall
  have h2 : I ×ˢ δ ≤# δ ×ˢ δ := prod_cardLE_prod hI (cardLE_of_subset (fun x hx ↦ hx))
  have h3 : δ ×ˢ δ ≤# δ ∪ (ω : V) := ordinal_prod_cardLE_union_omega δ
  rw [ordinal_union_omega_eq hreg.2.1] at h3
  exact (h1.trans h2).trans h3

/-- The bounds of the values of `f` in `δ`. -/
noncomputable def valueBounds (f δ i : V) : V := {μ ∈ δ ; f ‘ i ≤# μ}

theorem valueBounds_definable_one (f δ : V) : ℒₛₑₜ-function₁[V] (valueBounds f δ) := by
  have h : ℒₛₑₜ-relation[V] (fun S i ↦ ∀ μ, μ ∈ S ↔ μ ∈ δ ∧ f ‘ i ≤# μ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = valueBounds f δ (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [valueBounds, mem_sep_iff]

/-- Below a regular cardinal, the union of fewer than `δ` sets of size below `δ` has size below
`δ`. -/
theorem sUnion_range_small_of_regular (hAC : InternalChoice V) {δ : V} (hreg : IsRegularCardinal δ)
    (hωδ : (ω : V) ∈ δ) {I f lam : V} [IsFunction f] (hdom : domain f = I) (hlam : lam ∈ δ) (hI : I ≤# lam)
    (hsmall : ∀ i ∈ I, ∃ μ ∈ δ, f ‘ i ≤# μ) : ∃ μ ∈ δ, ⋃ˢ range f ≤# μ := by
  have hδ : IsOrdinal δ := hreg.1.1
  have hlamo : IsOrdinal lam := IsOrdinal.of_mem hlam
  -- choose a bound for each value
  have hne : ∀ i ∈ I, IsNonempty (valueBounds f δ i) := by
    intro i hi
    obtain ⟨μ, hμ, hle⟩ := hsmall i hi
    exact ⟨⟨μ, mem_sep_iff.mpr ⟨hμ, hle⟩⟩⟩
  obtain ⟨b, hbf, hbd, hbval⟩ := choice_for_definable_family hAC I _ (valueBounds_definable_one f δ) hne
  have hS : range b ⊆ δ := by
    intro μ hμ
    obtain ⟨i, hiμ⟩ := mem_range_iff.mp hμ
    have hi : i ∈ I := by rw [← hbd]; exact mem_domain_of_kpair_mem hiμ
    have := hbval i hi
    rw [value_eq_of_kpair_mem hiμ] at this
    exact (mem_sep_iff.mp this).1
  have hSle : range b ≤# lam :=
    (cardLE_of_surjective_function (wellOrderable_of_internalChoice hAC I)
      (function_mem_of_isFunction' hbd rfl) rfl).trans hI
  obtain ⟨ν, hν, hSν⟩ := regular_small_subset_bounded hreg hS hlam hSle
  have hνo : IsOrdinal ν := IsOrdinal.of_mem hν
  have hsmall' : ∀ i ∈ I, f ‘ i ≤# ν := by
    intro i hi
    have hb := mem_sep_iff.mp (hbval i hi)
    have hbν : b ‘ i ∈ ν := hSν _ (mem_range_of_kpair_mem (kpair_value_mem (by rw [hbd]; exact hi)))
    exact hb.2.trans (cardLE_of_subset (IsOrdinal.toIsTransitive.transitive _ hbν))
  let ρ : V := lam ∪ ν
  have hρo : IsOrdinal ρ := ordinal_union_ordinal lam ν
  have hρ : ρ ∈ δ := union_mem_of_ordinals hlam hν
  have hlamρ : lam ⊆ ρ := fun x hx ↦ mem_union_iff.mpr (Or.inl hx)
  have hνρ : ν ⊆ ρ := fun x hx ↦ mem_union_iff.mpr (Or.inr hx)
  have h1 : ⋃ˢ range f ≤# I ×ˢ ν := sUnion_range_cardLE_prod hAC hdom hsmall'
  have h2 : I ×ˢ ν ≤# ρ ×ˢ ρ := prod_cardLE_prod (hI.trans (cardLE_of_subset hlamρ)) (cardLE_of_subset hνρ)
  have h3 : ρ ×ˢ ρ ≤# ρ ∪ (ω : V) := ordinal_prod_cardLE_union_omega ρ
  exact ⟨ρ ∪ (ω : V), union_mem_of_ordinals hρ hωδ, (h1.trans h2).trans h3⟩

end ZFVP
