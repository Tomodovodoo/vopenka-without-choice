import Mathlib.SetTheory.Cardinal.Aleph
import ZFVP.ModelTheory.FiniteSubsetsAbsolute
import ZFVP.SetTheory.SplittingScheme
import ZFVP.SetTheory.UniformNumerals

/-! The poset vocabulary of Enayat's Definitions 5.10, 5.11, 5.12 and 5.16 in "Models of set
theory: extensions and dead ends", for an internal poset ordered by inclusion: filters over the
poset, maximal filters, and cofinal chains of order type `ω₁`. The example after Definition 5.12
is here too: for an internal function `f : A → 2`, the finite subsets of `f` form a maximal filter
of `Fin(A,2)`. The last group of results builds the characteristic function of a subset of `A`,
which is the map used to turn subsets of `A` into elements of `2 ^ A`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A singleton is internally finite. -/
theorem internallyFinite_singleton (a : V) : IsInternallyFinite ({a} : V) := by
  simpa using internallyFinite_insert (internallyFinite_empty (V := V)) a

/-- Enayat 5.10(b): a filter over an internal poset ordered by inclusion. -/
def IsInternalFilter (P : V) (F : V → Prop) : Prop :=
  (∀ x, F x → x ∈ P) ∧ ∀ x y, F x → F y → ∃ z, F z ∧ x ⊆ z ∧ y ⊆ z

/-- Enayat 5.10(c): a filter that has no proper extension to a filter. -/
def IsMaximalInternalFilter (P : V) (F : V → Prop) : Prop :=
  IsInternalFilter P F ∧
    ∀ F' : V → Prop, IsInternalFilter P F' → (∀ x, F x → F' x) → ∀ x, F' x → F x

/-- A chain of order type `ω₁`, increasing and cofinal in `F`. -/
def IsCofinalOmegaOneChain (F : V → Prop)
    (p : Ordinal.ToType (Ordinal.omega.{0} 1) → V) : Prop :=
  (∀ i, F (p i)) ∧ (∀ i i', i < i' → p i ⊆ p i' ∧ p i ≠ p i') ∧ (∀ x, F x → ∃ i, x ⊆ p i)

/-- Enayat 5.16 asks for a maximal filter with a cofinal chain of order type `ω₁`. -/
def HasCofinalOmegaOneChain (F : V → Prop) : Prop := ∃ p, IsCofinalOmegaOneChain F p

/-- The union of all finite subsets of a set is that set. -/
theorem sUnion_finiteSubsets (f : V) : ⋃ˢ (finiteSubsets f) = f := by
  apply mem_ext
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, hyx⟩ := mem_sUnion_iff.mp hy
    exact ((mem_finiteSubsets_iff f x).mp hx).1 y hyx
  · intro hy
    refine mem_sUnion_iff.mpr ⟨{y}, ?_, mem_singleton_iff.mpr rfl⟩
    exact (mem_finiteSubsets_iff f _).mpr
      ⟨singleton_subset_iff_mem.mpr hy, internallyFinite_singleton y⟩

/-- Enayat's example after Definition 5.12: for an internal `f : A → 2`, the finite subsets of `f`
form a maximal filter of `Fin(A,2)`. -/
theorem isMaximalInternalFilter_finiteSubsets {A f : V} (hf : f ∈ ((2 : ℕ) : V) ^ A) :
    IsMaximalInternalFilter (finitePartialFunctions A ((2 : ℕ) : V))
      (fun p ↦ p ⊆ f ∧ IsInternallyFinite p) := by
  have hfun : IsFunction f := IsFunction.of_mem hf
  have hprod : f ⊆ A ×ˢ ((2 : ℕ) : V) := subset_prod_of_mem_function hf
  have hdom : domain f = A := domain_eq_of_mem_function hf
  have hmem : ∀ p : V, p ⊆ f → IsInternallyFinite p →
      p ∈ finitePartialFunctions A ((2 : ℕ) : V) := by
    intro p hpf hpfin
    exact (mem_finitePartialFunctions _ _ _).mpr
      ⟨fun z hz ↦ hprod z (hpf z hz), IsFunction.ofSubset f p hpf,
        internallyFinite_domain hpfin⟩
  refine ⟨⟨fun x hx ↦ hmem x hx.1 hx.2, ?_⟩, ?_⟩
  · intro x y hx hy
    refine ⟨x ∪ y, ⟨?_, internallyFinite_union hx.2 hy.2⟩,
      fun z hz ↦ mem_union_iff.mpr (Or.inl hz), fun z hz ↦ mem_union_iff.mpr (Or.inr hz)⟩
    intro z hz
    rcases mem_union_iff.mp hz with h | h
    · exact hx.1 z h
    · exact hy.1 z h
  · intro F' hF' hle q hq
    obtain ⟨hqsub, hqfun, hqdomfin⟩ := (mem_finitePartialFunctions _ _ _).mp (hF'.1 q hq)
    refine ⟨?_, internallyFinite_function hqdomfin⟩
    intro p hp
    obtain ⟨x, v, rfl⟩ := IsFunction.mem_eq_kpair hp
    have hxd : x ∈ domain f := by
      rw [hdom]
      exact (kpair_mem_iff.mp (hqsub _ hp)).1
    have hfx : ⟨x, f ‘ x⟩ₖ ∈ f := kpair_value_mem hxd
    have hsing : ({⟨x, f ‘ x⟩ₖ} : V) ⊆ f ∧ IsInternallyFinite ({⟨x, f ‘ x⟩ₖ} : V) :=
      ⟨singleton_subset_iff_mem.mpr hfx, internallyFinite_singleton _⟩
    obtain ⟨z, hz, hqz, hsz⟩ := hF'.2 q _ hq (hle _ hsing)
    have hzfun : IsFunction z := ((mem_finitePartialFunctions _ _ _).mp (hF'.1 z hz)).2.1
    have hv : v = f ‘ x :=
      IsFunction.unique (hqz _ hp) (hsz _ (mem_singleton_iff.mpr rfl))
    rw [hv]
    exact hfx

/-- The characteristic function of `s` on `A`: the function on `A` sending members of `s` to `1`
and everything else to `0`. -/
noncomputable def characteristicFunction (A s : V) : V :=
  {p ∈ A ×ˢ ((2 : ℕ) : V) ;
    (kpair.π₁ p ∈ s ∧ kpair.π₂ p = ((1 : ℕ) : V)) ∨
      (kpair.π₁ p ∉ s ∧ kpair.π₂ p = ((0 : ℕ) : V))}

theorem kpair_mem_characteristicFunction (A s x v : V) :
    ⟨x, v⟩ₖ ∈ characteristicFunction A s ↔
      (x ∈ A ∧ v ∈ ((2 : ℕ) : V)) ∧
        ((x ∈ s ∧ v = ((1 : ℕ) : V)) ∨ (x ∉ s ∧ v = ((0 : ℕ) : V))) := by
  simp only [characteristicFunction, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]

theorem zero_mem_two' : ((0 : ℕ) : V) ∈ ((2 : ℕ) : V) := empty_mem_two

theorem one_mem_two' : ((1 : ℕ) : V) ∈ ((2 : ℕ) : V) := succ_empty_mem_two

theorem zero_ne_one' : ((0 : ℕ) : V) ≠ ((1 : ℕ) : V) := zero_ne_one

theorem characteristicFunction_mem (A s : V) : characteristicFunction A s ∈ ((2 : ℕ) : V) ^ A := by
  apply mem_function.intro sep_subset
  intro x hx
  by_cases hxs : x ∈ s
  · refine ExistsUnique.intro ((1 : ℕ) : V)
      ((kpair_mem_characteristicFunction A s x _).mpr
        ⟨⟨hx, one_mem_two'⟩, Or.inl ⟨hxs, rfl⟩⟩) ?_
    intro y hy
    rcases ((kpair_mem_characteristicFunction A s x y).mp hy).2 with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd hxs h
  · refine ExistsUnique.intro ((0 : ℕ) : V)
      ((kpair_mem_characteristicFunction A s x _).mpr
        ⟨⟨hx, zero_mem_two'⟩, Or.inr ⟨hxs, rfl⟩⟩) ?_
    intro y hy
    rcases ((kpair_mem_characteristicFunction A s x y).mp hy).2 with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h hxs
    · exact h

theorem mem_iff_characteristicFunction {A s x : V} (hs : s ⊆ A) (hx : x ∈ A) :
    x ∈ s ↔ (characteristicFunction A s) ‘ x = ((1 : ℕ) : V) := by
  have hcf : IsFunction (characteristicFunction A s) :=
    IsFunction.of_mem (characteristicFunction_mem A s)
  have hxd : x ∈ domain (characteristicFunction A s) := by
    rw [domain_eq_of_mem_function (characteristicFunction_mem A s)]
    exact hx
  constructor
  · intro hxs
    exact value_eq_of_kpair_mem
      ((kpair_mem_characteristicFunction A s x _).mpr ⟨⟨hx, one_mem_two'⟩, Or.inl ⟨hxs, rfl⟩⟩)
  · intro hv
    have hmem : ⟨x, ((1 : ℕ) : V)⟩ₖ ∈ characteristicFunction A s := by
      have := kpair_value_mem hxd
      rwa [hv] at this
    rcases ((kpair_mem_characteristicFunction A s x _).mp hmem).2 with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · exact absurd h.symm zero_ne_one'

theorem characteristicFunction_injective {A s t : V} (hs : s ⊆ A) (ht : t ⊆ A)
    (h : characteristicFunction A s = characteristicFunction A t) : s = t := by
  apply mem_ext
  intro x
  constructor
  · intro hxs
    have hx : x ∈ A := hs x hxs
    rw [mem_iff_characteristicFunction ht hx, ← h]
    exact (mem_iff_characteristicFunction hs hx).mp hxs
  · intro hxt
    have hx : x ∈ A := ht x hxt
    rw [mem_iff_characteristicFunction hs hx, h]
    exact (mem_iff_characteristicFunction ht hx).mp hxt

instance characteristicFunction_definable : ℒₛₑₜ-function₂[V] characteristicFunction := by
  have h : ℒₛₑₜ-relation₃[V] (fun C A s ↦ ∀ p, p ∈ C ↔ p ∈ A ×ˢ ((2 : ℕ) : V) ∧
      ((kpair.π₁ p ∈ s ∧ kpair.π₂ p = ((1 : ℕ) : V)) ∨
        (kpair.π₁ p ∉ s ∧ kpair.π₂ p = ((0 : ℕ) : V)))) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = characteristicFunction (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [characteristicFunction, mem_sep_iff]

end ZFVP
