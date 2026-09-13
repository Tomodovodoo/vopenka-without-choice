import ZFVP.SetTheory.Hessenberg
import ZFVP.SetTheory.FiniteSequences
import ZFVP.SetTheory.CardinalSmallUnions
import ZFVP.SetTheory.OrdinalDependentChoiceAC

/-! `|λ^{<ω}| = λ` for infinite initial `λ` (with choice): each `λ ^ n` injects into `λ` by
Hessenberg, and the countable union of the powers injects into `ω × λ`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `A ^ (n + 1)` injects into `A ^ n × A` via `f ↦ ⟨f ↾ n, f n⟩`. -/
theorem function_power_succ_cardLE (A n : V) : A ^ succ n ≤# (A ^ n) ×ˢ A := by
  let F : V → V := fun f ↦ ⟨f ↾ n, f ‘ n⟩ₖ
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  refine ⟨definableGraph (A ^ succ n) F hF, definableGraph_mem_function_of_mapsTo _ _ F hF ?_, ?_⟩
  · intro f hf
    exact kpair_mem_iff.mpr ⟨function_restrict_mem hf (mem_subset_refl n),
      function_value_mem hf (mem_succ_self n)⟩
  · intro f g z hf hg
    obtain ⟨hfA, rfl⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hf
    obtain ⟨hgA, hz⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hg
    obtain ⟨h1, h2⟩ := kpair_iff.mp hz
    obtain ⟨t, x, ht, hx, rfl⟩ := function_succ_decompose hfA
    obtain ⟨t', x', ht', hx', rfl⟩ := function_succ_decompose hgA
    have hval : ∀ {t x : V}, t ∈ A ^ n → x ∈ A → (insert ⟨n, x⟩ₖ t) ‘ n = x := by
      intro t x ht hx
      have : IsFunction (insert ⟨n, x⟩ₖ t) := IsFunction.of_mem (function_append_mem ht hx)
      exact value_eq_of_kpair_mem (mem_insert.mpr (Or.inl rfl))
    rw [function_append_restrict ht, function_append_restrict ht'] at h1
    rw [hval ht hx, hval ht' hx'] at h2
    rw [h1, h2]

/-- `A ^ 0` injects into any nonempty set. -/
theorem function_power_zero_cardLE {A B : V} (hB : IsNonempty B) : A ^ (∅ : V) ≤# B := by
  obtain ⟨b, hb⟩ := hB.nonempty
  let F : V → V := fun _ ↦ b
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  have hsub : ∀ f ∈ A ^ (∅ : V), f = ∅ := by
    intro f hf
    apply mem_ext
    intro p
    constructor
    · intro hp
      have := subset_prod_of_mem_function hf p hp
      obtain ⟨x, hx, _⟩ := mem_prod_iff.mp this
      exact (not_mem_empty hx).elim
    · intro hp
      exact (not_mem_empty hp).elim
  refine ⟨definableGraph (A ^ (∅ : V)) F hF, definableGraph_mem_function_of_mapsTo _ _ F hF
    (fun _ _ ↦ hb), ?_⟩
  intro f g z hf hg
  obtain ⟨hfA, _⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hf
  obtain ⟨hgA, _⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hg
  rw [hsub f hfA, hsub g hgA]

/-- Every finite power of an infinite initial ordinal injects into it. -/
theorem function_power_cardLE_initial {lam : V} (hlam : IsInitialOrdinal lam) (hω : (ω : V) ⊆ lam) :
    ∀ n ∈ (ω : V), lam ^ n ≤# lam := by
  apply naturalNumber_induction (fun n ↦ lam ^ n ≤# lam) (by definability)
  · exact function_power_zero_cardLE ⟨∅, hω ∅ empty_mem_ω⟩
  · intro n _ ih
    exact (function_power_succ_cardLE lam n).trans
      (prod_cardLE_of_cardLE_initial hlam hω ih (CardLE.refl lam))

/-- The finite sequences from an infinite initial ordinal inject into it (using choice). -/
theorem finiteSequences_cardLE_initial (hAC : InternalChoice V) {lam : V} (hlam : IsInitialOrdinal lam)
    (hω : (ω : V) ⊆ lam) : finiteSequences lam ≤# lam := by
  have : IsOrdinal lam := hlam.1
  let C := definableGraph (ω : V) (fun n ↦ lam ^ n) (by definability)
  have hC : IsFunction C := definableGraph_isFunction _ _ _
  have hd : domain C = (ω : V) := domain_definableGraph _ _ _
  have hCv : ∀ n ∈ (ω : V), C ‘ n = lam ^ n := fun n hn ↦ value_definableGraph _ _ _ hn
  have hcount : ∀ n ∈ (ω : V), (C ‘ n) ≤# lam := by
    intro n hn
    rw [hCv n hn]
    exact function_power_cardLE_initial hlam hω n hn
  obtain ⟨g, hg⟩ := ordinal_family_injections (dependentChoiceAt_of_internalChoice hAC (ω : V)) hcount
  have hunion : (⋃ˢ range C) ≤# ((ω : V) ×ˢ lam) :=
    union_cardLE_ordinal_prod_of_injection_family hd hg
  have hsub : finiteSequences lam ⊆ ⋃ˢ range C := by
    intro s hs
    obtain ⟨n, hn, hsn⟩ := (mem_finiteSequences_iff lam s).mp hs
    refine mem_sUnion_iff.mpr ⟨lam ^ n, ?_, hsn⟩
    rw [← hCv n hn]
    exact value_mem_range (IsFunction.mem_function C) (hd ▸ hn)
  exact ((cardLE_of_subset hsub).trans hunion).trans
    (prod_cardLE_of_cardLE_initial hlam hω (cardLE_of_subset hω) (CardLE.refl lam))

end ZFVP
