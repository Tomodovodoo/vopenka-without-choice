import ZFVP.SetTheory.CountableSubsetFamily
import ZFVP.SetTheory.Hessenberg
import ZFVP.SetTheory.InternalChoice
import ZFVP.SetTheory.Cofinality
import ZFVP.SetTheory.PulledWellOrder

/-! The counting step of the Erdos-Hajnal construction.

Let `lam` be an infinite initial ordinal of cofinality `ω`, witnessed by a map `s : ω → lam`, and
assume every `℘ α` for `α ∈ lam` injects into `lam` (a strong limit). Then `℘ lam` injects into
`countableSubsets lam`.

A subset `X ⊆ lam` is cut into the pieces `X ∩ s ‘ n`. Each piece is a subset of `s ‘ n`, so it
gets a name in `lam` from an injection `℘ (s ‘ n) → lam`, chosen once for all `n` by internal
choice. A pairing function `p : lam × lam → lam` glues the index `n` to that name, and the set of
the resulting `ω`-many points is the code of `X`. The code is enumerated by `ω`, so it lies in
`countableSubsets lam`, and it determines `X` because `p` is injective (so the index can be read
off), each name map is injective (so the piece can be read off), and `s` is cofinal (so the pieces
cover `X`). -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The injections from `℘ (s ‘ n)` into `lam`. -/
noncomputable def sliceInjections (lam s n : V) : V :=
  {j ∈ lam ^ ℘ (s ‘ n) ; Injective j}

theorem mem_sliceInjections_iff {lam s n j : V} :
    j ∈ sliceInjections lam s n ↔ j ∈ lam ^ ℘ (s ‘ n) ∧ Injective j := by
  simp only [sliceInjections, mem_sep_iff]

instance sliceInjections_definable (lam s : V) :
    ℒₛₑₜ-function₁[V] (sliceInjections lam s) := by
  have h : ℒₛₑₜ-relation (fun A n : V ↦ ∀ j, j ∈ A ↔ j ∈ lam ^ ℘ (s ‘ n) ∧ Injective j) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = sliceInjections lam s (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_sliceInjections_iff]

/-- One entry of the code of `X`: the piece `X ∩ s ‘ n` gets the name `(q ‘ n) ‘ (X ∩ s ‘ n)` in
`lam`, and the pairing map `p` glues the index `n` to that name. -/
noncomputable def codePoint (p q s X n : V) : V := p ‘ ⟨n, (q ‘ n) ‘ (X ∩ (s ‘ n))⟩ₖ

instance codePoint_definable₂ (p q s : V) : ℒₛₑₜ-function₂[V] (codePoint p q s) := by
  unfold codePoint
  definability

instance codePoint_definable (p q s X : V) : ℒₛₑₜ-function₁[V] (codePoint p q s X) := by
  unfold codePoint
  definability

/-- The code of `X`: the entries `codePoint p q s X n` for `n ∈ ω`, cut out of `lam`. -/
noncomputable def powerCode (p q s lam X : V) : V :=
  {z ∈ lam ; ∃ n ∈ (ω : V), z = codePoint p q s X n}

theorem mem_powerCode_iff {p q s lam X z : V} :
    z ∈ powerCode p q s lam X ↔ z ∈ lam ∧ ∃ n ∈ (ω : V), z = codePoint p q s X n := by
  simp only [powerCode, mem_sep_iff]

theorem powerCode_subset {p q s lam X : V} : powerCode p q s lam X ⊆ lam :=
  fun _ hz ↦ (mem_powerCode_iff.mp hz).1

instance powerCode_definable (p q s lam : V) : ℒₛₑₜ-function₁[V] (powerCode p q s lam) := by
  have h : ℒₛₑₜ-relation
      (fun Y X : V ↦ ∀ z, z ∈ Y ↔ z ∈ lam ∧ ∃ n ∈ (ω : V), z = codePoint p q s X n) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = powerCode p q s lam (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_powerCode_iff]

/-- At an infinite initial ordinal of cofinality `ω` all of whose smaller power sets inject into
it, the power set injects into the family of countably enumerated subsets. -/
theorem power_cardLE_countableSubsets (hAC : InternalChoice V) {lam : V}
    (hlam : IsInitialOrdinal lam) (hω : (ω : V) ∈ lam)
    (hcof : ∃ s, s ∈ lam ^ (ω : V) ∧ IsCofinalMap lam (ω : V) s)
    (hsl : ∀ α ∈ lam, ℘ α ≤# lam) :
    ℘ lam ≤# countableSubsets lam := by
  have hord : IsOrdinal lam := hlam.1
  have hωsub : (ω : V) ⊆ lam := IsOrdinal.toIsTransitive.transitive _ hω
  -- Step 1: a pairing function on `lam`.
  obtain ⟨p, hp, hpinj⟩ : lam ×ˢ lam ≤# lam := by
    have h := ordinal_prod_cardLE_union_omega lam
    rwa [union_eq_iff_right.mpr hωsub] at h
  have hpf : IsFunction p := IsFunction.of_mem hp
  have hpdom : domain p = lam ×ˢ lam := domain_eq_of_mem_function hp
  obtain ⟨s, hs, hscof⟩ := hcof
  -- Step 2: one injection `℘ (s ‘ n) → lam` for every `n ∈ ω`.
  have hFne : ∀ n ∈ (ω : V), IsNonempty (sliceInjections lam s n) := by
    intro n hn
    obtain ⟨j, hj, hjinj⟩ := hsl (s ‘ n) (function_value_mem hs hn)
    exact ⟨j, mem_sliceInjections_iff.mpr ⟨hj, hjinj⟩⟩
  obtain ⟨q, _, _, hqval⟩ :=
    choice_for_definable_family hAC (ω : V) (sliceInjections lam s) inferInstance hFne
  have hq : ∀ n ∈ (ω : V), q ‘ n ∈ lam ^ ℘ (s ‘ n) ∧ Injective (q ‘ n) :=
    fun n hn ↦ mem_sliceInjections_iff.mp (hqval n hn)
  -- The pieces of a subset of `lam`, and the pairs the code is built from.
  have hpiece : ∀ X n : V, X ∩ (s ‘ n) ∈ ℘ (s ‘ n) := by
    intro X n
    exact mem_power_iff.mpr fun z hz ↦ (mem_inter_iff.mp hz).2
  have hname : ∀ n ∈ (ω : V), ∀ X : V, (q ‘ n) ‘ (X ∩ (s ‘ n)) ∈ lam :=
    fun n hn X ↦ function_value_mem (hq n hn).1 (hpiece X n)
  have hpair : ∀ n ∈ (ω : V), ∀ X : V,
      ⟨n, (q ‘ n) ‘ (X ∩ (s ‘ n))⟩ₖ ∈ lam ×ˢ lam :=
    fun n hn X ↦ kpair_mem_iff.mpr ⟨hωsub n hn, hname n hn X⟩
  have hpt : ∀ n ∈ (ω : V), ∀ X : V, codePoint p q s X n ∈ lam :=
    fun n hn X ↦ function_value_mem hp (hpair n hn X)
  -- Step 3: the code of `X` is a countably enumerated subset of `lam`.
  have hcodemem : ∀ X ∈ ℘ lam, powerCode p q s lam X ∈ countableSubsets lam := by
    intro X _
    have hmaps : ∀ n ∈ (ω : V), codePoint p q s X n ∈ powerCode p q s lam X :=
      fun n hn ↦ mem_powerCode_iff.mpr ⟨hpt n hn X, n, hn, rfl⟩
    refine mem_countableSubsets_of_enumeration powerCode_subset
      (g := definableGraph (ω : V) (codePoint p q s X) inferInstance) ?_ ?_
    · exact definableGraph_mem_function_of_mapsTo _ _ _ _ hmaps
    · rw [range_definableGraph]
      apply SetTheory.subset_antisymm
      · intro y hy
        obtain ⟨n, hn, rfl⟩ := (repl_spec _).mp hy
        exact hmaps n hn
      · intro y hy
        obtain ⟨_, n, hn, rfl⟩ := mem_powerCode_iff.mp hy
        exact (repl_spec _).mpr ⟨n, hn, rfl⟩
  -- Step 4: the code determines the subset.
  have hcodeinj : ∀ X ∈ ℘ lam, ∀ Y ∈ ℘ lam,
      powerCode p q s lam X = powerCode p q s lam Y → X = Y := by
    intro X hX Y hY he
    have hXsub : X ⊆ lam := mem_power_iff.mp hX
    have hYsub : Y ⊆ lam := mem_power_iff.mp hY
    have hslice : ∀ n ∈ (ω : V), X ∩ (s ‘ n) = Y ∩ (s ‘ n) := by
      intro n hn
      have hmem : codePoint p q s X n ∈ powerCode p q s lam Y := by
        rw [← he]
        exact mem_powerCode_iff.mpr ⟨hpt n hn X, n, hn, rfl⟩
      obtain ⟨_, m, hm, heq⟩ := mem_powerCode_iff.mp hmem
      have h1 : ⟨⟨n, (q ‘ n) ‘ (X ∩ (s ‘ n))⟩ₖ, codePoint p q s X n⟩ₖ ∈ p :=
        kpair_value_mem (hpdom ▸ hpair n hn X)
      have h2 : ⟨⟨m, (q ‘ m) ‘ (Y ∩ (s ‘ m))⟩ₖ, codePoint p q s X n⟩ₖ ∈ p := by
        rw [heq]
        exact kpair_value_mem (hpdom ▸ hpair m hm Y)
      have hpp := hpinj _ _ _ h1 h2
      obtain ⟨hnm, hval⟩ := kpair_iff.mp hpp
      subst hnm
      have hqn := hq n hn
      have : IsFunction (q ‘ n) := IsFunction.of_mem hqn.1
      have hdomq : domain (q ‘ n) = ℘ (s ‘ n) := domain_eq_of_mem_function hqn.1
      have hXd : X ∩ (s ‘ n) ∈ domain (q ‘ n) := by rw [hdomq]; exact hpiece X n
      have hYd : Y ∩ (s ‘ n) ∈ domain (q ‘ n) := by rw [hdomq]; exact hpiece Y n
      exact hqn.2 _ _ _ (kpair_value_mem hXd) (hval ▸ kpair_value_mem hYd)
    have key : ∀ U W : V, U ⊆ lam → (∀ n ∈ (ω : V), U ∩ (s ‘ n) = W ∩ (s ‘ n)) → U ⊆ W := by
      intro U W hU hUW ξ hξ
      have hsucc : succ ξ ∈ lam := initial_succ_mem hlam hωsub (hU ξ hξ)
      obtain ⟨i, hi, hsi⟩ := hscof.2 (succ ξ) hsucc
      have hmem : ξ ∈ U ∩ (s ‘ i) := mem_inter_iff.mpr ⟨hξ, hsi _ (mem_succ_self ξ)⟩
      rw [hUW i hi] at hmem
      exact (mem_inter_iff.mp hmem).1
    exact SetTheory.subset_antisymm (key X Y hXsub hslice)
      (key Y X hYsub fun n hn ↦ (hslice n hn).symm)
  -- Step 5: package the code map as an injection.
  exact cardLE_of_injective_map (powerCode p q s lam) inferInstance hcodemem hcodeinj

end ZFVP
