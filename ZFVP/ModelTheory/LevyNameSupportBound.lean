import ZFVP.ModelTheory.LevyDeterminedSubalgebra
import ZFVP.SetTheory.RegularUnions

/-! One ordinal `ξ < κ` below which every condition of a small set of nice names is determined.

`levy_regular_exists_determined_below` gives, for a single regular set `d` of `Coll(ω, <κ)`, an
ordinal `ξ < κ` with `IsLevyDeterminedBelow κ ξ d`. The lemmas of
`ZFVP/ModelTheory/LevyGaloisStep.lean` that feed the row permutations into the forced stabilizer
of a set `E` of nice names need one `ξ` that works simultaneously for every condition occurring
in `E`. That is what this file supplies: the conditions of `E` form a set of size below `κ`, a
selector picks one `ξ_d` for each of them, and regularity of `κ` bounds the selected ordinals by
a single `ξ < κ`; being determined below `ξ` is monotone in `ξ`, so that single bound works for
all of them.

The size bound needs the names of `E` to be small. `IsNiceName Q one K σ` only says that the
members of `σ` are pairs `⟨ǩ, p⟩` with `k ∈ K` and `p` a condition; it does not bound how many
conditions `σ` attaches to one code, and over the Boolean completion that number can be as large
as the completion itself. The extra hypothesis used here is `IsSingleValuedName`: at most one
condition per code, which is the shape of the names in Karagila-Schilhan Lemma 9.3. With it a
nice name over `K` has size at most `|K|`, and the union over `E` stays below `κ`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Images and unions of small sets -/

/-- With choice, the image of a set under a definable function is no larger than the set. -/
theorem repl_cardLE (hAC : InternalChoice V) (F : V → V) (hF : ℒₛₑₜ-function₁[V] F) (X : V) :
    repl F hF X ≤# X := by
  have hdom : domain (definableGraph X F hF) = X := domain_definableGraph X F hF
  have hran : range (definableGraph X F hF) = repl F hF X := range_definableGraph X F hF
  exact cardLE_of_surjective_function (wellOrderable_of_internalChoice hAC X)
    (function_mem_of_isFunction' hdom hran) hran

/-- Below a regular cardinal `δ`, the union of a set of size below `δ` whose members all have
size below `δ` has size below `δ`. -/
theorem sUnion_small_of_members_small (hAC : InternalChoice V) {δ ν E : V}
    (hreg : IsRegularCardinal δ) (hωδ : (ω : V) ∈ δ) (hν : ν ∈ δ) (hEν : E ≤# ν)
    (hmem : ∀ σ ∈ E, ∃ μ ∈ δ, σ ≤# μ) : ∃ μ ∈ δ, ⋃ˢ E ≤# μ := by
  have hid : ℒₛₑₜ-function₁[V] (fun x : V ↦ x) := by definability
  have hdom : domain (definableGraph E (fun x : V ↦ x) hid) = E := domain_definableGraph E _ hid
  have hran : range (definableGraph E (fun x : V ↦ x) hid) = E := by
    rw [range_definableGraph]
    apply mem_ext
    intro y
    rw [repl_spec]
    exact ⟨fun ⟨x, hx, hy⟩ ↦ hy ▸ hx, fun h ↦ ⟨y, h, rfl⟩⟩
  have hsmall : ∀ i ∈ E, ∃ μ ∈ δ, (definableGraph E (fun x : V ↦ x) hid) ‘ i ≤# μ := by
    intro i hi
    have hv : (definableGraph E (fun x : V ↦ x) hid) ‘ i = i := value_definableGraph E _ hid hi
    rw [hv]
    exact hmem i hi
  obtain ⟨μ, hμ, hle⟩ := sUnion_range_small_of_regular hAC hreg hωδ hdom hν hEν hsmall
  rw [hran] at hle
  exact ⟨μ, hμ, hle⟩

/-! ### The conditions occurring in a set of names -/

/-- The conditions occurring in a set of names are no more numerous than the pairs making up
those names. -/
theorem nameConditions_cardLE_sUnion (hAC : InternalChoice V) (E : V) :
    nameConditions E ≤# ⋃ˢ E := by
  unfold nameConditions
  exact repl_cardLE hAC _ _ _

/-- A name attaching at most one condition to each code. -/
def IsSingleValuedName (σ : V) : Prop :=
  ∀ ν d d' : V, (⟨ν, d⟩ₖ : V) ∈ σ → (⟨ν, d'⟩ₖ : V) ∈ σ → d = d'

/-- A nice name over `K` that attaches at most one condition to each code has size at most
`|K|`. -/
theorem niceName_cardLE (hAC : InternalChoice V) {Q one K σ : V}
    (hσ : IsNiceName Q one K σ) (hsv : IsSingleValuedName σ) : σ ≤# K := by
  have hchk : ℒₛₑₜ-function₁[V] (checkName one) := by definability
  refine (cardLE_of_injective_map (fun z ↦ kpair.π₁ z) (by definability)
    (B := repl (checkName one) hchk K) ?_ ?_).trans (repl_cardLE hAC (checkName one) hchk K)
  · intro z hz
    obtain ⟨k, hk, p, hp, rfl⟩ := hσ z hz
    rw [kpair.π₁_kpair]
    exact (repl_spec hchk).mpr ⟨k, hk, rfl⟩
  · intro z hz z' hz' heq
    obtain ⟨k, hk, p, hp, rfl⟩ := hσ z hz
    obtain ⟨k', hk', p', hp', rfl⟩ := hσ z' hz'
    rw [kpair.π₁_kpair, kpair.π₁_kpair] at heq
    have h2 : (⟨checkName one k, p'⟩ₖ : V) ∈ σ := by rw [heq]; exact hz'
    have hpp : p = p' := hsv (checkName one k) p p' hz h2
    rw [heq, hpp]

/-! ### Being determined below a larger ordinal -/

/-- Being determined below `ξ` is inherited by every larger ordinal. -/
theorem levy_determinedBelow_mono {κ ξ ξ' d : V} (h : ξ ⊆ ξ')
    (hd : IsLevyDeterminedBelow κ ξ d) : IsLevyDeterminedBelow κ ξ' d := by
  intro p hp
  have hcut : levyCut ξ' p ∈ levyCollapse κ := levyCollapse_subset hp (levyCut_subset ξ' p)
  rw [hd p hp, ← levyCut_levyCut_of_subset (p := p) h, ← hd _ hcut]

/-! ### The ordinals below which a set of conditions is determined -/

/-- The ordinals `ξ < κ` below which `d` is determined. -/
noncomputable def levyDeterminingOrdinals (κ d : V) : V :=
  sep κ (fun ξ ↦ IsLevyDeterminedBelow κ ξ d)
    (by unfold IsLevyDeterminedBelow levyCut; definability)

theorem mem_levyDeterminingOrdinals_iff (κ d ξ : V) :
    ξ ∈ levyDeterminingOrdinals κ d ↔ ξ ∈ κ ∧ IsLevyDeterminedBelow κ ξ d := mem_sep_iff

theorem levyDeterminingOrdinals_definable_one (κ : V) :
    ℒₛₑₜ-function₁[V] (levyDeterminingOrdinals κ) := by
  have h : ℒₛₑₜ-relation[V] (fun S d ↦ ∀ ξ, ξ ∈ S ↔ ξ ∈ κ ∧ IsLevyDeterminedBelow κ ξ d) := by
    unfold IsLevyDeterminedBelow levyCut
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = levyDeterminingOrdinals κ (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_levyDeterminingOrdinals_iff]

section

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)

include hAC hU hc hω hκ in
/-- The conditions of a small set of small names are small. -/
theorem levy_nameConditions_small_of_names_small {E ν : V} (hν : ν ∈ κ) (hEν : E ≤# ν)
    (hnames : ∀ σ ∈ E, ∃ μ ∈ κ, σ ≤# μ) : ∃ μ ∈ κ, nameConditions E ≤# μ := by
  have hreg := measurable_regular hκ (IsOrdinal.toIsTransitive.transitive _ hω) hU hc
  obtain ⟨μ, hμ, hle⟩ := sUnion_small_of_members_small hAC hreg hω hν hEν hnames
  exact ⟨μ, hμ, (nameConditions_cardLE_sUnion hAC E).trans hle⟩

include hAC hU hc hω hκ in
/-- The conditions occurring in a small set of single-valued nice names over a small set of codes
form a set of size below `κ`. -/
theorem levy_nameConditions_small {K E : V}
    (hE : ∀ σ ∈ E, IsNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
      (levyCollapse κ) K σ)
    (hsv : ∀ σ ∈ E, IsSingleValuedName σ)
    (hKsmall : ∃ μ ∈ κ, K ≤# μ) (hEsmall : ∃ ν ∈ κ, E ≤# ν) :
    ∃ μ ∈ κ, nameConditions E ≤# μ := by
  obtain ⟨ν, hν, hEν⟩ := hEsmall
  obtain ⟨μ₀, hμ₀, hKμ⟩ := hKsmall
  exact levy_nameConditions_small_of_names_small hAC hU hc hω hκ hν hEν
    (fun σ hσ ↦ ⟨μ₀, hμ₀, (niceName_cardLE hAC (hE σ hσ) (hsv σ hσ)).trans hKμ⟩)

include hAC hU hc hω hκ in
/-- A set of conditions of the Boolean completion of size below `κ` is determined below one
ordinal `ξ < κ`. -/
theorem levy_exists_determined_below_of_small {D μ : V}
    (hD : D ⊆ booleanConditions (levyCollapse κ) (levyOrder κ)) (hμ : μ ∈ κ) (hDμ : D ≤# μ) :
    ∃ ξ ∈ κ, ∀ d ∈ D, IsLevyDeterminedBelow κ ξ d := by
  have hreg := measurable_regular hκ (IsOrdinal.toIsTransitive.transitive _ hω) hU hc
  have hne : ∀ d ∈ D, IsNonempty (levyDeterminingOrdinals κ d) := by
    intro d hd
    obtain ⟨ξ, hξ, hdet⟩ := levy_regular_exists_determined_below hAC hU hc hω hκ
      (booleanConditions_regular (hD d hd))
    exact ⟨ξ, (mem_levyDeterminingOrdinals_iff κ d ξ).mpr ⟨hξ, hdet⟩⟩
  obtain ⟨f, hf, hdom, hval⟩ := choice_for_definable_family hAC D _
    (levyDeterminingOrdinals_definable_one κ) hne
  have := hf
  have hS : range f ⊆ κ := by
    intro ξ hξ
    obtain ⟨d, hdξ⟩ := mem_range_iff.mp hξ
    have hd : d ∈ D := hdom ▸ mem_domain_of_kpair_mem hdξ
    have hv := hval d hd
    rw [value_eq_of_kpair_mem hdξ] at hv
    exact ((mem_levyDeterminingOrdinals_iff _ _ _).mp hv).1
  have hSle : range f ≤# μ :=
    (cardLE_of_surjective_function (wellOrderable_of_internalChoice hAC D)
      (function_mem_of_isFunction' hdom rfl) rfl).trans hDμ
  obtain ⟨ξ, hξ, hsub⟩ := regular_small_subset_bounded hreg hS hμ hSle
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  refine ⟨ξ, hξ, fun d hd ↦ ?_⟩
  have hfd := (mem_levyDeterminingOrdinals_iff _ _ _).mp (hval d hd)
  have hmem : f ‘ d ∈ ξ := hsub _ (mem_range_of_kpair_mem (kpair_value_mem (hdom ▸ hd)))
  exact levy_determinedBelow_mono (IsOrdinal.toIsTransitive.transitive _ hmem) hfd.2

include hAC hU hc hω hκ in
/-- One ordinal `ξ < κ` below which every condition of every name of a small set of
single-valued nice names is determined. -/
theorem levy_exists_determined_below_nameConditions {K E : V}
    (hE : ∀ σ ∈ E, IsNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
      (levyCollapse κ) K σ)
    (hsv : ∀ σ ∈ E, IsSingleValuedName σ)
    (hKsmall : ∃ μ ∈ κ, K ≤# μ) (hEsmall : ∃ ν ∈ κ, E ≤# ν) :
    ∃ ξ ∈ κ, ∀ d ∈ nameConditions E, IsLevyDeterminedBelow κ ξ d := by
  obtain ⟨μ, hμ, hle⟩ := levy_nameConditions_small hAC hU hc hω hκ hE hsv hKsmall hEsmall
  exact levy_exists_determined_below_of_small hAC hU hc hω hκ (nameConditions_subset hE) hμ hle

include hAC hU hc hω hκ in
/-- The finite case used in the Solovay argument: finitely many single-valued nice names for
subsets of `ω × ω`. -/
theorem levy_exists_determined_below_finite_names {E : V} (hEfin : IsInternallyFinite E)
    (hE : ∀ σ ∈ E, IsNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
      (levyCollapse κ) ((ω : V) ×ˢ (ω : V)) σ)
    (hsv : ∀ σ ∈ E, IsSingleValuedName σ) :
    ∃ ξ ∈ κ, ∀ d ∈ nameConditions E, IsLevyDeterminedBelow κ ξ d := by
  obtain ⟨n, hn, hEn⟩ := hEfin
  have hprod : (ω : V) ×ˢ (ω : V) ≤# (ω : V) := by
    have h := ordinal_prod_cardLE_union_omega (V := V) (ω : V)
    rwa [ordinal_union_omega_eq (subset_refl (ω : V))] at h
  exact levy_exists_determined_below_nameConditions hAC hU hc hω hκ hE hsv ⟨(ω : V), hω, hprod⟩
    ⟨n, IsOrdinal.toIsTransitive.mem_trans hn hω, hEn.le⟩

include hAC hU hc hω hκ in
/-- The payoff: for finitely many single-valued nice names for subsets of `ω × ω` there is an
ordinal `ξ < κ` at which every row permutation lifts into the forced stabilizer of the names. -/
theorem levy_exists_rowPermutations_in_forcedStabilizer {E : V} (hEfin : IsInternallyFinite E)
    (hE : ∀ σ ∈ E, IsNiceName (booleanConditions (levyCollapse κ) (levyOrder κ))
      (levyCollapse κ) ((ω : V) ×ˢ (ω : V)) σ)
    (hsv : ∀ σ ∈ E, IsSingleValuedName σ) :
    ∃ ξ ∈ κ, ∀ s, IsInternalPermutation (ω : V) s →
      booleanLift (levyCollapse κ) (levyOrder κ) (levyPermutation κ ξ s) ∈
        forcedStabilizer (booleanConditions (levyCollapse κ) (levyOrder κ))
          (booleanOrder (levyCollapse κ) (levyOrder κ))
          (forcingAutomorphisms (booleanConditions (levyCollapse κ) (levyOrder κ))
            (booleanOrder (levyCollapse κ) (levyOrder κ))) E := by
  obtain ⟨ξ, hξ, hdet⟩ := levy_exists_determined_below_finite_names hAC hU hc hω hκ hEfin hE hsv
  exact ⟨ξ, hξ, fun s hs ↦ levy_booleanLift_mem_forcedStabilizer_of_determined hs hE hdet⟩

end

end ZFVP
