import ZFVP.SetTheory.TransfiniteIteration
import ZFVP.SetTheory.RegularUnions
import ZFVP.SetTheory.LeastOrdinalChoice
import ZFVP.SetTheory.LevyCollapseSmallSets
import ZFVP.SetTheory.FiniteCardinalArithmetic
import ZFVP.SetTheory.PulledWellOrder

/-! Laver's uniqueness lemma (Reitz, Lemma 6.2), first step: two transitive sets with the
`δ`-cover and `δ`-approximation properties over the same ordinals admit simultaneous covers: every
small set of ordinals is contained in a set of size at most `δ` lying in both. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `A` has size below `δ`. -/
def USmall (δ A : V) : Prop := ∃ μ ∈ δ, A ≤# μ

instance uSmall_definable (δ : V) : ℒₛₑₜ-predicate (USmall δ) := by
  unfold USmall
  definability

/-- `B` is covered by a member of `M` that `M` injects into an ordinal below `δ`. -/
def MSmall (M δ B : V) : Prop := ∃ μ ∈ δ, ∃ C ∈ M, B ⊆ C ∧ ∃ f ∈ M, f ∈ μ ^ C ∧ Injective f

instance mSmall_definable (M δ : V) : ℒₛₑₜ-predicate (MSmall M δ) := by
  unfold MSmall
  definability

/-- `B` is covered by a member of `M` that `M` injects into `δ`. -/
def MBounded (M δ B : V) : Prop := ∃ C ∈ M, B ⊆ C ∧ ∃ f ∈ M, f ∈ δ ^ C ∧ Injective f

instance mBounded_definable (M δ : V) : ℒₛₑₜ-predicate (MBounded M δ) := by
  unfold MBounded
  definability

theorem uSmall_of_mSmall {M δ B : V} (h : MSmall M δ B) : USmall δ B := by
  obtain ⟨μ, hμ, C, -, hBC, f, -, hf, hinj⟩ := h
  exact ⟨μ, hμ, (cardLE_of_subset hBC).trans ⟨f, hf, hinj⟩⟩

theorem mSmall_of_subset {M δ B B' : V} (h : MSmall M δ B) (hB' : B' ⊆ B) : MSmall M δ B' := by
  obtain ⟨μ, hμ, C, hC, hBC, f, hf, hfC, hinj⟩ := h
  exact ⟨μ, hμ, C, hC, fun x hx ↦ hBC x (hB' x hx), f, hf, hfC, hinj⟩

theorem uSmall_of_subset {δ B B' : V} (h : USmall δ B) (hB' : B' ⊆ B) : USmall δ B' := by
  obtain ⟨μ, hμ, hle⟩ := h
  exact ⟨μ, hμ, (cardLE_of_subset hB').trans hle⟩

/-- The `δ`-cover property of `M` for subsets of `θ`. -/
def HasSmallCover (M δ θ : V) : Prop :=
  ∀ A, A ⊆ θ → USmall δ A → ∃ B ∈ M, A ⊆ B ∧ B ⊆ θ ∧ MSmall M δ B

/-- The `δ`-approximation property of `M` for subsets of `θ`. -/
def HasApproximation (M δ θ : V) : Prop :=
  ∀ A, A ⊆ θ → (∀ B ∈ M, B ⊆ θ → MSmall M δ B → A ∩ B ∈ M) → A ∈ M

def InterClosed (M : V) : Prop := ∀ x ∈ M, ∀ y ∈ M, x ∩ y ∈ M

/-- The small subsets of `θ`. -/
noncomputable def smallSubsetsBelow (δ θ : V) : V := sep (℘ θ) (USmall δ) inferInstance

theorem mem_smallSubsetsBelow_iff (δ θ x : V) : x ∈ smallSubsetsBelow δ θ ↔ x ⊆ θ ∧ USmall δ x := by
  rw [smallSubsetsBelow, mem_sep_iff, mem_power_iff]

/-- The covers of `x` in `M`. -/
noncomputable def groundCoverSet (M δ θ x : V) : V := {B ∈ M ; x ⊆ B ∧ B ⊆ θ ∧ MSmall M δ B}

theorem groundCoverSet_definable_one (M δ θ : V) : ℒₛₑₜ-function₁[V] (groundCoverSet M δ θ) := by
  have h : ℒₛₑₜ-relation[V] (fun S x ↦ ∀ B, B ∈ S ↔ B ∈ M ∧ x ⊆ B ∧ B ⊆ θ ∧ MSmall M δ B) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = groundCoverSet M δ θ (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [groundCoverSet, mem_sep_iff]

theorem mem_groundCoverSet_iff (M δ θ x B : V) :
    B ∈ groundCoverSet M δ θ x ↔ B ∈ M ∧ x ⊆ B ∧ B ⊆ θ ∧ MSmall M δ B :=
  mem_sep_iff

/-- An infinite ordinal injects its successor. -/
theorem succ_cardLE_of_infinite (ν : V) [IsOrdinal ν] (hω : (ω : V) ⊆ ν) : succ ν ≤# ν := by
  classical
  let F : V → V := fun x ↦ if x ∈ (ω : V) then succ x else if x = ν then ∅ else x
  have hF : ℒₛₑₜ-function₁ F := by
    have h : ℒₛₑₜ-relation (fun y x : V ↦ (x ∈ (ω : V) ∧ y = succ x) ∨
        (x ∉ (ω : V) ∧ x = ν ∧ y = ∅) ∨ (x ∉ (ω : V) ∧ x ≠ ν ∧ y = x)) := by definability
    apply Language.Definable.of_iff h
    intro v
    change v 0 = F (v 1) ↔ _
    by_cases h1 : v 1 ∈ (ω : V)
    · simp [F, h1]
    · by_cases h2 : v 1 = ν
      · rw [h2] at h1
        simp [F, h1, h2]
      · simp [F, h1, h2]
  have hνω : ν ∉ (ω : V) := fun h ↦ mem_irrefl ν (hω ν h)
  have hFω : ∀ x ∈ (ω : V), F x = succ x := fun x hx ↦ by simp [F, hx]
  have hFν : F ν = ∅ := by simp [F, hνω]
  have hFid : ∀ x, x ∉ (ω : V) → x ≠ ν → F x = x := fun x h1 h2 ↦ by simp [F, h1, h2]
  apply cardLE_of_injective_map F hF
  · intro x hx
    by_cases h1 : x ∈ (ω : V)
    · rw [hFω x h1]
      exact hω _ (ω_succ_closed h1)
    · by_cases h2 : x = ν
      · rw [h2, hFν]
        exact hω _ empty_mem_ω
      · rw [hFid x h1 h2]
        rcases mem_succ_iff.mp hx with h | h
        · exact (h2 h).elim
        · exact h
  · intro x _ y _ hxy
    by_cases h1 : x ∈ (ω : V) <;> by_cases h3 : y ∈ (ω : V)
    · rw [hFω x h1, hFω y h3] at hxy
      haveI : IsOrdinal x := IsOrdinal.nat h1
      haveI : IsOrdinal y := IsOrdinal.nat h3
      exact succ_injective_ordinal hxy
    · by_cases h4 : y = ν
      · rw [hFω x h1, h4, hFν] at hxy
        exact (not_mem_empty (hxy ▸ mem_succ_self x)).elim
      · rw [hFω x h1, hFid y h3 h4] at hxy
        exact (h3 (hxy ▸ ω_succ_closed h1)).elim
    · by_cases h2 : x = ν
      · rw [h2, hFν, hFω y h3] at hxy
        exact (not_mem_empty (hxy ▸ mem_succ_self y)).elim
      · rw [hFid x h1 h2, hFω y h3] at hxy
        exact (h1 (hxy ▸ ω_succ_closed h3)).elim
    · by_cases h2 : x = ν <;> by_cases h4 : y = ν
      · rw [h2, h4]
      · rw [h2, hFν, hFid y h3 h4] at hxy
        exact (h3 (hxy ▸ empty_mem_ω)).elim
      · rw [hFid x h1 h2, h4, hFν] at hxy
        exact (h1 (hxy ▸ empty_mem_ω)).elim
      · rwa [hFid x h1 h2, hFid y h3 h4] at hxy

/-- Below an infinite initial ordinal, successors stay below. -/
theorem succ_mem_of_initial {δ ν : V} (hδ : IsInitialOrdinal δ) (hω : (ω : V) ⊆ δ) (hν : ν ∈ δ) :
    succ ν ∈ δ := by
  haveI hδo : IsOrdinal δ := hδ.1
  haveI hνo : IsOrdinal ν := IsOrdinal.of_mem hν
  rcases IsOrdinal.mem_trichotomy (succ ν) δ with h | h | h
  · exact h
  · exfalso
    have hων : (ω : V) ⊆ ν := by
      intro x hx
      have hxs : x ∈ succ ν := by rw [h]; exact hω x hx
      rcases mem_succ_iff.mp hxs with rfl | hxν
      · exact absurd (hω _ (by rw [← h]; exact ω_succ_closed hx)) (mem_irrefl δ)
      · exact hxν
    have hle := succ_cardLE_of_infinite ν hων
    rw [h] at hle
    exact hδ.2 ν hν hle
  · exfalso
    rcases mem_succ_iff.mp h with hδν | hδν
    · subst hδν
      exact mem_irrefl _ hν
    · exact mem_irrefl δ (IsTransitive.mem_trans IsOrdinal.toIsTransitive hδν hν)

section

variable (hAC : InternalChoice V) {δ θ : V} (hreg : IsRegularCardinal δ) (hωδ : (ω : V) ∈ δ)

/-- The stage at which `c` enters the iteration. -/
noncomputable def entryStage (it : V → V) (hit : ℒₛₑₜ-function₁ it) (δ c : V) : V :=
  leastOrdinalOrZero (fun c ξ ↦ ξ ∈ δ ∧ c ∈ it ξ) (by definability) c

theorem entryStage_definable (it : V → V) (hit : ℒₛₑₜ-function₁ it) (δ : V) :
    ℒₛₑₜ-function₁ (entryStage it hit δ) := by
  unfold entryStage
  infer_instance

include hAC hreg hωδ in
/-- Simultaneous covers: a small subset of `θ` lies in a set of size at most `δ` belonging to
both `M` and `M'`. -/
theorem simultaneous_cover {M M' : V} (hcov : HasSmallCover M δ θ) (hcov' : HasSmallCover M' δ θ)
    (happ : HasApproximation M δ θ) (happ' : HasApproximation M' δ θ)
    (hint : InterClosed M) (hint' : InterClosed M') {A : V} (hA : A ⊆ θ) (hsmall : USmall δ A) :
    ∃ B, B ∈ M ∧ B ∈ M' ∧ A ⊆ B ∧ B ⊆ θ ∧ B ≤# δ := by
  have hδo : IsOrdinal δ := hreg.1.1
  have hωsub : (ω : V) ⊆ δ := hreg.2.1
  -- choice functions for covers in `M'` and in `M`
  have hne' : ∀ x ∈ smallSubsetsBelow δ θ, IsNonempty (groundCoverSet M' δ θ x) := by
    intro x hx
    obtain ⟨hxθ, hxs⟩ := (mem_smallSubsetsBelow_iff δ θ x).mp hx
    obtain ⟨B, hB, hxB, hBθ, hBs⟩ := hcov' x hxθ hxs
    exact ⟨⟨B, (mem_groundCoverSet_iff _ _ _ _ _).mpr ⟨hB, hxB, hBθ, hBs⟩⟩⟩
  have hne : ∀ x ∈ smallSubsetsBelow δ θ, IsNonempty (groundCoverSet M δ θ x) := by
    intro x hx
    obtain ⟨hxθ, hxs⟩ := (mem_smallSubsetsBelow_iff δ θ x).mp hx
    obtain ⟨B, hB, hxB, hBθ, hBs⟩ := hcov x hxθ hxs
    exact ⟨⟨B, (mem_groundCoverSet_iff _ _ _ _ _).mpr ⟨hB, hxB, hBθ, hBs⟩⟩⟩
  obtain ⟨c', hc'f, hc'd, hc'val⟩ :=
    choice_for_definable_family hAC _ _ (groundCoverSet_definable_one M' δ θ) hne'
  obtain ⟨c, hcf, hcd, hcval⟩ :=
    choice_for_definable_family hAC _ _ (groundCoverSet_definable_one M δ θ) hne
  -- the step: cover in `M'`, then in `M`
  let F : V → V := fun x ↦ x ∪ (c ‘ (c' ‘ x))
  have hF : ℒₛₑₜ-function₁ F := by
    have h : ℒₛₑₜ-relation (fun y x : V ↦ y = x ∪ (c ‘ (c' ‘ x))) := by definability
    exact h
  have hincl : ∀ x, x ⊆ F x := fun x y hy ↦ mem_union_iff.mpr (Or.inl hy)
  have hstep : ∀ x ∈ smallSubsetsBelow δ θ,
      c' ‘ x ∈ M' ∧ x ⊆ c' ‘ x ∧ c' ‘ x ⊆ θ ∧ MSmall M' δ (c' ‘ x) ∧
      F x ∈ M ∧ c' ‘ x ⊆ F x ∧ F x ∈ smallSubsetsBelow δ θ := by
    intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := (mem_groundCoverSet_iff _ _ _ _ _).mp (hc'val x hx)
    have hx' : c' ‘ x ∈ smallSubsetsBelow δ θ :=
      (mem_smallSubsetsBelow_iff δ θ _).mpr ⟨h3, uSmall_of_mSmall h4⟩
    obtain ⟨h5, h6, h7, h8⟩ := (mem_groundCoverSet_iff _ _ _ _ _).mp (hcval _ hx')
    have hFx : F x = c ‘ (c' ‘ x) := by
      apply mem_ext
      intro y
      rw [mem_union_iff]
      exact ⟨fun h ↦ h.elim (fun h ↦ h6 y (h2 y h)) id, Or.inr⟩
    refine ⟨h1, h2, h3, h4, ?_, ?_, ?_⟩
    · rw [hFx]; exact h5
    · rw [hFx]; exact h6
    · rw [hFx]
      exact (mem_smallSubsetsBelow_iff δ θ _).mpr ⟨h7, uSmall_of_mSmall h8⟩
  -- the iteration
  let it : V → V := iterate F hF A
  have hit : ℒₛₑₜ-function₁ it := iterate_definable hF A
  have hit0 : it ∅ = A := iterate_zero hF A
  have hitS : ∀ ξ : V, IsOrdinal ξ → it (succ ξ) = F (it ξ) := by
    intro ξ hξ
    letI := hξ
    exact iterate_succ hF A ξ
  have hitL : ∀ lam : V, IsLimitOrdinal lam → it lam = ⋃ˢ range (definableGraph lam it hit) := by
    intro lam hlam
    rw [range_definableGraph]
    exact iterate_limit hF A lam hlam
  have hA' : A ∈ smallSubsetsBelow δ θ := (mem_smallSubsetsBelow_iff δ θ A).mpr ⟨hA, hsmall⟩
  have hmono : ∀ η : Ordinal V, ∀ ξ ∈ (η : V), it ξ ⊆ it η := iterate_mono hF hincl A
  -- all stages below `δ` are small
  have hstages : ∀ ξ : Ordinal V, (ξ : V) ∈ δ → it ξ ∈ smallSubsetsBelow δ θ := by
    apply transfinite_induction (fun ξ : V ↦ ξ ∈ δ → it ξ ∈ smallSubsetsBelow δ θ) (by definability)
    intro ξ ih hξ
    have hξo : IsOrdinal (ξ : V) := ξ.ordinal
    rcases ordinal_cases (ξ : V) with h0 | ⟨ζ, hζ, hζe⟩ | hlim
    · rw [h0, hit0]
      exact hA'
    · haveI hζo : IsOrdinal ζ := hζ
      have hζξ : (IsOrdinal.toOrdinal ζ : Ordinal V) < ξ := by
        refine Ordinal.lt_def.mpr ?_
        show ζ ∈ (ξ : V)
        rw [hζe]
        exact mem_succ_self ζ
      have hζδ : ζ ∈ δ :=
        IsTransitive.mem_trans IsOrdinal.toIsTransitive (by rw [hζe]; exact mem_succ_self ζ) hξ
      rw [hζe, hitS ζ hζo]
      exact (hstep _ (ih _ hζξ hζδ)).2.2.2.2.2.2
    · haveI hlimo : IsOrdinal (ξ : V) := hlim.1
      rw [mem_smallSubsetsBelow_iff]
      constructor
      · intro x hx
        obtain ⟨ζ, hζ, hxζ⟩ := (mem_iterate_limit_iff hF A _ hlim x).mp hx
        haveI hζo : IsOrdinal ζ := IsOrdinal.of_mem hζ
        have hζδ : ζ ∈ δ := IsTransitive.mem_trans IsOrdinal.toIsTransitive hζ hξ
        have := ih (IsOrdinal.toOrdinal ζ) (Ordinal.lt_def.mpr hζ) hζδ
        exact ((mem_smallSubsetsBelow_iff δ θ _).mp this).1 x hxζ
      · rw [hitL _ hlim]
        have hgd : domain (definableGraph (ξ : V) it hit) = ξ := domain_definableGraph _ _ _
        refine sUnion_range_small_of_regular hAC hreg hωδ hgd hξ (cardLE_of_subset (fun x hx ↦ hx)) ?_
        intro ζ hζ
        rw [value_definableGraph _ _ _ hζ]
        haveI hζo : IsOrdinal ζ := IsOrdinal.of_mem hζ
        have hζδ : ζ ∈ δ := IsTransitive.mem_trans IsOrdinal.toIsTransitive hζ hξ
        have := ih (IsOrdinal.toOrdinal ζ) (Ordinal.lt_def.mpr hζ) hζδ
        exact ((mem_smallSubsetsBelow_iff δ θ _).mp this).2
  have hstage : ∀ ξ ∈ δ, it ξ ∈ smallSubsetsBelow δ θ := by
    intro ξ hξ
    haveI : IsOrdinal ξ := IsOrdinal.of_mem hξ
    exact hstages (IsOrdinal.toOrdinal ξ) hξ
  -- the union of the stages
  let B : V := ⋃ˢ range (definableGraph δ it hit)
  have hgd : domain (definableGraph δ it hit) = δ := domain_definableGraph _ _ _
  have hmemB : ∀ x, x ∈ B ↔ ∃ ξ ∈ δ, x ∈ it ξ := by
    intro x
    rw [mem_sUnion_iff, range_definableGraph]
    constructor
    · rintro ⟨y, hy, hxy⟩
      obtain ⟨ξ, hξ, rfl⟩ := (repl_spec _).mp hy
      exact ⟨ξ, hξ, hxy⟩
    · rintro ⟨ξ, hξ, hx⟩
      exact ⟨it ξ, (repl_spec _).mpr ⟨ξ, hξ, rfl⟩, hx⟩
  have hBθ : B ⊆ θ := by
    intro x hx
    obtain ⟨ξ, hξ, hxξ⟩ := (hmemB x).mp hx
    exact ((mem_smallSubsetsBelow_iff δ θ _).mp (hstage ξ hξ)).1 x hxξ
  have hAB : A ⊆ B := fun x hx ↦ (hmemB x).mpr
    ⟨∅, IsTransitive.mem_trans IsOrdinal.toIsTransitive empty_mem_ω hωδ, by rw [hit0]; exact hx⟩
  have hBδ : B ≤# δ := by
    refine sUnion_range_cardLE_of_regular hAC hreg hgd (cardLE_of_subset (fun x hx ↦ hx)) ?_
    intro ξ hξ
    rw [value_definableGraph _ _ _ hξ]
    obtain ⟨μ, hμ, hle⟩ := ((mem_smallSubsetsBelow_iff δ θ _).mp (hstage ξ hξ)).2
    exact hle.trans (cardLE_of_subset (IsOrdinal.toIsTransitive.transitive μ hμ))
  -- a small subset of `B` lies in a bounded stage
  have hbounded : ∀ C, C ⊆ θ → USmall δ C → ∃ ν ∈ δ, C ∩ B ⊆ it ν := by
    intro C hCθ hCs
    let st : V → V := entryStage it hit δ
    have hst : ℒₛₑₜ-function₁ st := entryStage_definable it hit δ
    have hstspec : ∀ x ∈ C ∩ B, st x ∈ δ ∧ x ∈ it (st x) := by
      intro x hx
      obtain ⟨ξ, hξ, hxξ⟩ := (hmemB x).mp (mem_inter_iff.mp hx).2
      have := leastOrdinalOrZero_spec (fun c ξ ↦ ξ ∈ δ ∧ c ∈ it ξ) (by definability) x
        ⟨ξ, IsOrdinal.of_mem hξ, hξ, hxξ⟩
      exact this.2.1
    let S : V := repl st hst (C ∩ B)
    have hSδ : S ⊆ δ := by
      intro ν hν
      obtain ⟨x, hx, rfl⟩ := (repl_spec _).mp hν
      exact (hstspec x hx).1
    obtain ⟨μ, hμ, hCμ⟩ := uSmall_of_subset hCs (fun x hx ↦ (mem_inter_iff.mp hx).1)
    have hSle : S ≤# μ := by
      have hsurj : range (definableGraph (C ∩ B) st hst) = S := range_definableGraph _ _ _
      exact (cardLE_of_surjective_function (wellOrderable_of_internalChoice hAC _)
        (function_mem_of_isFunction' (domain_definableGraph _ _ _) hsurj) hsurj).trans hCμ
    obtain ⟨ν, hν, hSν⟩ := regular_small_subset_bounded hreg hSδ hμ hSle
    refine ⟨ν, hν, fun x hx ↦ ?_⟩
    have hxν : st x ∈ ν := hSν _ ((repl_spec _).mpr ⟨x, hx, rfl⟩)
    haveI : IsOrdinal ν := IsOrdinal.of_mem hν
    exact hmono (IsOrdinal.toOrdinal ν) (st x) hxν x (hstspec x hx).2
  have hsuccmem : ∀ ν ∈ δ, succ ν ∈ δ := fun ν hν ↦ succ_mem_of_initial hreg.1 hωsub hν
  have hstageB : ∀ ξ ∈ δ, it ξ ⊆ B := fun ξ hξ x hx ↦ (hmemB x).mpr ⟨ξ, hξ, hx⟩
  refine ⟨B, ?_, ?_, hAB, hBθ, hBδ⟩
  · -- `B ∈ M` by approximation
    refine happ B hBθ (fun C hC hCθ hCs ↦ ?_)
    obtain ⟨ν, hν, hCν⟩ := hbounded C hCθ (uSmall_of_mSmall hCs)
    haveI hνo : IsOrdinal ν := IsOrdinal.of_mem hν
    have hsucc := hstep _ (hstage ν hν)
    have heq : B ∩ C = it (succ ν) ∩ C := by
      apply mem_ext
      intro x
      rw [mem_inter_iff, mem_inter_iff]
      constructor
      · rintro ⟨hxB, hxC⟩
        refine ⟨?_, hxC⟩
        rw [hitS ν hνo]
        exact hincl _ x (hCν x (mem_inter_iff.mpr ⟨hxC, hxB⟩))
      · rintro ⟨hx, hxC⟩
        exact ⟨hstageB _ (hsuccmem ν hν) x hx, hxC⟩
    rw [heq]
    refine hint _ ?_ C hC
    rw [hitS ν hνo]
    exact hsucc.2.2.2.2.1
  · -- `B ∈ M'` by approximation, through the intermediate covers
    refine happ' B hBθ (fun C hC hCθ hCs ↦ ?_)
    obtain ⟨ν, hν, hCν⟩ := hbounded C hCθ (uSmall_of_mSmall hCs)
    haveI hνo : IsOrdinal ν := IsOrdinal.of_mem hν
    have hsucc := hstep _ (hstage ν hν)
    have heq : B ∩ C = (c' ‘ (it ν)) ∩ C := by
      apply mem_ext
      intro x
      rw [mem_inter_iff, mem_inter_iff]
      constructor
      · rintro ⟨hxB, hxC⟩
        exact ⟨hsucc.2.1 x (hCν x (mem_inter_iff.mpr ⟨hxC, hxB⟩)), hxC⟩
      · rintro ⟨hx, hxC⟩
        refine ⟨hstageB _ (hsuccmem ν hν) x ?_, hxC⟩
        rw [hitS ν hνo]
        exact hsucc.2.2.2.2.2.1 x hx
    rw [heq]
    exact hint' _ hsucc.1 C hC

end

end ZFVP
