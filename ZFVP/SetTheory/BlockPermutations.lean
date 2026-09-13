import ZFVP.SetTheory.CohenTranspositions
import ZFVP.SetTheory.NaturalArithmeticOrder
import ZFVP.SetTheory.FiniteNaturalSets

/-!
Permutations of the index set `ω ×ˢ ω` that permute the first coordinate (the block) and are
free on the second coordinate (the copy inside a block), together with the explicit permutation
used in Jech's first embedding theorem: the identity on a finite set of blocks, and a shift of
the copy indices everywhere else.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### A shift permutation of omega -/

/-- The graph condition for the involution of `ω` swapping `γ` with the next `γ` naturals. -/
def shiftStep (γ x y : V) : Prop :=
  (x ∈ γ ∧ y = ordinalAdd γ x) ∨ (x ∉ γ ∧ y ∈ γ ∧ ordinalAdd γ y = x) ∨
    (x ∉ ordinalAdd γ γ ∧ y = x)

instance shiftStep_definable : ℒₛₑₜ-relation₃[V] shiftStep := by
  unfold shiftStep
  definability

/-- The value of the involution of `ω` that swaps `ξ` and `γ + ξ` for `ξ ∈ γ`. -/
noncomputable def shiftValue (γ x : V) : V := ⋃ˢ {y ∈ (ω : V) ; shiftStep γ x y}

theorem shiftValue_right_definable (γ : V) : ℒₛₑₜ-function₁[V] (shiftValue γ) := by
  have h : ℒₛₑₜ-relation[V] (fun u x ↦ ∀ z, z ∈ u ↔
      ∃ y, (y ∈ (ω : V) ∧ shiftStep γ x y) ∧ z ∈ y) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = shiftValue γ (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [shiftValue, mem_sUnion_iff, mem_sep_iff]

instance shiftValue_definable : ℒₛₑₜ-function₂[V] shiftValue := by
  have h : ℒₛₑₜ-relation₃[V] (fun u γ x ↦ ∀ z, z ∈ u ↔
      ∃ y, (y ∈ (ω : V) ∧ shiftStep γ x y) ∧ z ∈ y) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = shiftValue (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [shiftValue, mem_sUnion_iff, mem_sep_iff]

theorem shiftValue_eq {γ x y : V} (hy : y ∈ (ω : V)) (h : shiftStep γ x y)
    (hu : ∀ z ∈ (ω : V), shiftStep γ x z → z = y) : shiftValue γ x = y := by
  have he : {z ∈ (ω : V) ; shiftStep γ x z} = ({y} : V) := by
    apply mem_ext
    intro z
    simp only [mem_sep_iff, mem_singleton_iff]
    exact ⟨fun hz ↦ hu z hz.1 hz.2, fun hz ↦ hz ▸ ⟨hy, h⟩⟩
  unfold shiftValue
  rw [he, sUnion_singleton_eq]

theorem shiftValue_of_mem {γ x : V} (hγ : γ ∈ (ω : V)) (hx : x ∈ (ω : V)) (hxγ : x ∈ γ) :
    shiftValue γ x = ordinalAdd γ x := by
  have : IsOrdinal γ := IsOrdinal.of_mem hγ
  have : IsOrdinal x := IsOrdinal.of_mem hx
  apply shiftValue_eq (ordinalAdd_natural hγ hx) (Or.inl ⟨hxγ, rfl⟩)
  intro z _ hz
  rcases hz with ⟨_, rfl⟩ | ⟨hnx, _, _⟩ | ⟨hnl, rfl⟩
  · rfl
  · exact absurd hxγ hnx
  · exact absurd (subset_ordinalAdd γ γ _ hxγ) hnl

theorem shiftValue_add {γ c : V} (hγ : γ ∈ (ω : V)) (hc : c ∈ (ω : V)) (hcγ : c ∈ γ) :
    shiftValue γ (ordinalAdd γ c) = c := by
  have : IsOrdinal γ := IsOrdinal.of_mem hγ
  have : IsOrdinal c := IsOrdinal.of_mem hc
  have hnot : ordinalAdd γ c ∉ γ := fun h ↦ mem_irrefl _ (subset_ordinalAdd γ c _ h)
  apply shiftValue_eq hc (Or.inr (Or.inl ⟨hnot, hcγ, rfl⟩))
  intro z hz hs
  have : IsOrdinal z := IsOrdinal.of_mem hz
  rcases hs with ⟨h1, _⟩ | ⟨_, _, he⟩ | ⟨hnl, rfl⟩
  · exact absurd h1 hnot
  · exact ordinalAdd_right_injective he
  · exact absurd (ordinalAdd_mem hcγ) hnl

theorem shiftValue_of_large {γ x : V} (hγ : γ ∈ (ω : V)) (hx : x ∈ (ω : V))
    (hxl : x ∉ ordinalAdd γ γ) : shiftValue γ x = x := by
  have : IsOrdinal γ := IsOrdinal.of_mem hγ
  apply shiftValue_eq hx (Or.inr (Or.inr ⟨hxl, rfl⟩))
  intro z hz hs
  have : IsOrdinal z := IsOrdinal.of_mem hz
  rcases hs with ⟨h1, rfl⟩ | ⟨_, hzγ, he⟩ | ⟨_, rfl⟩
  · exact absurd (subset_ordinalAdd γ γ _ h1) hxl
  · exact absurd (he ▸ ordinalAdd_mem hzγ) hxl
  · rfl

/-- The three shapes the shift can take at a natural number. -/
theorem shiftValue_cases {γ x : V} (hγ : γ ∈ (ω : V)) (hx : x ∈ (ω : V)) :
    (x ∈ γ ∧ shiftValue γ x = ordinalAdd γ x) ∨
      (∃ c, c ∈ (ω : V) ∧ c ∈ γ ∧ x = ordinalAdd γ c ∧ shiftValue γ x = c) ∨
      (x ∉ ordinalAdd γ γ ∧ shiftValue γ x = x) := by
  classical
  have hoγ : IsOrdinal γ := IsOrdinal.of_mem hγ
  have hox : IsOrdinal x := IsOrdinal.of_mem hx
  by_cases hxγ : x ∈ γ
  · exact Or.inl ⟨hxγ, shiftValue_of_mem hγ hx hxγ⟩
  by_cases hxl : x ∈ ordinalAdd γ γ
  · have hsub : γ ⊆ x := by
      rcases IsOrdinal.mem_trichotomy (α := x) (β := γ) with h | h | h
      · exact absurd h hxγ
      · exact h ▸ subset_refl _
      · exact IsOrdinal.toIsTransitive.transitive _ h
    obtain ⟨c, hc, he⟩ := ordinalAdd_difference_natural hγ hx hsub
    have hoc : IsOrdinal c := IsOrdinal.of_mem hc
    have hcγ : c ∈ γ := by
      by_contra hcn
      have hgc : γ ⊆ c := by
        rcases IsOrdinal.mem_trichotomy (α := c) (β := γ) with h | h | h
        · exact absurd h hcn
        · exact h ▸ subset_refl _
        · exact IsOrdinal.toIsTransitive.transitive _ h
      have : ordinalAdd γ γ ⊆ x := he ▸ ordinalAdd_mono_right γ hgc
      exact mem_irrefl _ (this _ hxl)
    exact Or.inr (Or.inl ⟨c, hc, hcγ, he.symm, he ▸ shiftValue_add hγ hc hcγ⟩)
  · exact Or.inr (Or.inr ⟨hxl, shiftValue_of_large hγ hx hxl⟩)

theorem shiftValue_mem {γ x : V} (hγ : γ ∈ (ω : V)) (hx : x ∈ (ω : V)) :
    shiftValue γ x ∈ (ω : V) := by
  rcases shiftValue_cases hγ hx with ⟨_, he⟩ | ⟨c, hc, _, _, he⟩ | ⟨_, he⟩
  · rw [he]; exact ordinalAdd_natural hγ hx
  · rw [he]; exact hc
  · rw [he]; exact hx

theorem shiftValue_involutive {γ x : V} (hγ : γ ∈ (ω : V)) (hx : x ∈ (ω : V)) :
    shiftValue γ (shiftValue γ x) = x := by
  rcases shiftValue_cases hγ hx with ⟨h1, he⟩ | ⟨c, hc, hcγ, hxc, he⟩ | ⟨_, he⟩
  · rw [he, shiftValue_add hγ hx h1]
  · rw [he, shiftValue_of_mem hγ hc hcγ, ← hxc]
  · rw [he, he]

/-- The involution of `ω` that swaps `ξ` and `γ + ξ` for `ξ ∈ γ`. -/
noncomputable def omegaShift (γ : V) : V :=
  definableGraph (ω : V) (shiftValue γ) (shiftValue_right_definable γ)

theorem omegaShift_value {γ x : V} (hx : x ∈ (ω : V)) :
    (omegaShift γ) ‘ x = shiftValue γ x := value_definableGraph _ _ _ hx

theorem omegaShift_permutation {γ : V} (hγ : γ ∈ (ω : V)) :
    IsInternalPermutation (ω : V) (omegaShift γ) := by
  have hf : omegaShift γ ∈ (ω : V) ^ (ω : V) :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ hx ↦ shiftValue_mem hγ hx)
  have : IsFunction (omegaShift γ) := IsFunction.of_mem hf
  refine ⟨hf, ?_, ?_⟩
  · intro x y z hx hy
    have hxω := (mem_of_mem_functions hf hx).1
    have hyω := (mem_of_mem_functions hf hy).1
    have he := (value_eq_of_kpair_mem hx).trans (value_eq_of_kpair_mem hy).symm
    rw [omegaShift_value hxω, omegaShift_value hyω] at he
    have hh := congrArg (shiftValue γ) he
    rwa [shiftValue_involutive hγ hxω, shiftValue_involutive hγ hyω] at hh
  · apply SetTheory.subset_antisymm (range_subset_of_mem_function hf)
    intro x hx
    have hm := shiftValue_mem hγ hx
    have he : (omegaShift γ) ‘ (shiftValue γ x) = x := by
      rw [omegaShift_value hm, shiftValue_involutive hγ hx]
    exact he ▸ value_mem_range hf hm

/-- A finite set of naturals can be moved off itself by a permutation of `ω`. -/
theorem exists_omega_shift {F : V} (hF : F ⊆ (ω : V)) (hFfin : IsInternallyFinite F) :
    ∃ s, IsInternalPermutation (ω : V) s ∧ ∀ ξ ∈ F, s ‘ ξ ∉ F := by
  obtain ⟨γ, hγ, hFγ⟩ := internallyFinite_naturals_bounded hFfin hF
  refine ⟨omegaShift γ, omegaShift_permutation hγ, ?_⟩
  intro ξ hξ
  have hξω : ξ ∈ (ω : V) := hF ξ hξ
  have : IsOrdinal ξ := IsOrdinal.of_mem hξω
  rw [omegaShift_value hξω, shiftValue_of_mem hγ hξω (hFγ ξ hξ)]
  intro hmem
  exact mem_irrefl _ (subset_ordinalAdd γ ξ _ (hFγ _ hmem))

/-! ### Block permutations of `ω ×ˢ ω` -/

/-- `π` permutes `ω ×ˢ ω` by permuting the blocks according to `ρ`. -/
def IsBlockPermutation (π ρ : V) : Prop :=
  IsInternalPermutation ((ω : V) ×ˢ (ω : V)) π ∧ IsInternalPermutation (ω : V) ρ ∧
    ∀ a ∈ (ω : V), ∀ ξ ∈ (ω : V), ∃ η ∈ (ω : V), π ‘ ⟨a, ξ⟩ₖ = ⟨ρ ‘ a, η⟩ₖ

instance isBlockPermutation_definable : ℒₛₑₜ-relation[V] IsBlockPermutation := by
  unfold IsBlockPermutation
  definability

theorem isBlockPermutation_identity :
    IsBlockPermutation (identity ((ω : V) ×ˢ (ω : V))) (identity (ω : V)) := by
  refine ⟨internalPermutation_identity _, internalPermutation_identity _, ?_⟩
  intro a ha ξ hξ
  refine ⟨ξ, hξ, ?_⟩
  rw [identity_value (kpair_mem_iff.mpr ⟨ha, hξ⟩), identity_value ha]

theorem IsBlockPermutation.comp {π ρ σ τ : V} (h₁ : IsBlockPermutation π ρ)
    (h₂ : IsBlockPermutation σ τ) : IsBlockPermutation (compose π σ) (compose ρ τ) := by
  refine ⟨h₁.1.comp h₂.1, h₁.2.1.comp h₂.2.1, ?_⟩
  intro a ha ξ hξ
  obtain ⟨η, hη, he⟩ := h₁.2.2 a ha ξ hξ
  obtain ⟨θ, hθ, he'⟩ := h₂.2.2 (ρ ‘ a) (function_value_mem h₁.2.1.1 ha) η hη
  refine ⟨θ, hθ, ?_⟩
  rw [value_compose_of_mem_function h₁.1.1 h₂.1.1 (kpair_mem_iff.mpr ⟨ha, hξ⟩), he, he',
    value_compose_of_mem_function h₁.2.1.1 h₂.2.1.1 ha]

theorem IsBlockPermutation.inv {π ρ : V} (h : IsBlockPermutation π ρ) :
    IsBlockPermutation (converseGraph π) (converseGraph ρ) := by
  refine ⟨h.1.inv, h.2.1.inv, ?_⟩
  intro a ha ξ hξ
  have haξ : ⟨a, ξ⟩ₖ ∈ (ω : V) ×ˢ (ω : V) := kpair_mem_iff.mpr ⟨ha, hξ⟩
  have hv : (converseGraph π) ‘ ⟨a, ξ⟩ₖ ∈ (ω : V) ×ˢ (ω : V) :=
    function_value_mem h.1.inv.1 haξ
  obtain ⟨b, hb, η, hη, hbη⟩ := mem_prod_iff.mp hv
  obtain ⟨θ, hθ, hval⟩ := h.2.2 b hb η hη
  have hback : π ‘ ((converseGraph π) ‘ ⟨a, ξ⟩ₖ) = ⟨a, ξ⟩ₖ := h.1.value_inv haξ
  rw [hbη, hval] at hback
  have hρb : ρ ‘ b = a := (kpair_iff.mp hback).1
  refine ⟨η, hη, ?_⟩
  rw [hbη, ← hρb, h.2.1.inv_value hb]

/-! ### The explicit block permutation -/

/-- The value of the permutation that fixes the blocks in `E` and applies `ρ` to the block and
`s` to the copy index elsewhere. -/
noncomputable def blockShiftValue (E ρ s z : V) : V := by
  classical
  exact if kpair.π₁ z ∈ E then z else ⟨ρ ‘ (kpair.π₁ z), s ‘ (kpair.π₂ z)⟩ₖ

theorem blockShiftValue_of_mem {E ρ s z : V} (h : kpair.π₁ z ∈ E) :
    blockShiftValue E ρ s z = z := by
  classical
  simp only [blockShiftValue, h, if_true, reduceIte]

theorem blockShiftValue_of_not_mem {E ρ s z : V} (h : kpair.π₁ z ∉ E) :
    blockShiftValue E ρ s z = ⟨ρ ‘ (kpair.π₁ z), s ‘ (kpair.π₂ z)⟩ₖ := by
  classical
  simp only [blockShiftValue, h, if_false, reduceIte]

theorem blockShiftValue_right_definable (E ρ s : V) :
    ℒₛₑₜ-function₁[V] (blockShiftValue E ρ s) := by
  have h : ℒₛₑₜ-relation[V] (fun y z ↦ (kpair.π₁ z ∈ E ∧ y = z) ∨
      (kpair.π₁ z ∉ E ∧ y = ⟨ρ ‘ (kpair.π₁ z), s ‘ (kpair.π₂ z)⟩ₖ)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = blockShiftValue E ρ s (v 1) ↔ _
  unfold blockShiftValue
  split_ifs <;> simp_all

instance blockShiftValue_definable : ℒₛₑₜ-function₄[V] blockShiftValue := by
  have h : ℒₛₑₜ-relation₅[V] (fun y E ρ s z ↦ (kpair.π₁ z ∈ E ∧ y = z) ∨
      (kpair.π₁ z ∉ E ∧ y = ⟨ρ ‘ (kpair.π₁ z), s ‘ (kpair.π₂ z)⟩ₖ)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = blockShiftValue (v 1) (v 2) (v 3) (v 4) ↔ _
  unfold blockShiftValue
  split_ifs <;> simp_all

/-- The permutation of `ω ×ˢ ω` that is the identity on the blocks in `E` and acts by `ρ` on the
block and `s` on the copy index outside `E`. -/
noncomputable def blockShift (E ρ s : V) : V :=
  definableGraph ((ω : V) ×ˢ (ω : V)) (blockShiftValue E ρ s)
    (blockShiftValue_right_definable E ρ s)

theorem blockShift_value_mem {E ρ s a ξ : V} (ha : a ∈ E) (haω : a ∈ (ω : V))
    (hξ : ξ ∈ (ω : V)) : (blockShift E ρ s) ‘ ⟨a, ξ⟩ₖ = ⟨a, ξ⟩ₖ := by
  rw [show blockShift E ρ s
      = definableGraph ((ω : V) ×ˢ (ω : V)) (blockShiftValue E ρ s) _ from rfl,
    value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨haω, hξ⟩)]
  exact blockShiftValue_of_mem (by simpa only [kpair.π₁_kpair] using ha)

theorem blockShift_value_not_mem {E ρ s a ξ : V} (ha : a ∉ E) (haω : a ∈ (ω : V))
    (hξ : ξ ∈ (ω : V)) : (blockShift E ρ s) ‘ ⟨a, ξ⟩ₖ = ⟨ρ ‘ a, s ‘ ξ⟩ₖ := by
  rw [show blockShift E ρ s
      = definableGraph ((ω : V) ×ˢ (ω : V)) (blockShiftValue E ρ s) _ from rfl,
    value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨haω, hξ⟩),
    blockShiftValue_of_not_mem (by simpa only [kpair.π₁_kpair] using ha)]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]

theorem blockShift_value_mem_prod {E ρ s : V} (hρ : IsInternalPermutation (ω : V) ρ)
    (hs : IsInternalPermutation (ω : V) s) {z : V} (hz : z ∈ (ω : V) ×ˢ (ω : V)) :
    blockShiftValue E ρ s z ∈ (ω : V) ×ˢ (ω : V) := by
  classical
  obtain ⟨a, ha, ξ, hξ, rfl⟩ := mem_prod_iff.mp hz
  by_cases hE : a ∈ E
  · rw [blockShiftValue_of_mem (by simpa only [kpair.π₁_kpair] using hE)]
    exact hz
  · rw [blockShiftValue_of_not_mem (by simpa only [kpair.π₁_kpair] using hE)]
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact kpair_mem_iff.mpr ⟨function_value_mem hρ.1 ha, function_value_mem hs.1 hξ⟩

theorem blockShift_isBlockPermutation {E ρ s : V} (hE : E ⊆ (ω : V))
    (hρ : IsInternalPermutation (ω : V) ρ) (hρfix : ∀ a ∈ E, ρ ‘ a = a)
    (hρout : ∀ a ∈ (ω : V), a ∉ E → ρ ‘ a ∉ E) (hs : IsInternalPermutation (ω : V) s) :
    IsBlockPermutation (blockShift E ρ s) ρ := by
  classical
  have hf : blockShift E ρ s ∈ ((ω : V) ×ˢ (ω : V)) ^ ((ω : V) ×ˢ (ω : V)) :=
    definableGraph_mem_function_of_mapsTo _ _ _ _
      (fun _ hz ↦ blockShift_value_mem_prod hρ hs hz)
  have hfun : IsFunction (blockShift E ρ s) := IsFunction.of_mem hf
  have hperm : IsInternalPermutation ((ω : V) ×ˢ (ω : V)) (blockShift E ρ s) := by
    refine ⟨hf, ?_, ?_⟩
    · intro x y z hx hy
      obtain ⟨a, ha, ξ, hξ, rfl⟩ := mem_prod_iff.mp (mem_of_mem_functions hf hx).1
      obtain ⟨b, hb, ζ, hζ, rfl⟩ := mem_prod_iff.mp (mem_of_mem_functions hf hy).1
      have he := (value_eq_of_kpair_mem hx).trans (value_eq_of_kpair_mem hy).symm
      by_cases haE : a ∈ E <;> by_cases hbE : b ∈ E
      · rw [blockShift_value_mem haE ha hξ, blockShift_value_mem hbE hb hζ] at he
        exact he
      · rw [blockShift_value_mem haE ha hξ, blockShift_value_not_mem hbE hb hζ] at he
        exact absurd ((kpair_iff.mp he).1 ▸ haE) (hρout b hb hbE)
      · rw [blockShift_value_not_mem haE ha hξ, blockShift_value_mem hbE hb hζ] at he
        exact absurd ((kpair_iff.mp he).1 ▸ hbE) (hρout a ha haE)
      · rw [blockShift_value_not_mem haE ha hξ, blockShift_value_not_mem hbE hb hζ] at he
        obtain ⟨h1, h2⟩ := kpair_iff.mp he
        rw [injective_value_eq hρ.1 hρ.2.1 ha hb h1, injective_value_eq hs.1 hs.2.1 hξ hζ h2]
    · apply SetTheory.subset_antisymm (range_subset_of_mem_function hf)
      intro z hz
      obtain ⟨a, ha, ξ, hξ, rfl⟩ := mem_prod_iff.mp hz
      by_cases haE : a ∈ E
      · exact (blockShift_value_mem haE ha hξ) ▸ value_mem_range hf hz
      · obtain ⟨b, hb, hba⟩ := hρ.surjective ha
        obtain ⟨ζ, hζ, hζξ⟩ := hs.surjective hξ
        have hbE : b ∉ E := by
          intro hbin
          apply haE
          rw [← hba, hρfix b hbin]
          exact hbin
        have he : (blockShift E ρ s) ‘ ⟨b, ζ⟩ₖ = ⟨a, ξ⟩ₖ := by
          rw [blockShift_value_not_mem hbE hb hζ, hba, hζξ]
        exact he ▸ value_mem_range hf (kpair_mem_iff.mpr ⟨hb, hζ⟩)
  refine ⟨hperm, hρ, ?_⟩
  intro a ha ξ hξ
  by_cases haE : a ∈ E
  · exact ⟨ξ, hξ, by rw [blockShift_value_mem haE ha hξ, hρfix a haE]⟩
  · exact ⟨s ‘ ξ, function_value_mem hs.1 hξ, blockShift_value_not_mem haE ha hξ⟩

/-! ### The two forcing facts -/

/-- The copy indices used by a Cohen condition over `ω ×ˢ ω`. -/
noncomputable def blockCopyIndices (p : V) : V := range (cohenSupport p)

instance blockCopyIndices_definable : ℒₛₑₜ-function₁[V] blockCopyIndices := by
  unfold blockCopyIndices
  definability

theorem mem_blockCopyIndices (p ξ : V) :
    ξ ∈ blockCopyIndices p ↔ ∃ a, ⟨a, ξ⟩ₖ ∈ cohenSupport p := by
  simp only [blockCopyIndices, mem_range_iff]

theorem blockCopyIndices_finite {p : V} (hp : p ∈ cohenConditions ((ω : V) ×ˢ (ω : V))) :
    IsInternallyFinite (blockCopyIndices p) :=
  internallyFinite_range (cohenSupport_finite hp)

theorem blockCopyIndices_subset {p : V} (hp : p ∈ cohenConditions ((ω : V) ×ˢ (ω : V))) :
    blockCopyIndices p ⊆ (ω : V) := by
  intro ξ hξ
  obtain ⟨a, ha⟩ := (mem_blockCopyIndices p ξ).mp hξ
  exact (kpair_mem_iff.mp (cohenSupport_subset hp _ ha)).2

theorem blockShift_fixes_condition {E ρ s q : V}
    (hq : q ∈ cohenConditions ((ω : V) ×ˢ (ω : V)))
    (hsupp : ∀ z ∈ cohenSupport q, kpair.π₁ z ∈ E) :
    cohenConditionAction ((ω : V) ×ˢ (ω : V)) (blockShift E ρ s) q = q := by
  apply cohenConditionAction_fix hq
  intro z hz
  obtain ⟨a, ha, ξ, hξ, rfl⟩ := mem_prod_iff.mp (cohenSupport_subset hq _ hz)
  have haE : a ∈ E := by simpa only [kpair.π₁_kpair] using hsupp _ hz
  exact blockShift_value_mem haE ha hξ

theorem blockShift_compatible {E ρ s p : V}
    (hp : p ∈ cohenConditions ((ω : V) ×ˢ (ω : V)))
    (hfresh : ∀ ξ ∈ blockCopyIndices p, s ‘ ξ ∉ blockCopyIndices p)
    (hE : E ⊆ (ω : V)) (hρ : IsInternalPermutation (ω : V) ρ) (hρfix : ∀ a ∈ E, ρ ‘ a = a)
    (hρout : ∀ a ∈ (ω : V), a ∉ E → ρ ‘ a ∉ E) (hs : IsInternalPermutation (ω : V) s) :
    ForcingCompatible (cohenConditions ((ω : V) ×ˢ (ω : V)))
      (cohenOrder ((ω : V) ×ˢ (ω : V))) p
      (cohenConditionAction ((ω : V) ×ˢ (ω : V)) (blockShift E ρ s) p) := by
  classical
  have hπ := (blockShift_isBlockPermutation hE hρ hρfix hρout hs).1
  have hq := cohenConditionAction_condition hπ hp
  have : IsFunction p := ((mem_finitePartialFunctions _ _ _).mp hp).2.1
  apply (finitePartialFunctions_compatible_iff hp hq).mpr
  intro x y z hxy hxz
  obtain ⟨k, hk, n, hn, rfl⟩ :=
    mem_prod_iff.mp (finitePartialFunction_domain hp _ (mem_domain_of_kpair_mem hxy))
  obtain ⟨l, hlz, hkl⟩ := (cohenConditionAction_pair_iff hp).mp hxz
  have hlsupp : l ∈ cohenSupport p := (mem_cohenSupport p l).mpr ⟨n, z, hlz⟩
  have hksupp : k ∈ cohenSupport p := (mem_cohenSupport p k).mpr ⟨n, y, hxy⟩
  obtain ⟨b, hb, ζ, hζ, rfl⟩ := mem_prod_iff.mp (cohenSupport_subset hp _ hlsupp)
  by_cases hbE : b ∈ E
  · rw [blockShift_value_mem hbE hb hζ] at hkl
    subst hkl
    exact IsFunction.unique hxy hlz
  · rw [blockShift_value_not_mem hbE hb hζ] at hkl
    have hζmem : ζ ∈ blockCopyIndices p := (mem_blockCopyIndices p ζ).mpr ⟨b, hlsupp⟩
    have hin : s ‘ ζ ∈ blockCopyIndices p :=
      (mem_blockCopyIndices p _).mpr ⟨ρ ‘ b, hkl ▸ hksupp⟩
    exact absurd hin (hfresh ζ hζmem)

end ZFVP
