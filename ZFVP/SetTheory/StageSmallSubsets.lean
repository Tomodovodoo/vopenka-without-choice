import ZFVP.SetTheory.GroundUniqueness
import ZFVP.SetTheory.CodingUniverse
import ZFVP.SetTheory.WellOrderedSurjection

/-! A rank stage at a regular cardinal absorbs the subsets of itself that are small. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The set of ranks of the members of `w`. -/
noncomputable def rankImage (w : V) : V := repl rank rank_definable w

theorem mem_rankImage_iff (w ζ : V) : ζ ∈ rankImage w ↔ ∃ x ∈ w, ζ = rank x :=
  repl_spec _

/-- If `w` injects into `μ` then the ranks of the members of `w` also inject into `μ`. The
injection of `w` well orders `w`, so no choice is used. -/
theorem rankImage_cardLE {w μ : V} [IsOrdinal μ] (hcard : w ≤# μ) : rankImage w ≤# μ := by
  obtain ⟨e, he, hinj⟩ := hcard
  have hde : domain e = w := domain_eq_of_mem_function he
  have : IsFunction e := IsFunction.of_mem he
  refine cardLE_of_separating_relation (ordinal_wellOrderable μ)
    (fun ζ y ↦ ∃ x, ⟨x, y⟩ₖ ∈ e ∧ rank x = ζ) (by definability) ?_ ?_
  · intro ζ hζ
    obtain ⟨x, hx, rfl⟩ := (mem_rankImage_iff w ζ).mp hζ
    exact ⟨e ‘ x, function_value_mem he hx, x, kpair_value_mem (by rw [hde]; exact hx), rfl⟩
  · rintro ζ _ ζ' _ y _ ⟨x, hxe, rfl⟩ ⟨x', hx'e, rfl⟩
    rw [hinj x x' y hxe hx'e]

/-- A subset of a rank stage at a regular `θ` whose size is bounded below `θ` is a member of
the stage. -/
theorem subset_mem_hierarchy_of_cardLE {θ w μ : V} (hθ : IsRegularCardinal θ) (hμ : μ ∈ θ)
    (hw : w ⊆ hierarchy θ) (hcard : w ≤# μ) : w ∈ hierarchy θ := by
  have hθord : IsOrdinal θ := hθ.1.1
  have hμord : IsOrdinal μ := IsOrdinal.of_mem hμ
  have hSsub : rankImage w ⊆ θ := by
    intro ζ hζ
    obtain ⟨x, hx, rfl⟩ := (mem_rankImage_iff w ζ).mp hζ
    exact (mem_hierarchy_iff_rank_mem x θ).mp (hw x hx)
  obtain ⟨ξ, hξ, hSξ⟩ :=
    regular_small_subset_bounded hθ hSsub hμ (rankImage_cardLE hcard)
  have hξord : IsOrdinal ξ := IsOrdinal.of_mem hξ
  refine (mem_hierarchy_iff_of_ordinal θ w).mpr ⟨ξ, hξ, fun x hx ↦ ?_⟩
  exact (mem_hierarchy_iff_rank_mem x ξ).mpr (hSξ _ ((mem_rankImage_iff w _).mpr ⟨x, hx, rfl⟩))

/-- A subset of a rank stage at a regular `θ` whose size is below some `κ ∈ θ` is a member of
the stage. -/
theorem small_subset_mem_hierarchy {θ κ w : V} (hθ : IsRegularCardinal θ) (hκθ : κ ∈ θ)
    (hw : w ⊆ hierarchy θ) (hsmall : USmall κ w) : w ∈ hierarchy θ := by
  obtain ⟨μ, hμκ, hle⟩ := hsmall
  have hθord : IsOrdinal θ := hθ.1.1
  exact subset_mem_hierarchy_of_cardLE hθ
    (IsTransitive.mem_trans IsOrdinal.toIsTransitive hμκ hκθ) hw hle

end ZFVP
