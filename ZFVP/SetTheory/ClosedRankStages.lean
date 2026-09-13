import ZFVP.SetTheory.RankBounds
import ZFVP.SetTheory.UniformCollapse
import ZFVP.SetTheory.TransfiniteIteration
import ZFVP.SetTheory.WellOrderedSurjection
import ZFVP.SetTheory.WellOrderingChoice
import ZFVP.SetTheory.HartogsRegularChoice

/-! Rank stages closed under Mostowski collapses. A limit ordinal `lam` closed under successor and
under `β ↦ hartogsNumber (hierarchy β)` gives a stage `hierarchy lam` that contains the transitive
collapse of every well-founded extensional relation it contains. The two ingredients are the bound
`rank C ≤# C` for transitive `C` and the fact that such a `lam` exists above every ordinal. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A subset of a member of a rank stage is a member of that stage. -/
theorem mem_hierarchy_of_subset' {lam x C : V} [IsOrdinal lam] (hC : C ∈ hierarchy lam)
    (h : x ⊆ C) : x ∈ hierarchy lam := by
  have hrC : rank C ∈ lam := (mem_hierarchy_iff_rank_mem C lam).mp hC
  have : IsOrdinal (rank x) := (rank_spec x).1
  have : IsOrdinal (rank C) := (rank_spec C).1
  rcases IsOrdinal.subset_iff.mp (rank_mono h) with he | hlt
  · exact (mem_hierarchy_iff_rank_mem x lam).mpr (he ▸ hrC)
  · exact (mem_hierarchy_iff_rank_mem x lam).mpr
      (IsOrdinal.toIsTransitive.transitive _ hrC _ hlt)

/-- The union of two ordinals is one of them. -/
theorem ordinal_union_eq_or (a b : V) [IsOrdinal a] [IsOrdinal b] : a ∪ b = a ∨ a ∪ b = b := by
  rcases IsOrdinal.subset_or_supset (α := a) (β := b) with h | h
  · exact Or.inr (union_eq_iff_left.mpr h)
  · exact Or.inl (union_eq_iff_right.mpr h)

/-- The union of two ordinals is an ordinal. -/
theorem union_isOrdinal (a b : V) [IsOrdinal a] [IsOrdinal b] : IsOrdinal (a ∪ b) := by
  rcases ordinal_union_eq_or a b with h | h <;> rw [h] <;> infer_instance

/-- An ordinal below or equal to `b` is a member of `succ b`. -/
theorem mem_succ_of_subset {a b : V} [IsOrdinal a] [IsOrdinal b] (h : a ⊆ b) : a ∈ succ b := by
  rcases IsOrdinal.subset_iff.mp h with rfl | hm
  · exact mem_succ_self _
  · exact mem_succ_iff.mpr (Or.inr hm)

/-- Every ordinal below the rank of a transitive set is the rank of one of its members. -/
theorem exists_mem_rank_eq {C α : V} (hC : IsTransitive C) (hα : α ∈ rank C) :
    ∃ x ∈ C, rank x = α := by
  have hαo : IsOrdinal α := IsOrdinal.of_mem hα
  -- from `α ∈ rank C`, some member of `C` has rank at least `α`
  have key : ∀ B : V, α ∈ rank B → ∃ x ∈ B, α ⊆ rank x := by
    intro B hB
    have hnot : ¬ B ⊆ hierarchy α := by
      intro hsub
      exact mem_irrefl α (rank_minimal B α hαo hsub α hB)
    have hex : ∃ x ∈ B, x ∉ hierarchy α := by
      by_contra h
      refine hnot (fun x hx ↦ ?_)
      by_contra hnx
      exact h ⟨x, hx, hnx⟩
    obtain ⟨x, hxB, hx⟩ := hex
    refine ⟨x, hxB, ?_⟩
    have hrx : rank x ∉ α := fun h ↦ hx ((mem_hierarchy_iff_rank_mem x α).mpr h)
    rcases IsOrdinal.mem_trichotomy α (rank x) with h | h | h
    · exact IsOrdinal.toIsTransitive.transitive _ h
    · exact h ▸ subset_refl _
    · exact (hrx h).elim
  -- the least rank of such a member is `α` itself
  set P : V → Prop := fun β ↦ ∃ x ∈ C, rank x = β ∧ α ⊆ β with hPdef
  have hP : ℒₛₑₜ-predicate P := by rw [hPdef]; definability
  obtain ⟨x₀, hx₀C, hx₀⟩ := key C hα
  obtain ⟨β, hβ, -⟩ := leastOrdinal_existsUnique P hP ⟨rank x₀, inferInstance, x₀, hx₀C, rfl, hx₀⟩
  obtain ⟨y, hyC, hry, hαβ⟩ := hβ.2.1
  have hβo : IsOrdinal β := hβ.1
  rcases IsOrdinal.subset_iff.mp hαβ with rfl | hlt
  · exact ⟨y, hyC, hry⟩
  · exfalso
    have hyr : α ∈ rank y := hry ▸ hlt
    obtain ⟨z, hzy, hz⟩ := key y hyr
    have hzC : z ∈ C := hC.mem_trans hzy hyC
    have hzβ : rank z ∈ β := hry ▸ rank_mem hzy
    have hmin : β ⊆ rank z := hβ.2.2 (rank z) inferInstance ⟨z, hzC, rfl, hz⟩
    exact mem_irrefl _ (hmin _ hzβ)

/-- For a transitive set the rank map is onto the rank, so with a well-ordering of the set the
rank injects into it. -/
theorem rank_cardLE_of_transitive (hAC : InternalChoice V) {C : V} (hC : IsTransitive C) :
    rank C ≤# C := by
  have hmap : ∀ x ∈ C, rank x ∈ rank C := fun x hx ↦ rank_mem hx
  have hf := definableGraph_mem_function_of_mapsTo C (rank C) (rank : V → V) inferInstance hmap
  refine cardLE_of_surjective_function (wellOrderable_of_internalChoice hAC C) hf ?_
  rw [range_definableGraph]
  apply mem_ext
  intro α
  rw [repl_spec]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact rank_mem hx
  · intro hα
    obtain ⟨x, hx, hrx⟩ := exists_mem_rank_eq hC hα
    exact ⟨x, hx, hrx.symm⟩

/-- The rank of a transitive set is below the Hartogs number of that set. -/
theorem rank_mem_hartogsNumber (hAC : InternalChoice V) {C : V} (hC : IsTransitive C) :
    rank C ∈ hartogsNumber C :=
  ordinal_cardLE_iff_mem_hartogsNumber.mp (rank_cardLE_of_transitive hAC hC)

/-- The step of the closure iteration: past `β` and past the Hartogs number of `V_β`. -/
noncomputable def rankClosureStep (β : V) : V := succ (β ∪ hartogsNumber (hierarchy β))

instance rankClosureStep_definable : ℒₛₑₜ-function₁[V] rankClosureStep := by
  unfold rankClosureStep
  definability

/-- `ω` is a limit ordinal. -/
theorem isLimitOrdinal_omega : IsLimitOrdinal (ω : V) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · intro h
    exact not_mem_empty (h ▸ (empty_mem_ω : (∅ : V) ∈ (ω : V)))
  · rintro ⟨ξ, hξ⟩
    have hξω : ξ ∈ (ω : V) := hξ ▸ mem_succ_self ξ
    exact mem_irrefl _ (hξ ▸ ω_succ_closed hξω)

/-- Above every ordinal there is a limit ordinal closed under successor and under
`β ↦ hartogsNumber (hierarchy β)`. -/
theorem exists_closed_limit_ordinal (γ : V) [IsOrdinal γ] :
    ∃ lam : V, IsOrdinal lam ∧ γ ∈ lam ∧ (∀ β ∈ lam, succ β ∈ lam) ∧
      (∀ β ∈ lam, hartogsNumber (hierarchy β) ∈ lam) := by
  have hstep : ℒₛₑₜ-function₁ (rankClosureStep : V → V) := inferInstance
  obtain ⟨it, hitdef⟩ : ∃ g : V → V, g = iterate rankClosureStep hstep (succ γ) := ⟨_, rfl⟩
  have hit : ℒₛₑₜ-function₁ it := hitdef ▸ iterate_definable hstep (succ γ)
  have hit0 : it ∅ = succ γ := by rw [hitdef]; exact iterate_zero hstep (succ γ)
  have hitS : ∀ n : V, IsOrdinal n → it (succ n) = rankClosureStep (it n) := by
    intro n hn
    have := hn
    rw [hitdef]
    exact iterate_succ hstep (succ γ) n
  have hlim : IsLimitOrdinal (ω : V) := isLimitOrdinal_omega
  have hitL : ∀ x : V, x ∈ it (ω : V) ↔ ∃ n ∈ (ω : V), x ∈ it n := by
    intro x
    rw [hitdef]
    exact mem_iterate_limit_iff hstep (succ γ) (ω : V) hlim x
  -- every finite stage is an ordinal
  have hord : ∀ n ∈ (ω : V), IsOrdinal (it n) := by
    apply naturalNumber_induction (fun n ↦ IsOrdinal (it n)) (by rw [hitdef]; definability)
    · show IsOrdinal (it ∅)
      rw [hit0]
      infer_instance
    · intro n hn ih
      have : IsOrdinal n := IsOrdinal.nat hn
      have := ih
      rw [hitS n inferInstance]
      unfold rankClosureStep
      have := union_isOrdinal (it n) (hartogsNumber (hierarchy (it n)))
      infer_instance
  refine ⟨it (ω : V), ?_, ?_, ?_, ?_⟩
  · refine IsOrdinal.of_transitive_of_isOrdinal ⟨?_⟩ ?_
    · intro x hx y hy
      obtain ⟨n, hn, hxn⟩ := (hitL x).mp hx
      have : IsOrdinal (it n) := hord n hn
      exact (hitL y).mpr ⟨n, hn, IsOrdinal.toIsTransitive.transitive x hxn y hy⟩
    · intro x hx
      obtain ⟨n, hn, hxn⟩ := (hitL x).mp hx
      have : IsOrdinal (it n) := hord n hn
      exact IsOrdinal.of_mem hxn
  · exact (hitL γ).mpr ⟨∅, empty_mem_ω, by rw [hit0]; exact mem_succ_self γ⟩
  · -- closure under successor
    intro β hβ
    obtain ⟨n, hn, hβn⟩ := (hitL β).mp hβ
    have : IsOrdinal n := IsOrdinal.nat hn
    have : IsOrdinal (it n) := hord n hn
    have : IsOrdinal β := IsOrdinal.of_mem hβn
    have := union_isOrdinal (it n) (hartogsNumber (hierarchy (it n)))
    have hβsub : β ⊆ it n := IsOrdinal.toIsTransitive.transitive β hβn
    have hsubu : it n ⊆ it n ∪ hartogsNumber (hierarchy (it n)) :=
      fun x hx ↦ mem_union_iff.mpr (Or.inl hx)
    refine (hitL _).mpr ⟨succ n, ω_succ_closed hn, ?_⟩
    rw [hitS n inferInstance]
    unfold rankClosureStep
    refine mem_succ_of_subset (subset_trans ?_ hsubu)
    intro x hx
    rcases mem_succ_iff.mp hx with rfl | hx
    · exact hβn
    · exact hβsub x hx
  · -- closure under the Hartogs number of the stage
    intro β hβ
    obtain ⟨n, hn, hβn⟩ := (hitL β).mp hβ
    have : IsOrdinal n := IsOrdinal.nat hn
    have : IsOrdinal (it n) := hord n hn
    have : IsOrdinal β := IsOrdinal.of_mem hβn
    have := union_isOrdinal (it n) (hartogsNumber (hierarchy (it n)))
    have hβsub : β ⊆ it n := IsOrdinal.toIsTransitive.transitive β hβn
    have hsubu : hartogsNumber (hierarchy (it n)) ⊆
        it n ∪ hartogsNumber (hierarchy (it n)) := fun x hx ↦ mem_union_iff.mpr (Or.inr hx)
    refine (hitL _).mpr ⟨succ n, ω_succ_closed hn, ?_⟩
    rw [hitS n inferInstance]
    unfold rankClosureStep
    refine mem_succ_of_subset (subset_trans ?_ hsubu)
    exact hartogsNumber_mono (cardLE_of_subset (hierarchy_mono hβsub))

/-- If a rank stage is closed under successor and under the Hartogs numbers of the earlier stages,
it contains the Mostowski collapse of every well-founded extensional relation it contains. -/
theorem collapse_mem_hierarchy {lam : V} [IsOrdinal lam] (hAC : InternalChoice V)
    (hlim : ∀ β ∈ lam, succ β ∈ lam)
    (hclosed : ∀ β ∈ lam, hartogsNumber (hierarchy β) ∈ lam)
    {R D : V} (hR : R ∈ hierarchy lam) (hD : D ∈ hierarchy lam)
    (hwf : IsInternallyWellFounded R D) (hext : IsExtensionalOn R D) :
    mostowskiMap R D ∈ hierarchy lam := by
  have hc := mostowskiMap_isTransitiveCollapse hwf hext
  set f : V := mostowskiMap R D with hfdef
  set C : V := range f with hCdef
  have hCtrans : IsTransitive C := hc.1
  -- the collapse is a surjection from `D` onto `C`
  have hCD : C ≤# D :=
    cardLE_of_surjective_function (wellOrderable_of_internalChoice hAC D) hc.2.1 hc.2.2.1
  -- `D` sits inside the stage `succ (rank D)`, which is below `lam`
  have hrD : rank D ∈ lam := (mem_hierarchy_iff_rank_mem D lam).mp hD
  have hβ : succ (rank D) ∈ lam := hlim _ hrD
  have hDsub : D ⊆ hierarchy (succ (rank D)) :=
    subset_trans (subset_hierarchy_rank D)
      (hierarchy_mono (IsOrdinal.toIsTransitive.transitive _ (mem_succ_self (rank D))))
  have hCstage : C ≤# hierarchy (succ (rank D)) := hCD.trans (cardLE_of_subset hDsub)
  -- hence the rank of `C` is below the Hartogs number of that stage
  have hrankC : rank C ≤# hierarchy (succ (rank D)) :=
    (rank_cardLE_of_transitive hAC hCtrans).trans hCstage
  have hCmem : C ∈ hierarchy lam := by
    refine (mem_hierarchy_iff_rank_mem C lam).mpr ?_
    exact IsOrdinal.toIsTransitive.transitive _ (hclosed _ hβ) _
      (ordinal_cardLE_iff_mem_hartogsNumber.mp hrankC)
  -- the collapse map is a set of pairs from `D × C`
  exact mem_hierarchy_of_subset' (prod_mem_hierarchy_limit hlim hD hCmem)
    (subset_prod_of_mem_function hc.2.1)

end ZFVP
