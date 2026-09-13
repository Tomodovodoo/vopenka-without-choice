import ZFVP.ModelTheory.CompleteSubalgebra
import ZFVP.ModelTheory.LevyConeAlgebraProperties
import ZFVP.ModelTheory.BooleanAntichains
import ZFVP.SetTheory.MaximalAntichains
import ZFVP.SetTheory.RegularUnions

/-! Regular joins reduce to joins of antichains.

A maximal antichain `A` of the nonzero conditions below a family `X` has the same regular join
as `X`: every element of `A` sits below a member of `X`, and a member of `X` that escaped the
join of `A` would meet `A` in nothing, contradicting maximality.

Two consequences:

* `isCompleteSubalgebra_of_antichain_joins`: to check that a negation and intersection closed set
  of regular sets is a complete subalgebra it is enough to check joins of antichains.
* `levy_exists_small_subset_regularJoin_eq`: over the Levy collapse at a measurable `κ` every
  regular join is already the join of a subfamily of size below `κ`, because the antichain has
  size below `κ` by the chain condition. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The nonzero conditions of a subalgebra `D` that lie below a member of `X`. -/
noncomputable def subalgebraBelowSet (P R D X : V) : V :=
  {d ∈ subalgebraConditions P R D ; ∃ w ∈ X, d ⊆ w}

theorem mem_subalgebraBelowSet_iff (P R D X d : V) :
    d ∈ subalgebraBelowSet P R D X ↔ d ∈ subalgebraConditions P R D ∧ ∃ w ∈ X, d ⊆ w :=
  mem_sep_iff

/-- The nonzero Boolean conditions that lie below a member of `X`. -/
noncomputable def booleanBelowSet (P R X : V) : V :=
  {d ∈ booleanConditions P R ; ∃ w ∈ X, d ⊆ w}

theorem mem_booleanBelowSet_iff (P R X d : V) :
    d ∈ booleanBelowSet P R X ↔ d ∈ booleanConditions P R ∧ ∃ w ∈ X, d ⊆ w :=
  mem_sep_iff

/-- The set of members of `W` containing `a`. Used to pick, for each element of an antichain
below `W`, a member of `W` above it. -/
noncomputable def coveringMembers (W a : V) : V := {w ∈ W ; a ⊆ w}

theorem mem_coveringMembers_iff (W a w : V) : w ∈ coveringMembers W a ↔ w ∈ W ∧ a ⊆ w := mem_sep_iff

instance coveringMembers_definable (W : V) : ℒₛₑₜ-function₁[V] (coveringMembers W) := by
  have hd : ℒₛₑₜ-relation[V] (fun S a ↦ ∀ w, w ∈ S ↔ w ∈ W ∧ a ⊆ w) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = coveringMembers W (v 1) ↔ _
  rw [mem_ext_iff]
  exact ⟨fun h w ↦ (h w).trans (mem_coveringMembers_iff W (v 1) w),
    fun h w ↦ (h w).trans (mem_coveringMembers_iff W (v 1) w).symm⟩

/-- A maximal antichain `A` among conditions below `X` joins to the same regular set as `X`.

`hSbelow` says every element of `S` lies below a member of `X`; `hScl` says the part of a member
of `X` missed by the join of `A` is back in `S` whenever it is nonzero. -/
theorem regularJoin_eq_of_maximalAntichain {P R X S A : V} (hR : IsForcingPreorder P R)
    (hXreg : ∀ w ∈ X, IsForcingRegular P R w)
    (hSsub : S ⊆ booleanConditions P R)
    (hSbelow : ∀ d ∈ S, ∃ w ∈ X, d ⊆ w)
    (hScl : ∀ w ∈ X, w ∩ forcingNegation P R (regularJoin P R A) ∈ booleanConditions P R →
      w ∩ forcingNegation P R (regularJoin P R A) ∈ S)
    (hA : IsMaximalAntichainIn (booleanConditions P R) (booleanOrder P R) S A) :
    regularJoin P R A = regularJoin P R X := by
  have hAB : A ⊆ booleanConditions P R := subset_trans hA.2.1 hSsub
  have hbreg : IsForcingRegular P R (regularJoin P R A) :=
    regularJoin_booleanSubset_regular hR hAB
  have hXjreg : IsForcingRegular P R (regularJoin P R X) :=
    regularJoin_regular hR (fun w hw ↦ (hXreg w hw).1)
  apply SetTheory.subset_antisymm
  · refine regularJoin_subset hR (fun a ha ↦ ?_) hXjreg
    obtain ⟨w, hw, haw⟩ := hSbelow a (hA.2.1 a ha)
    exact subset_trans haw (subset_regularJoin hR hw (hXreg w hw))
  · refine regularJoin_subset hR (fun w hw ↦ ?_) hbreg
    by_contra hnb
    have hex : ∃ p, p ∈ w ∧ p ∉ regularJoin P R A := by
      by_contra h
      push Not at h
      exact hnb (fun x hx ↦ h x hx)
    obtain ⟨p, hp, hpb⟩ := hex
    have hpP : p ∈ P := (hXreg w hw).1 p hp
    obtain ⟨q, hq, hqp⟩ := exists_forcingNegation_of_not_mem hpP hpb hbreg.2.2
    have hqP : q ∈ P := forcingNegation_subset _ _ _ q hq
    have hqw : q ∈ w := (hXreg w hw).2.1 p hp q hqP hqp
    have hcreg : IsForcingRegular P R (w ∩ forcingNegation P R (regularJoin P R A)) :=
      forcingRegular_inter (hXreg w hw) (forcingNegation_regular hR hbreg.2.1)
    have hcB : w ∩ forcingNegation P R (regularJoin P R A) ∈ booleanConditions P R :=
      (mem_booleanConditions_iff _ _ _).mpr ⟨hcreg, q, mem_inter_iff.mpr ⟨hqw, hq⟩⟩
    obtain ⟨a, ha, hcompat⟩ := hA.2.2 _ (hScl w hw hcB)
    obtain ⟨r, hr⟩ := (boolean_compatible_iff (hAB a ha) hcB).mp hcompat
    obtain ⟨hra, hrc⟩ := mem_inter_iff.mp hr
    have hrb : r ∈ regularJoin P R A := subset_regularJoin_of_mem hR hAB ha r hra
    have hrn : r ∈ forcingNegation P R (regularJoin P R A) := (mem_inter_iff.mp hrc).2
    have : r ∈ regularJoin P R A ∩ forcingNegation P R (regularJoin P R A) :=
      mem_inter_iff.mpr ⟨hrb, hrn⟩
    rw [inter_forcingNegation_eq_empty hR hbreg.1] at this
    exact not_mem_empty this

/-- Closure under joins of antichains is enough for a complete subalgebra. -/
theorem isCompleteSubalgebra_of_antichain_joins (hAC : InternalChoice V) {P R D : V}
    (hR : IsForcingPreorder P R) (hDreg : D ⊆ regularSets P R) (hPD : P ∈ D)
    (hneg : ∀ A ∈ D, forcingNegation P R A ∈ D)
    (hinter : ∀ A ∈ D, ∀ B ∈ D, A ∩ B ∈ D)
    (hjoin : ∀ A, A ⊆ subalgebraConditions P R D →
      IsForcingAntichain (booleanConditions P R) (booleanOrder P R) A →
      regularJoin P R A ∈ D) :
    IsCompleteSubalgebra P R D := by
  refine ⟨hDreg, hPD, hneg, ?_⟩
  intro X hX
  have hXreg : ∀ w ∈ X, IsForcingRegular P R w := fun w hw ↦
    (mem_regularSets_iff P R w).mp (hDreg w (hX w hw))
  set S := subalgebraBelowSet P R D X with hSdef
  have hSsub : S ⊆ booleanConditions P R := fun d hd ↦
    ((mem_subalgebraConditions_iff _ _ _ _).mp
      ((mem_subalgebraBelowSet_iff P R D X d).mp hd).1).2
  obtain ⟨A, hA⟩ := exists_maximalAntichain (P := booleanConditions P R) (R := booleanOrder P R)
    (booleanOrder_poset P R).1 hSsub (wellOrderable_of_internalChoice hAC S)
  have hAsub : A ⊆ subalgebraConditions P R D := fun a ha ↦
    ((mem_subalgebraBelowSet_iff P R D X a).mp (hA.2.1 a ha)).1
  have hbD : regularJoin P R A ∈ D := hjoin A hAsub hA.1
  have hScl : ∀ w ∈ X, w ∩ forcingNegation P R (regularJoin P R A) ∈ booleanConditions P R →
      w ∩ forcingNegation P R (regularJoin P R A) ∈ S := by
    intro w hw hcB
    refine (mem_subalgebraBelowSet_iff P R D X _).mpr ⟨?_, w, hw, fun x hx ↦ (mem_inter_iff.mp hx).1⟩
    exact (mem_subalgebraConditions_iff _ _ _ _).mpr
      ⟨hinter w (hX w hw) _ (hneg _ hbD), hcB⟩
  have hSbelow : ∀ d ∈ S, ∃ w ∈ X, d ⊆ w := fun d hd ↦
    ((mem_subalgebraBelowSet_iff P R D X d).mp hd).2
  rw [← regularJoin_eq_of_maximalAntichain hR hXreg hSsub hSbelow hScl hA]
  exact hbD

section Levy

variable {κ U : V} [IsOrdinal κ] (hAC : InternalChoice V)
  (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
  (hω : (ω : V) ∈ κ) (hκ : IsInitialOrdinal κ)

include hAC hU hc hω hκ in
/-- The `κ`-chain condition reduces regular joins over the Levy collapse to joins of subfamilies
of size below `κ`. -/
theorem levy_exists_small_subset_regularJoin_eq {W : V}
    (hW : W ⊆ booleanConditions (levyCollapse κ) (levyOrder κ)) :
    ∃ W₀ ⊆ W, ∃ ν ∈ κ, W₀ ≤# ν ∧
      regularJoin (levyCollapse κ) (levyOrder κ) W₀ =
        regularJoin (levyCollapse κ) (levyOrder κ) W := by
  set P := levyCollapse κ with hP
  set R := levyOrder κ with hRdef
  have hR : IsForcingPreorder P R := (levyCollapse_poset κ).1
  have hWreg : ∀ w ∈ W, IsForcingRegular P R w := fun w hw ↦ booleanConditions_regular (hW w hw)
  set S := booleanBelowSet P R W with hSdef
  have hSsub : S ⊆ booleanConditions P R := fun d hd ↦ ((mem_booleanBelowSet_iff P R W d).mp hd).1
  have hSbelow : ∀ d ∈ S, ∃ w ∈ W, d ⊆ w := fun d hd ↦
    ((mem_booleanBelowSet_iff P R W d).mp hd).2
  obtain ⟨A, hA⟩ := exists_maximalAntichain (P := booleanConditions P R) (R := booleanOrder P R)
    (booleanOrder_poset P R).1 hSsub (wellOrderable_of_internalChoice hAC S)
  have hAB : A ⊆ booleanConditions P R := subset_trans hA.2.1 hSsub
  have hScl : ∀ w ∈ W, w ∩ forcingNegation P R (regularJoin P R A) ∈ booleanConditions P R →
      w ∩ forcingNegation P R (regularJoin P R A) ∈ S := by
    intro w hw hcB
    exact (mem_booleanBelowSet_iff P R W _).mpr ⟨hcB, w, hw, fun x hx ↦ (mem_inter_iff.mp hx).1⟩
  have hAW : regularJoin P R A = regularJoin P R W :=
    regularJoin_eq_of_maximalAntichain hR hWreg hSsub hSbelow hScl hA
  -- the antichain has size below `κ`
  have hwo := wellOrderable_of_internalChoice hAC A
  have hνeq := wellOrderedCardinal_cardEQ hwo
  have hνinit := wellOrderedCardinal_initial hwo
  have := hνinit.1
  have hνκ : wellOrderedCardinal A ∈ κ := by
    rcases IsOrdinal.mem_trichotomy (α := wellOrderedCardinal A) (β := κ) with h | h | h
    · exact h
    · exact (levyBooleanAntichain_not_cardLE hAC hU hc hω hκ hA.1 (h ▸ hνeq.le)).elim
    · exact (levyBooleanAntichain_not_cardLE hAC hU hc hω hκ hA.1
        ((cardLE_of_subset (IsOrdinal.toIsTransitive.transitive _ h)).trans hνeq.le)).elim
  -- pick a member of `W` above each element of the antichain
  have hne : ∀ a ∈ A, IsNonempty (coveringMembers W a) := by
    intro a ha
    obtain ⟨w, hw, haw⟩ := hSbelow a (hA.2.1 a ha)
    exact ⟨w, (mem_coveringMembers_iff W a w).mpr ⟨hw, haw⟩⟩
  obtain ⟨f, hf, hdom, hval⟩ :=
    choice_for_definable_family hAC A (coveringMembers W) inferInstance hne
  have := hf
  refine ⟨range f, ?_, wellOrderedCardinal A, hνκ, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hxy⟩ := mem_range_iff.mp hy
    have hxA : x ∈ A := hdom ▸ mem_domain_of_kpair_mem hxy
    rw [← value_eq_of_kpair_mem hxy]
    exact ((mem_coveringMembers_iff W x _).mp (hval x hxA)).1
  · exact (cardLE_of_surjective_function (wellOrderable_of_internalChoice hAC A)
      (function_mem_of_isFunction' hdom rfl) rfl).trans hνeq.ge
  · have hW₀W : range f ⊆ W := by
      intro y hy
      obtain ⟨x, hxy⟩ := mem_range_iff.mp hy
      have hxA : x ∈ A := hdom ▸ mem_domain_of_kpair_mem hxy
      rw [← value_eq_of_kpair_mem hxy]
      exact ((mem_coveringMembers_iff W x _).mp (hval x hxA)).1
    have hW₀reg : IsForcingRegular P R (regularJoin P R (range f)) :=
      regularJoin_booleanSubset_regular hR (subset_trans hW₀W hW)
    apply SetTheory.subset_antisymm (regularJoin_mono hW₀W)
    rw [← hAW]
    refine regularJoin_subset hR (fun a ha ↦ ?_) hW₀reg
    have hfa : f ‘ a ∈ range f := mem_range_iff.mpr ⟨a, kpair_value_mem (hdom ▸ ha)⟩
    refine subset_trans ((mem_coveringMembers_iff W a _).mp (hval a ha)).2 ?_
    exact subset_regularJoin_of_mem hR (subset_trans hW₀W hW) hfa

end Levy

end ZFVP
