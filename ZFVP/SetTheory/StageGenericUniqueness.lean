import ZFVP.SetTheory.RegularSetAlgebra
import ZFVP.SetTheory.InternalWellFounded
import ZFVP.SetTheory.UniformCollapse

/-! Uniqueness of generic ultrafilters on a subalgebra presented by closure stages: two
antichain-generic ultrafilters on the regular sets that agree on the generators agree on every
stage. The statement is internal to one model of ZF; in an extension it is applied to the checked
stages of a generated subalgebra of the ground model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A generic ultrafilter on the regular sets `Reg` relative to a family `MA` of antichains. -/
structure IsAntichainGeneric (Reg MA U : V) : Prop where
  subset : U ⊆ Reg
  upward : ∀ d ∈ U, ∀ d' ∈ Reg, d ⊆ d' → d' ∈ U
  inter : ∀ d ∈ U, ∀ d' ∈ U, d ∩ d' ∈ U
  proper : (∅ : V) ∉ U
  meets : ∀ A ∈ MA, ∃ a ∈ A, a ∈ U

/-- Closure-stage data: a function `Cl` on the ordinal `θ` whose stages are built from the
generators `S` by complements and joins of members of `Ysets`, with deciding and refining
antichains in `MA`. -/
structure IsStageSystem (P R Reg MA Ysets S Cl θ : V) : Prop where
  ordinal : IsOrdinal θ
  fn : IsFunction Cl
  dom : domain Cl = θ
  reg_regular : ∀ d ∈ Reg, IsForcingRegular P R d
  stage_reg : ∀ α ∈ θ, Cl ‘ α ⊆ Reg
  gen_reg : S ⊆ Reg
  neg_reg : ∀ d ∈ Reg, forcingNegation P R d ∈ Reg
  join_reg : ∀ Y ∈ Ysets, regularJoin P R Y ∈ Reg
  step : ∀ α ∈ θ, ∀ d ∈ Cl ‘ α, d ∈ S ∨ (∃ β ∈ α, d ∈ Cl ‘ β) ∨
    (∃ A, (A ∈ S ∨ ∃ β ∈ α, A ∈ Cl ‘ β) ∧ d = forcingNegation P R A) ∨
    (∃ Y ∈ Ysets, (∀ y ∈ Y, y ∈ S ∨ ∃ β ∈ α, y ∈ Cl ‘ β) ∧ d = regularJoin P R Y)
  decide : ∀ d ∈ Reg, ∃ A ∈ MA, ∀ a ∈ A, a ⊆ d ∨ a ⊆ forcingNegation P R d
  refine : ∀ Y ∈ Ysets, ∃ A ∈ MA, ∀ a ∈ A,
    (∃ y ∈ Y, a ⊆ y) ∨ a ⊆ forcingNegation P R (regularJoin P R Y)

section

variable {P R Reg MA Ysets S Cl θ U : V} (hR : IsForcingPreorder P R)
  (hsys : IsStageSystem P R Reg MA Ysets S Cl θ) (hU : IsAntichainGeneric Reg MA U)

include hR hsys hU in
theorem antichainGeneric_neg_mem_iff {d : V} (hd : d ∈ Reg) :
    forcingNegation P R d ∈ U ↔ d ∉ U := by
  constructor
  · intro hn hdU
    have := hU.inter d hdU _ hn
    rw [inter_forcingNegation_eq_empty hR (hsys.reg_regular d hd).1] at this
    exact hU.proper this
  · intro hdU
    obtain ⟨A, hA, hdec⟩ := hsys.decide d hd
    obtain ⟨a, ha, haU⟩ := hU.meets A hA
    rcases hdec a ha with h | h
    · exact (hdU (hU.upward a haU d hd h)).elim
    · exact hU.upward a haU _ (hsys.neg_reg d hd) h

include hR hsys hU in
theorem antichainGeneric_join_mem_iff {Y : V} (hY : Y ∈ Ysets) (hYreg : ∀ y ∈ Y, y ∈ Reg) :
    regularJoin P R Y ∈ U ↔ ∃ y ∈ Y, y ∈ U := by
  constructor
  · intro hj
    obtain ⟨A, hA, href⟩ := hsys.refine Y hY
    obtain ⟨a, ha, haU⟩ := hU.meets A hA
    rcases href a ha with ⟨y, hy, hay⟩ | h
    · exact ⟨y, hy, hU.upward a haU y (hYreg y hy) hay⟩
    · exfalso
      have hin := hU.inter a haU _ hj
      have hempty : a ∩ regularJoin P R Y = ∅ := by
        apply mem_ext
        intro p
        constructor
        · intro hp
          obtain ⟨hpa, hpj⟩ := mem_inter_iff.mp hp
          have : p ∈ regularJoin P R Y ∩ forcingNegation P R (regularJoin P R Y) :=
            mem_inter_iff.mpr ⟨hpj, h p hpa⟩
          rw [inter_forcingNegation_eq_empty hR (hsys.reg_regular _ (hsys.join_reg Y hY)).1] at this
          exact (not_mem_empty this).elim
        · intro hp
          exact (not_mem_empty hp).elim
      rw [hempty] at hin
      exact hU.proper hin
  · rintro ⟨y, hy, hyU⟩
    exact hU.upward y hyU _ (hsys.join_reg Y hY)
      (subset_regularJoin hR hy (hsys.reg_regular y (hYreg y hy)))

end

/-- Two antichain-generic ultrafilters agreeing on the generators agree on every stage. -/
theorem stage_generic_unique {P R Reg MA Ysets S Cl θ U U' : V} (hR : IsForcingPreorder P R)
    (hsys : IsStageSystem P R Reg MA Ysets S Cl θ) (hU : IsAntichainGeneric Reg MA U)
    (hU' : IsAntichainGeneric Reg MA U') (hagree : ∀ s ∈ S, (s ∈ U ↔ s ∈ U')) :
    ∀ α ∈ θ, ∀ d ∈ Cl ‘ α, (d ∈ U ↔ d ∈ U') := by
  have := hsys.ordinal
  apply internalWellFounded_induction (membershipRelation_wellFounded θ)
    (fun α ↦ ∀ d ∈ Cl ‘ α, (d ∈ U ↔ d ∈ U')) (by definability)
  intro α hα ih d hd
  have hearlier : ∀ A, (A ∈ S ∨ ∃ β ∈ α, A ∈ Cl ‘ β) → A ∈ Reg ∧ (A ∈ U ↔ A ∈ U') := by
    intro A hA
    rcases hA with hA | ⟨β, hβα, hA⟩
    · exact ⟨hsys.gen_reg A hA, hagree A hA⟩
    · have hβ : β ∈ θ := IsOrdinal.toIsTransitive.mem_trans hβα hα
      exact ⟨hsys.stage_reg β hβ A hA,
        ih β hβ ((pair_mem_membershipRelation _ _ _).mpr ⟨hβ, hα, hβα⟩) A hA⟩
  rcases hsys.step α hα d hd with hdS | ⟨β, hβα, hdβ⟩ | ⟨A, hA, rfl⟩ | ⟨Y, hY, hYearly, rfl⟩
  · exact hagree d hdS
  · exact (hearlier d (Or.inr ⟨β, hβα, hdβ⟩)).2
  · obtain ⟨hAreg, hAiff⟩ := hearlier A hA
    rw [antichainGeneric_neg_mem_iff hR hsys hU hAreg, antichainGeneric_neg_mem_iff hR hsys hU' hAreg, hAiff]
  · have hYreg : ∀ y ∈ Y, y ∈ Reg := fun y hy ↦ (hearlier y (hYearly y hy)).1
    rw [antichainGeneric_join_mem_iff hR hsys hU hY hYreg, antichainGeneric_join_mem_iff hR hsys hU' hY hYreg]
    constructor
    · rintro ⟨y, hy, hyU⟩
      exact ⟨y, hy, (hearlier y (hYearly y hy)).2.mp hyU⟩
    · rintro ⟨y, hy, hyU⟩
      exact ⟨y, hy, (hearlier y (hYearly y hy)).2.mpr hyU⟩

end ZFVP
