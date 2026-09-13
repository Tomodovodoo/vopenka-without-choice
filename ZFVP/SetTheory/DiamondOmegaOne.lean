import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Cofinality.Club

/-! The index order `ω₁` used by the ω₁-length constructions on the ambient universe, and Jensen's
diamond principle on it. Club and stationary sets come from Mathlib
(`Mathlib/SetTheory/Cardinal/Cofinality/Club.lean`); this file only fixes the carrier
`Ordinal.ToType (Ordinal.omega.{0} 1)`, records its cardinality, states `◊`, and gives the two
consequences an ω₁ induction needs: a stationary set is cofinal, and a diamond sequence guesses
any set correctly at arbitrarily large stages. -/

namespace ZFVP

open Ordinal Set

/-- The order type `ω₁`, as a type in `Type 0`. This is the same spelling used by
`ZFVP.IsCofinalOmegaOneChain`, so chains indexed there and constructions here share an index
order. -/
abbrev OmegaOne : Type := Ordinal.ToType (Ordinal.omega.{0} 1)

instance : Nonempty OmegaOne :=
  Ordinal.nonempty_toType_iff.2 (Ordinal.omega_pos 1).ne'

noncomputable example : LinearOrder OmegaOne := inferInstance
example : WellFoundedLT OmegaOne := inferInstance

/-- `ω₁` has `ℵ₁` many elements. -/
theorem mk_omegaOne : Cardinal.mk OmegaOne = Cardinal.aleph 1 := by
  rw [Cardinal.mk_toType, Ordinal.card_omega]

/-- Every upper set is a club: it is closed under suprema because a supremum of a nonempty subset
lies above one of its elements, and it is cofinal because any point has an upper bound in it. -/
theorem isClub_Ici (γ : OmegaOne) : IsClub (Set.Ici γ) where
  dirSupClosed := by
    intro d hd hd0 _ a ha
    obtain ⟨b, hb⟩ := hd0
    exact le_trans (hd hb) (ha.1 hb)
  isCofinal := fun x => ⟨max x γ, Set.mem_Ici.2 (le_max_right _ _), le_max_left _ _⟩

/-- A stationary set has elements above any given point. -/
theorem IsStationary.exists_le {s : Set OmegaOne} (h : IsStationary s) (γ : OmegaOne) :
    ∃ α ∈ s, γ ≤ α := by
  obtain ⟨α, hαs, hαγ⟩ := h (isClub_Ici γ)
  exact ⟨α, hαs, hαγ⟩

/-- A stationary set is cofinal. -/
theorem IsStationary.isCofinal {s : Set OmegaOne} (h : IsStationary s) : IsCofinal s :=
  fun γ => IsStationary.exists_le h γ

/-- `A` is a diamond sequence: each `A α` is a subset of `α`, and for every `S ⊆ ω₁` the set of
stages where `A` guesses `S` correctly is stationary. -/
def IsDiamondSequence (A : OmegaOne → Set OmegaOne) : Prop :=
  (∀ α, A α ⊆ {β | β < α}) ∧ ∀ S : Set OmegaOne, IsStationary {α | A α = {β ∈ S | β < α}}

/-- Jensen's `◊` on `ω₁`, stated for the ambient universe. It is a hypothesis of the modules that
use it, not a theorem. -/
def DiamondOmegaOne : Prop := ∃ A, IsDiamondSequence A

variable {A : OmegaOne → Set OmegaOne}

/-- Each entry of a diamond sequence is a set of smaller ordinals. -/
theorem IsDiamondSequence.subset_lt (h : IsDiamondSequence A) (α : OmegaOne) :
    A α ⊆ {β | β < α} :=
  h.1 α

/-- The stages at which a diamond sequence guesses `S` form a stationary set. -/
theorem IsDiamondSequence.stationary_guess (h : IsDiamondSequence A) (S : Set OmegaOne) :
    IsStationary {α | A α = {β ∈ S | β < α}} :=
  h.2 S

/-- The form used by an ω₁ induction: past any stage `γ` there is a stage where the diamond
sequence guesses `S` correctly. -/
theorem IsDiamondSequence.exists_guess_above (h : IsDiamondSequence A) (S : Set OmegaOne)
    (γ : OmegaOne) : ∃ α, γ ≤ α ∧ A α = {β ∈ S | β < α} := by
  obtain ⟨α, hα, hγ⟩ := IsStationary.exists_le (h.stationary_guess S) γ
  exact ⟨α, hγ, hα⟩

end ZFVP
