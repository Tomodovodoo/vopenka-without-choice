import Mathlib.Order.CompleteLattice.Basic
import Mathlib.SetTheory.Cardinal.Aleph
import ZFVP.SetTheory.DiamondOmegaOne

/-! Transfinite stage recursion in a complete lattice.

Stage 1 of the appendix of Enayat's paper builds a family of stages indexed by the countable
ordinals: a limit stage is the union of the earlier stages, and a successor stage is obtained from
the previous one by a step operation. This file is the abstract skeleton of that construction, with
no set theory and no model theory in it. The stages live in an arbitrary complete lattice `S` and
the construction is driven by a function `step : Ordinal → S → S`.

The recursion is written in one clause,

    stageRec step o = step o (⨆ β < o, stageRec step β),

so there is no case split on zero, successor and limit. The limit behaviour is a hypothesis on
`step` (`step` is the identity at limit ordinals) rather than a case of the definition, and the
successor equation `stageRec step (succ o) = step (succ o) (stageRec step o)` is a theorem, proved
from monotonicity of the stages.

The last theorem is the one the construction needs: a property `Q` that survives one step and
survives suprema of countable families holds at every stage below `ω₁`. That is what keeps every
stage of Enayat's chain countable. -/

namespace ZFVP

open Set

universe u

variable {S : Type u} [CompleteLattice S]

/-- The stage at ordinal `o`: apply `step o` to the supremum of all earlier stages. -/
noncomputable def stageRec (step : Ordinal.{0} → S → S) (o : Ordinal.{0}) : S :=
  step o (⨆ β : Set.Iio o, stageRec step β.1)
termination_by o
decreasing_by exact β.2

/-- The defining equation of `stageRec`. -/
theorem stageRec_eq (step : Ordinal.{0} → S → S) (o : Ordinal.{0}) :
    stageRec step o = step o (⨆ β : Set.Iio o, stageRec step (β : Ordinal.{0})) := by
  rw [stageRec]

/-- Rewriting the supremum in the defining equation as the supremum of a set of stages. -/
theorem stageRec_eq_sSup (step : Ordinal.{0} → S → S) (o : Ordinal.{0}) :
    stageRec step o = step o (sSup (stageRec step '' Set.Iio o)) := by
  rw [stageRec_eq, Set.image_eq_range]
  rfl

/-- If every step is increasing then an earlier stage is below a later one. -/
theorem le_stageRec {step : Ordinal.{0} → S → S} (hstep : ∀ o s, s ≤ step o s)
    {o β : Ordinal.{0}} (h : β < o) : stageRec step β ≤ stageRec step o := by
  refine le_trans ?_ ((hstep o _).trans_eq (stageRec_eq step o).symm)
  exact le_iSup (fun γ : Set.Iio o ↦ stageRec step (γ : Ordinal.{0})) ⟨β, h⟩

/-- If every step is increasing then the stages are monotone in the ordinal index. -/
theorem stageRec_monotone {step : Ordinal.{0} → S → S} (hstep : ∀ o s, s ≤ step o s) :
    Monotone (stageRec step) := by
  intro a b hab
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · exact le_stageRec hstep h

/-- At a limit ordinal the stage is the supremum of the earlier stages, provided `step` does
nothing at limit ordinals. -/
theorem stageRec_limit {step : Ordinal.{0} → S → S}
    (hlim : ∀ o : Ordinal.{0}, Order.IsSuccLimit o → ∀ s, step o s = s)
    {o : Ordinal.{0}} (ho : Order.IsSuccLimit o) :
    stageRec step o = ⨆ β : Set.Iio o, stageRec step (β : Ordinal.{0}) := by
  rw [stageRec_eq, hlim o ho]

/-- The successor equation: the stage at `Order.succ o` is one step applied to the stage at `o`.
The supremum over the ordinals below `Order.succ o` collapses to the stage at `o`, since the
stages are monotone. -/
theorem stageRec_succ {step : Ordinal.{0} → S → S} (hstep : ∀ o s, s ≤ step o s)
    (o : Ordinal.{0}) :
    stageRec step (Order.succ o) = step (Order.succ o) (stageRec step o) := by
  rw [stageRec_eq]
  congr 1
  refine le_antisymm (iSup_le fun β ↦ ?_) ?_
  · exact stageRec_monotone hstep (Order.lt_succ_iff.mp β.2)
  · exact le_iSup (fun γ : Set.Iio (Order.succ o) ↦ stageRec step (γ : Ordinal.{0}))
      ⟨o, Order.lt_succ o⟩

/-- Smallness transfer. If `Q` survives one step and survives suprema of countable sets, then `Q`
holds at every stage below `ω₁`. The index set of the supremum in the defining equation is
`Set.Iio o`, which is countable exactly because `o` is a countable ordinal. -/
theorem stageRec_pred (step : Ordinal.{0} → S → S) (Q : S → Prop)
    (hQstep : ∀ o s, Q s → Q (step o s))
    (hQsup : ∀ T : Set S, T.Countable → (∀ s ∈ T, Q s) → Q (sSup T))
    {o : Ordinal.{0}} (ho : o < Ordinal.omega.{0} 1) : Q (stageRec step o) := by
  revert ho
  induction o using WellFoundedLT.induction with
  | ind o ih =>
    intro ho
    rw [stageRec_eq_sSup]
    refine hQstep o _ (hQsup _ ((Cardinal.countable_Iio_of_lt_omega_one ho).image _) ?_)
    rintro s ⟨β, hβ, rfl⟩
    exact ih β hβ (hβ.trans ho)

/-- The stages transported to the index type `OmegaOne`, which is what the ω₁-length construction
is indexed by. -/
noncomputable def stageRecOmegaOne (step : Ordinal.{0} → S → S) (i : OmegaOne) : S :=
  stageRec step (Ordinal.typein (α := OmegaOne) (· < ·) i)

/-- `stageRecOmegaOne` agrees with `stageRec` at the ordinal named by the index. -/
theorem stageRecOmegaOne_eq (step : Ordinal.{0} → S → S) (i : OmegaOne) :
    stageRecOmegaOne step i = stageRec step (Ordinal.typein (α := OmegaOne) (· < ·) i) :=
  rfl

/-- The `OmegaOne`-indexed stages are monotone. -/
theorem stageRecOmegaOne_monotone {step : Ordinal.{0} → S → S} (hstep : ∀ o s, s ≤ step o s) :
    Monotone (stageRecOmegaOne step) := fun _ _ hij ↦
  stageRec_monotone hstep (Ordinal.typein_le_typein' _ |>.mpr hij)

/-- Smallness transfer for the `OmegaOne`-indexed stages: every stage of the ω₁-length
construction satisfies `Q`. -/
theorem stageRecOmegaOne_pred (step : Ordinal.{0} → S → S) (Q : S → Prop)
    (hQstep : ∀ o s, Q s → Q (step o s))
    (hQsup : ∀ T : Set S, T.Countable → (∀ s ∈ T, Q s) → Q (sSup T))
    (i : OmegaOne) : Q (stageRecOmegaOne step i) := by
  refine stageRec_pred step Q hQstep hQsup ?_
  have htype : Ordinal.type (α := OmegaOne) (· < ·) = Ordinal.omega.{0} 1 :=
    Ordinal.type_toType _
  exact lt_of_lt_of_eq (Ordinal.typein_lt_type (α := OmegaOne) (· < ·) i) htype

end ZFVP
