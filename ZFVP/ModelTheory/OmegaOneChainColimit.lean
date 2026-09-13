import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular
import ZFVP.ModelTheory.ElementaryChain
import ZFVP.SetTheory.DiamondOmegaOne

/-! Cardinality of the colimit of an ω₁-chain of countable models.

Enayat's Theorem 5.17 builds a model of size `ℵ₁` as the union of an increasing ω₁-chain of
countable elementary extensions. This file does the counting for that union: the colimit of an
ω₁-indexed elementary chain of countable models has size at most `ℵ₁`, it has size at least `ℵ₁`
as soon as no single stage already exhausts the colimit cofinally often, and so it has size
exactly `ℵ₁`. -/

namespace ZFVP

open Cardinal

/-- A countable family of elements of `ω₁` has an upper bound in `ω₁`: `ω₁` is regular, so the
supremum of countably many ordinals below `ω₁` is again below `ω₁`. -/
theorem exists_upper_bound_of_countable {α : Type*} [Countable α] (f : α → OmegaOne) :
    ∃ k : OmegaOne, ∀ a, f a ≤ k := by
  have htype : Ordinal.type (α := OmegaOne) (· < ·) = Ordinal.omega.{0} 1 :=
    Ordinal.type_toType _
  set g : α → Ordinal.{0} := fun a ↦ Ordinal.typein (α := OmegaOne) (· < ·) (f a) with hg
  have hlt : ∀ a, g a < Ordinal.omega.{0} 1 := fun a ↦
    lt_of_lt_of_eq (Ordinal.typein_lt_type (α := OmegaOne) (· < ·) (f a)) htype
  have hs : (⨆ a, g a) < Ordinal.omega.{0} 1 := Ordinal.iSup_lt_omega_one hlt
  have hs' : (⨆ a, g a) < Ordinal.type (α := OmegaOne) (· < ·) := lt_of_lt_of_eq hs htype.symm
  refine ⟨Ordinal.enum (α := OmegaOne) (· < ·) ⟨⨆ a, g a, hs'⟩, fun a ↦ ?_⟩
  refine (Ordinal.typein_le_typein' (o := Ordinal.omega.{0} 1)).mp ?_
  rw [Ordinal.typein_enum]
  exact Ordinal.le_iSup g a

/-- The colimit of an ω₁-chain of countable models has at most `ℵ₁` elements. -/
theorem mk_chainColimit_le_alephOne (C : ElementaryChain OmegaOne)
    (hcount : ∀ i, Countable (C.Model i)) :
    Cardinal.mk (ElementaryChain.ChainColimit C) ≤ Cardinal.aleph 1 := by
  refine le_trans (ElementaryChain.ChainColimit.mk_le C) ?_
  have h1 : Cardinal.sum (fun i : OmegaOne ↦ Cardinal.mk (C.Model i))
      ≤ Cardinal.sum (fun _ : OmegaOne ↦ Cardinal.aleph0) := by
    refine Cardinal.sum_le_sum _ _ fun i ↦ ?_
    have := hcount i
    exact Cardinal.mk_le_aleph0
  rw [Cardinal.sum_const', mk_omegaOne,
    Cardinal.mul_eq_left (Cardinal.aleph0_le_aleph 1) (Cardinal.aleph0_le_aleph 1)
      Cardinal.aleph0_ne_zero] at h1
  exact h1

/-- If the chain keeps growing, in the sense that above every stage there is a later stage with an
element that is not the image of anything from the earlier one, then the colimit has at least `ℵ₁`
elements. If it had fewer it would be countable, and then the countably many stages needed to name
its elements would be bounded by a single stage `k`, since `ω₁` is regular; but then no later stage
could contain a new element. -/
theorem alephOne_le_mk_chainColimit (C : ElementaryChain OmegaOne)
    (hgrow : ∀ i : OmegaOne, ∃ j : OmegaOne, ∃ h : i < j, ∃ x : C.Model j,
      ∀ y : C.Model i, C.map h.le y ≠ x) :
    Cardinal.aleph 1 ≤ Cardinal.mk (ElementaryChain.ChainColimit C) := by
  by_contra hcon
  rw [not_le] at hcon
  have hc : Countable (ElementaryChain.ChainColimit C) :=
    Cardinal.mk_le_aleph0_iff.mp (Cardinal.lt_aleph_one_iff.mp hcon)
  choose σ w hw using ElementaryChain.ChainColimit.exists_mk C
  obtain ⟨k, hk⟩ := exists_upper_bound_of_countable σ
  have hsurj : ∀ z, ∃ y : C.Model k, ElementaryChain.ChainColimit.mk C k y = z := by
    intro z
    refine ⟨C.map (hk z) (w z), ?_⟩
    rw [ElementaryChain.ChainColimit.mk_map]
    exact (hw z).symm
  obtain ⟨j, hkj, x, hx⟩ := hgrow k
  obtain ⟨y, hy⟩ := hsurj (ElementaryChain.ChainColimit.mk C j x)
  have hxy := (ElementaryChain.ChainColimit.mk_eq_iff y x hkj.le (le_refl j)).mp hy
  rw [C.map_apply_self j (le_refl j)] at hxy
  exact hx y hxy

/-- The colimit of an ω₁-chain of countable models that keeps growing has exactly `ℵ₁`
elements. -/
theorem mk_chainColimit_eq_alephOne (C : ElementaryChain OmegaOne)
    (hcount : ∀ i, Countable (C.Model i))
    (hgrow : ∀ i : OmegaOne, ∃ j : OmegaOne, ∃ h : i < j, ∃ x : C.Model j,
      ∀ y : C.Model i, C.map h.le y ≠ x) :
    Cardinal.mk (ElementaryChain.ChainColimit C) = Cardinal.aleph 1 :=
  le_antisymm (mk_chainColimit_le_alephOne C hcount) (alephOne_le_mk_chainColimit C hgrow)

end ZFVP
