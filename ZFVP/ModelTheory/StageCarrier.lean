import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Logic.Equiv.Set
import ZFVP.SetTheory.DiamondOmegaOne

/-! Bookkeeping for an ω₁-length chain of countable models on one fixed carrier.

Enayat's ω₁-length construction (Appendix, Stage 1, condition (3)) asks that every stage of the
chain live on a subset of one fixed set of size `ℵ₁`. The successor step of that construction
hands back an abstract countable elementary extension `N` of the current stage, so `N` has to be
moved onto a countable subset of the carrier that extends the subset already used, in a way that
does not move the old points.

This file does that move. It is pure cardinal arithmetic together with one gluing of equivalences:
no set theory, no formulas. The carrier is any type `Ω` with `#Ω = ℵ₁`. -/

namespace ZFVP

open Cardinal

universe u v

/-- A countable subset of a carrier of size `ℵ₁` leaves `ℵ₁` many points outside it. If the
complement were smaller than `ℵ₁` then the whole carrier, a sum of two cardinals below the
infinite cardinal `ℵ₁`, would be below `ℵ₁` as well. -/
theorem alephOne_le_mk_compl {Ω : Type u} (hΩ : Cardinal.mk Ω = Cardinal.aleph 1)
    (A : Set Ω) (hA : A.Countable) : Cardinal.aleph 1 ≤ Cardinal.mk ↥(Aᶜ) := by
  by_contra hcon
  replace hcon : Cardinal.mk ↥(Aᶜ) < Cardinal.aleph 1 := not_le.mp hcon
  have hAc : Countable ↥A := hA.to_subtype
  have hA' : Cardinal.mk ↥A < Cardinal.aleph 1 :=
    lt_of_le_of_lt Cardinal.mk_le_aleph0 Cardinal.aleph0_lt_aleph_one
  have hsum := Cardinal.add_lt_of_lt (Cardinal.aleph0_le_aleph 1) hA' hcon
  rw [Cardinal.mk_sum_compl, hΩ] at hsum
  exact lt_irrefl _ hsum

/-- The complement of a countable subset of a carrier of size `ℵ₁` is infinite. -/
theorem infinite_compl {Ω : Type u} (hΩ : Cardinal.mk Ω = Cardinal.aleph 1)
    (A : Set Ω) (hA : A.Countable) : Infinite ↥(Aᶜ) := by
  rw [Cardinal.infinite_iff]
  exact le_trans (Cardinal.aleph0_le_aleph 1) (alephOne_le_mk_compl hΩ A hA)

/-- A carrier of size `ℵ₁` is infinite. -/
theorem infinite_of_mk_alephOne {Ω : Type u} (hΩ : Cardinal.mk Ω = Cardinal.aleph 1) :
    Infinite Ω := by
  rw [Cardinal.infinite_iff, hΩ]
  exact Cardinal.aleph0_le_aleph 1

/-- The gluing step, stated for an arbitrary ambient type. Given an injection `i` of `A` into `N`
and an injection `g` of the points of `N` missed by `i` into the complement of `A`, the set
`A ∪ range g` is in bijection with `N` by a bijection that agrees with `i` on `A`. -/
theorem exists_equiv_union_of_injective {Ω : Type u} {N : Type v} (A : Set Ω) (i : ↥A → N)
    (hi : Function.Injective i) (g : ↥((Set.range i)ᶜ) → Ω)
    (hg : Function.Injective g) (hgA : ∀ r, g r ∉ A) :
    ∃ e : ↥(A ∪ Set.range g) ≃ N,
      ∀ x : ↥A, e (Set.inclusion Set.subset_union_left x) = i x := by
  classical
  have hdisj : Disjoint A (Set.range g) := by
    refine Set.disjoint_left.mpr ?_
    rintro y hyA ⟨r, rfl⟩
    exact absurd hyA (hgA r)
  refine ⟨(Equiv.Set.union hdisj).trans
    ((Equiv.sumCongr (Equiv.ofInjective i hi) (Equiv.ofInjective g hg).symm).trans
      (Equiv.Set.sumCompl (Set.range i))), ?_⟩
  intro x
  rw [Equiv.trans_apply, Equiv.trans_apply,
    Equiv.Set.union_apply_left hdisj
      (a := Set.inclusion (Set.subset_union_left (s := A) (t := Set.range g)) x) x.2,
    Equiv.sumCongr_apply, Sum.map_inl, Equiv.Set.sumCompl_apply_inl, Equiv.ofInjective_apply]

/-- Transport of a countable elementary extension onto the fixed carrier. If the countable set `A`
of carrier points is already in use and `i` embeds it into the countable model `N`, then `N` can
be placed on a countable superset `B` of `A` so that the old points keep their meaning: the
bijection `e : B ≃ N` restricted to `A` is `i`. -/
theorem exists_carrier_extension {Ω : Type u} (hΩ : Cardinal.mk Ω = Cardinal.aleph 1)
    (A : Set Ω) (hA : A.Countable) (N : Type v) [Countable N] (i : ↥A → N)
    (hi : Function.Injective i) :
    ∃ (B : Set Ω) (hAB : A ⊆ B) (e : ↥B ≃ N),
      B.Countable ∧ ∀ x : ↥A, e (Set.inclusion hAB x) = i x := by
  have hinf : Infinite ↥(Aᶜ) := infinite_compl hΩ A hA
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat ↥((Set.range i)ᶜ)
  have hninj : Function.Injective (Infinite.natEmbedding ↥(Aᶜ)) :=
    (Infinite.natEmbedding ↥(Aᶜ)).injective
  set g : ↥((Set.range i)ᶜ) → Ω := fun r => ((Infinite.natEmbedding ↥(Aᶜ) (f r) : ↥(Aᶜ)) : Ω)
    with hgdef
  have hg : Function.Injective g := by
    intro a b hab
    exact hf (hninj (Subtype.ext hab))
  have hgA : ∀ r, g r ∉ A := fun r => (Infinite.natEmbedding ↥(Aᶜ) (f r)).2
  obtain ⟨e, he⟩ := exists_equiv_union_of_injective A i hi g hg hgA
  exact ⟨A ∪ Set.range g, Set.subset_union_left, e, hA.union (Set.countable_range g), he⟩

/-- The base case of the construction: a countable model can be placed on a countable subset of
the fixed carrier. -/
theorem exists_carrier_embedding {Ω : Type u} (hΩ : Cardinal.mk Ω = Cardinal.aleph 1)
    (N : Type v) [Countable N] : ∃ (B : Set Ω) (_ : ↥B ≃ N), B.Countable := by
  have hinf : Infinite Ω := infinite_of_mk_alephOne hΩ
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat N
  have hninj : Function.Injective (Infinite.natEmbedding Ω) := (Infinite.natEmbedding Ω).injective
  have h : Function.Injective fun x : N => Infinite.natEmbedding Ω (f x) :=
    fun a b hab => hf (hninj hab)
  exact ⟨Set.range fun x : N => Infinite.natEmbedding Ω (f x), (Equiv.ofInjective _ h).symm,
    Set.countable_range _⟩

end ZFVP
