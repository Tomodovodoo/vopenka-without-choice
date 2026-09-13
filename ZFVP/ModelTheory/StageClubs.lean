import ZFVP.ModelTheory.StageRun

/-! # Club sets of closure points for an ω₁-filtration

The reflection half of Enayat's ω₁-length construction needs to know that certain closure
conditions hold at club many indices. This file supplies three such facts, all built from one
lemma: the set of common closure points of countably many functions `ω₁ → ω₁` is a club
(`ZFVP.exists_club_closure_points`).

* `ZFVP.exists_club_closed`: a filtration by countable sets, continuous at limit indices, is closed
  under countably many finitary operations at club many indices.
* `ZFVP.exists_club_code_image`: along a bijection `ω₁ ≃ Ω`, the stage `A α` is exactly the image of
  the initial segment below `α` at club many indices.

`IsClub` and `IsStationary` are Mathlib's (`Mathlib/SetTheory/Cardinal/Cofinality/Club.lean`).
`ZFVP.IsClub.inter` and `ZFVP.IsStationary.exists_mem_club` are one line wrappers around the
Mathlib lemmas, specialised to `OmegaOne` so that callers do not have to supply the cofinality
side condition.
-/

namespace ZFVP

open Ordinal Set

universe u

/-! ## Basic facts about the index order `ω₁` -/

/-- The order type of `OmegaOne` is `ω₁`. -/
theorem type_omegaOne : Ordinal.type (α := OmegaOne) (· < ·) = Ordinal.omega.{0} 1 :=
  Ordinal.type_toType _

/-- Every index of `OmegaOne` has order type below `ω₁`. -/
theorem typein_lt_omegaOne (γ : OmegaOne) :
    Ordinal.typein (α := OmegaOne) (· < ·) γ < Ordinal.omega.{0} 1 :=
  lt_of_lt_of_eq (Ordinal.typein_lt_type (α := OmegaOne) (· < ·) γ) type_omegaOne

/-- An initial segment of `OmegaOne` is countable. -/
theorem countable_Iio_omegaOne (γ : OmegaOne) : (Set.Iio γ).Countable := by
  have h : Set.Iio γ = Ordinal.typein (α := OmegaOne) (· < ·) ⁻¹'
      Set.Iio (Ordinal.typein (α := OmegaOne) (· < ·) γ) := by
    ext β
    simp only [Set.mem_Iio, Set.mem_preimage, Ordinal.typein_lt_typein]
  rw [h]
  exact (Cardinal.countable_Iio_of_lt_omega_one (typein_lt_omegaOne γ)).preimage
    (Ordinal.typein_injective _)

/-- `OmegaOne` has no largest element. -/
theorem exists_gt_omegaOne (γ : OmegaOne) : ∃ δ : OmegaOne, γ < δ := by
  have hsucc : Order.succ (Ordinal.typein (α := OmegaOne) (· < ·) γ) < Ordinal.omega.{0} 1 :=
    (Cardinal.isSuccLimit_omega 1).succ_lt (typein_lt_omegaOne γ)
  have hsucc' : Order.succ (Ordinal.typein (α := OmegaOne) (· < ·) γ) <
      Ordinal.type (α := OmegaOne) (· < ·) := by
    rw [type_omegaOne]; exact hsucc
  refine ⟨Ordinal.enum (α := OmegaOne) (· < ·)
    ⟨Order.succ (Ordinal.typein (α := OmegaOne) (· < ·) γ), hsucc'⟩, ?_⟩
  refine (Ordinal.typein_lt_typein (α := OmegaOne) (· < ·)).mp ?_
  rw [Ordinal.typein_enum]
  exact Order.lt_succ _

/-- The cofinality of `OmegaOne` is `ℵ₁`, so in particular it is not `ℵ₀`. This is the side
condition of Mathlib's intersection lemmas for clubs. -/
theorem cof_omegaOne_ne_aleph0 : Order.cof OmegaOne ≠ Cardinal.aleph0 := by
  have h : Order.cof OmegaOne = Cardinal.aleph 1 := by
    rw [Ordinal.cof_toType, Cardinal.cof_omega_one]
  rw [h]
  exact (Cardinal.aleph0_lt_aleph_one).ne'

/-! ## The core closure lemma -/

/-- The set of common closure points of countably many functions `ω₁ → ω₁` is a club, and each of
its members is a limit index. -/
theorem exists_club_closure_points {ι : Type} [Countable ι] (η : ι → OmegaOne → OmegaOne) :
    ∃ C : Set OmegaOne, IsClub C ∧
      ∀ α ∈ C, IsLimitIndex α ∧ ∀ (i : ι) (β : OmegaOne), β < α → η i β < α := by
  -- One step: past `γ` there is an index bounding `η i β` for every `i` and every `β < γ`.
  have hstep : ∀ γ : OmegaOne, ∃ δ : OmegaOne, γ < δ ∧
      ∀ (i : ι) (β : OmegaOne), β < γ → η i β < δ := by
    intro γ
    have : Countable (Set.Iio γ) := (countable_Iio_omegaOne γ).to_subtype
    obtain ⟨k, hk⟩ := exists_upper_bound_of_countable
      (fun p : ι × Set.Iio γ ↦ η p.1 (p.2 : OmegaOne))
    obtain ⟨δ, hδ⟩ := exists_gt_omegaOne (max γ k)
    refine ⟨δ, lt_of_le_of_lt (le_max_left γ k) hδ, fun i β hβ ↦ ?_⟩
    exact lt_of_le_of_lt ((hk (i, ⟨β, hβ⟩)).trans (le_max_right γ k)) hδ
  choose next hnext_gt hnext_bound using hstep
  refine ⟨{α | IsLimitIndex α ∧ ∀ (i : ι) (β : OmegaOne), β < α → η i β < α},
    ⟨?_, ?_⟩, fun α hα ↦ hα⟩
  · -- Closed under suprema.
    intro d hd hd0 _ a ha
    have key : ∀ β : OmegaOne, β < a → ∃ b ∈ d, β < b := by
      intro β hβ
      by_contra hcon
      push_neg at hcon
      exact absurd (ha.2 (fun b hb ↦ hcon b hb)) (not_le.mpr hβ)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · obtain ⟨b, hb⟩ := hd0
      obtain ⟨c, hc⟩ := (hd hb).1.1
      exact ⟨c, lt_of_lt_of_le hc (ha.1 hb)⟩
    · intro β hβ
      obtain ⟨b, hbd, hβb⟩ := key β hβ
      rcases lt_or_eq_of_le (ha.1 hbd) with hba | hba
      · exact ⟨b, hβb, hba⟩
      · obtain ⟨c, hc1, hc2⟩ := (hd hbd).1.2 β hβb
        exact ⟨c, hc1, hba ▸ hc2⟩
    · intro i β hβ
      obtain ⟨b, hbd, hβb⟩ := key β hβ
      exact lt_of_lt_of_le ((hd hbd).2 i β hβb) (ha.1 hbd)
  · -- Cofinal: iterate `next` ω times and take the supremum.
    intro γ₀
    set g : ℕ → OmegaOne := fun n ↦ next^[n] γ₀ with hg
    have hgsucc : ∀ n, g n < g (n + 1) := by
      intro n
      have : g (n + 1) = next (g n) := by
        rw [hg]; exact Function.iterate_succ_apply' next n γ₀
      rw [this]
      exact hnext_gt (g n)
    have hs : (⨆ n : ℕ, Ordinal.typein (α := OmegaOne) (· < ·) (g n)) < Ordinal.omega.{0} 1 :=
      Ordinal.iSup_lt_omega_one (fun n ↦ typein_lt_omegaOne (g n))
    have hs' : (⨆ n : ℕ, Ordinal.typein (α := OmegaOne) (· < ·) (g n)) <
        Ordinal.type (α := OmegaOne) (· < ·) := by
      rw [type_omegaOne]; exact hs
    set α : OmegaOne := Ordinal.enum (α := OmegaOne) (· < ·) ⟨_, hs'⟩ with hαdef
    have hαtypein : Ordinal.typein (α := OmegaOne) (· < ·) α =
        ⨆ n : ℕ, Ordinal.typein (α := OmegaOne) (· < ·) (g n) := by
      rw [hαdef, Ordinal.typein_enum]
    have hgα : ∀ n, g n < α := by
      intro n
      refine (Ordinal.typein_lt_typein (α := OmegaOne) (· < ·)).mp ?_
      rw [hαtypein]
      refine lt_of_lt_of_le ?_ (Ordinal.le_iSup _ (n + 1))
      exact (Ordinal.typein_lt_typein (α := OmegaOne) (· < ·)).mpr (hgsucc n)
    have hbelow : ∀ β : OmegaOne, β < α → ∃ n, β < g n := by
      intro β hβ
      have h1 : Ordinal.typein (α := OmegaOne) (· < ·) β <
          ⨆ n : ℕ, Ordinal.typein (α := OmegaOne) (· < ·) (g n) := by
        rw [← hαtypein]
        exact (Ordinal.typein_lt_typein (α := OmegaOne) (· < ·)).mpr hβ
      obtain ⟨n, hn⟩ := Ordinal.lt_iSup_iff.mp h1
      exact ⟨n, (Ordinal.typein_lt_typein (α := OmegaOne) (· < ·)).mp hn⟩
    refine ⟨α, ⟨⟨⟨g 0, hgα 0⟩, fun β hβ ↦ ?_⟩, fun i β hβ ↦ ?_⟩, ?_⟩
    · obtain ⟨n, hn⟩ := hbelow β hβ
      exact ⟨g n, hn, hgα n⟩
    · obtain ⟨n, hn⟩ := hbelow β hβ
      have h2 : η i β < next (g n) := hnext_bound (g n) i β hn
      have h3 : g (n + 1) = next (g n) := by
        rw [hg]; exact Function.iterate_succ_apply' next n γ₀
      exact lt_trans (h3 ▸ h2) (hgα (n + 1))
    · have h0 : g 0 = γ₀ := rfl
      exact le_of_lt (h0 ▸ hgα 0)

/-! ## Closure of a filtration under countably many finitary operations -/

/-- A filtration by countable sets, continuous at limit indices, is closed under countably many
finitary operations at club many indices. -/
theorem exists_club_closed {Ω : Type u} (A : OmegaOne → Set Ω) (hmono : Monotone A)
    (hcount : ∀ α, (A α).Countable) (hcover : ∀ x : Ω, ∃ α, x ∈ A α)
    (hlim : ∀ α, IsLimitIndex α → A α = {x | ∃ β, β < α ∧ x ∈ A β})
    {ι : Type} [Countable ι] (k : ι → ℕ) (g : ∀ i, (Fin (k i) → Ω) → Ω) :
    ∃ C : Set OmegaOne, IsClub C ∧ ∀ α ∈ C, ∀ (i : ι) (v : Fin (k i) → Ω),
      (∀ j, v j ∈ A α) → g i v ∈ A α := by
  classical
  choose w hw using hcover
  -- One index past `β` holding every value of every operation on tuples from `A β`.
  have hstep : ∀ β : OmegaOne, ∃ δ : OmegaOne,
      ∀ (i : ι) (v : Fin (k i) → Ω), (∀ j, v j ∈ A β) → g i v ∈ A δ := by
    intro β
    have : Countable (A β) := (hcount β).to_subtype
    obtain ⟨δ, hδ⟩ := exists_upper_bound_of_countable
      (fun p : Σ i : ι, Fin (k i) → (A β) ↦ w (g p.1 (fun j ↦ ((p.2 j : Ω)))))
    refine ⟨δ, fun i v hv ↦ ?_⟩
    exact hmono (hδ ⟨i, fun j ↦ ⟨v j, hv j⟩⟩) (hw (g i v))
  choose η hη using hstep
  obtain ⟨C, hC, hCmem⟩ := exists_club_closure_points (ι := Unit) (fun _ ↦ η)
  refine ⟨C, hC, fun α hα i v hv ↦ ?_⟩
  obtain ⟨hlimα, hclos⟩ := hCmem α hα
  obtain ⟨β₀, hβ₀⟩ := hlimα.1
  have hb : ∀ j, ∃ b : OmegaOne, b < α ∧ v j ∈ A b := by
    intro j
    have hvj := hv j
    rw [hlim α hlimα] at hvj
    exact hvj
  choose b hb1 hb2 using hb
  set T : Finset OmegaOne := insert β₀ (Finset.image b Finset.univ) with hT
  have hTne : T.Nonempty := ⟨β₀, by rw [hT]; exact Finset.mem_insert_self _ _⟩
  have hβα : T.max' hTne < α := by
    rw [Finset.max'_lt_iff]
    intro y hy
    rw [hT, Finset.mem_insert] at hy
    rcases hy with h | h
    · exact h ▸ hβ₀
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp h
      exact hb1 j
  have hvβ : ∀ j, v j ∈ A (T.max' hTne) := by
    intro j
    refine hmono (Finset.le_max' T (b j) ?_) (hb2 j)
    rw [hT]
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem b (Finset.mem_univ j))
  exact hmono (le_of_lt (hclos () _ hβα)) (hη _ i v hvβ)

/-! ## The filtration as an initial segment along a bijection -/

/-- Along a bijection `e : ω₁ ≃ Ω`, the stage `A α` is exactly the image under `e` of the initial
segment below `α`, at club many indices. -/
theorem exists_club_code_image {Ω : Type u} (e : OmegaOne ≃ Ω) (A : OmegaOne → Set Ω)
    (hmono : Monotone A) (hcount : ∀ α, (A α).Countable) (hcover : ∀ x : Ω, ∃ α, x ∈ A α)
    (hlim : ∀ α, IsLimitIndex α → A α = {x | ∃ β, β < α ∧ x ∈ A β}) :
    ∃ C : Set OmegaOne, IsClub C ∧ ∀ α ∈ C, A α = e '' {β : OmegaOne | β < α} := by
  -- An index strictly above every code of an element of `A β`.
  have h1 : ∀ β : OmegaOne, ∃ δ : OmegaOne, ∀ x ∈ A β, e.symm x < δ := by
    intro β
    have : Countable (A β) := (hcount β).to_subtype
    obtain ⟨k, hk⟩ := exists_upper_bound_of_countable (fun x : A β ↦ e.symm (x : Ω))
    obtain ⟨δ, hδ⟩ := exists_gt_omegaOne k
    exact ⟨δ, fun x hx ↦ lt_of_le_of_lt (hk ⟨x, hx⟩) hδ⟩
  choose η₁ hη₁ using h1
  have h2 : ∀ β : OmegaOne, ∃ δ : OmegaOne, e β ∈ A δ := fun β ↦ hcover (e β)
  choose η₂ hη₂ using h2
  obtain ⟨C, hC, hCmem⟩ := exists_club_closure_points (ι := Bool)
    (fun i ↦ Bool.rec (motive := fun _ ↦ OmegaOne → OmegaOne) η₂ η₁ i)
  refine ⟨C, hC, fun α hα ↦ ?_⟩
  obtain ⟨hlimα, hclos⟩ := hCmem α hα
  apply Set.Subset.antisymm
  · intro x hx
    rw [hlim α hlimα] at hx
    obtain ⟨β, hβα, hxβ⟩ := hx
    exact ⟨e.symm x, lt_trans (hη₁ β x hxβ) (hclos true β hβα), e.apply_symm_apply x⟩
  · rintro _ ⟨β, hβ, rfl⟩
    exact hmono (le_of_lt (hclos false β hβ)) (hη₂ β)

/-! ## Intersections -/

/-- The intersection of two clubs in `ω₁` is a club. Wrapper around Mathlib's `IsClub.inter`,
which asks for the cofinality side condition. -/
theorem IsClub.inter {C D : Set OmegaOne} (hC : IsClub C) (hD : IsClub D) : IsClub (C ∩ D) :=
  _root_.IsClub.inter cof_omegaOne_ne_aleph0 hC hD

/-- A stationary set meets every club. This is the definition of `IsStationary`, restated in the
form callers use. -/
theorem IsStationary.exists_mem_club {S C : Set OmegaOne} (hS : IsStationary S) (hC : IsClub C) :
    ∃ α, α ∈ S ∧ α ∈ C := by
  obtain ⟨α, hα⟩ := hS hC
  exact ⟨α, hα.1, hα.2⟩

end ZFVP
