import Foundation.FirstOrder.SetTheory.Ordinal
import Foundation.FirstOrder.SetTheory.ZF
import ZFVP.ModelTheory.StageSuccessorAll

/-! # The successor step absorbs a prescribed point of the carrier

Condition (3) of Stage 1 in Enayat's Appendix asks that each successor stage reach strictly
further into the fixed carrier, so that the `ω₁`-chain of stages exhausts it. The successor step
`ZFVP.exists_stage_successor_all` produces a countable extension `T` of `S`, but the points it adds
are wherever the carrier transport happened to put them. This file adds the missing control.

* `ZFVP.exists_new_point` says the successor step is proper: the extension always has a point
  outside the old carrier. The reason is that the ordinals of `S` form a definable directed set
  with no last element, so the upper bound clause hands out an element of `T` strictly above the
  image of every ordinal of `S`, and such an element cannot be the image of an old point.
* `ZFVP.exists_stage_successor_point` is the successor step with a prescribed point `x₀` of the
  carrier put into the new stage. It calls `exists_stage_successor_all`, and if `x₀` was missed it
  relabels the carrier by the transposition swapping `x₀` with a new point of `T`. The
  transposition fixes `S.carrier` pointwise, so every clause survives the relabelling.

The ordinals are described here by the parameter free sentences `IsOrdinal.dfn` and `SSubset.dfn`
of the Foundation library, embedded into formulas with parameters from `S`. Two things come for
free that way: the reading of the two formulas inside `T` does not depend on the parameter map, and
elementarity of the inclusion is used only at formulas whose free variables are indexed by `Empty`,
so no universe juggling is needed.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

/-! ## The successor step adds a point -/

/-- Relabelling a subset of the carrier along a bijection of the carrier: a point of `σ '' B` read
as the point of `B` it came from. -/
def imageEquiv {Ω : Type u} (σ : Ω ≃ Ω) (B : Set Ω) : ↥(σ '' B) ≃ ↥B where
  toFun x := ⟨σ.symm x, by
    obtain ⟨a, ha, hax⟩ := x.2
    rw [← hax]
    simpa using ha⟩
  invFun a := ⟨σ a, ⟨a, a.2, rfl⟩⟩
  left_inv x := Subtype.ext (by simp)
  right_inv a := Subtype.ext (by simp)

@[simp] theorem coe_imageEquiv {Ω : Type u} (σ : Ω ≃ Ω) (B : Set Ω) (x : ↥(σ '' B)) :
    ((imageEquiv σ B x : ↥B) : Ω) = σ.symm (x : Ω) := rfl

/-- The successor step of Enayat's construction is proper: an extension `T` of `S` satisfying the
upper bound clause has a point outside `S.carrier`.

Inside `S`, which models ZF, the ordinals form a definable directed set with no last element: the
empty set is an ordinal, inclusion is total on ordinals, and the successor of an ordinal is a
strictly larger ordinal. The upper bound clause therefore gives a `t` in `T` satisfying the
ordinal formula and lying strictly above the image of every ordinal of `S`. If `t` were the image
of a point `m₀` of `S`, elementarity would make `m₀` an ordinal of `S`, and the bound at `m₀`
would say `t ⊊ t`. -/
theorem exists_new_point {Ω : Type u} (S T : StageModel Ω) (hsub : S.carrier ⊆ T.carrier)
    [Nonempty ↥S.carrier] [(↥S.carrier)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (j : ElementaryMap ↥S.carrier ↥T.carrier) (hj : ∀ x, j x = StageModel.incl hsub x)
    (hbound : ∀ (dφ : SetTheorySemiformula ↥S.carrier 1) (rφ : SetTheorySemiformula ↥S.carrier 2),
      DirectedNoLast (fun x ↦ dφ.Eval ![x] id) (fun x y ↦ rφ.Eval ![x, y] id) →
      ∃ t : ↥T.carrier, dφ.Eval ![t] (fun m ↦ StageModel.incl hsub m) ∧
        ∀ m : ↥S.carrier, dφ.Eval ![m] id →
          rφ.Eval ![StageModel.incl hsub m, t] (fun m ↦ StageModel.incl hsub m)) :
    ∃ y, y ∈ T.carrier ∧ y ∉ S.carrier := by
  classical
  -- the ordinals of `S`, ordered by strict inclusion, are directed with no last element
  have hdir : DirectedNoLast
      (fun x : ↥S.carrier ↦
        (Rewriting.emb IsOrdinal.dfn : SetTheorySemiformula ↥S.carrier 1).Eval ![x] id)
      (fun x y : ↥S.carrier ↦
        (Rewriting.emb SSubset.dfn : SetTheorySemiformula ↥S.carrier 2).Eval ![x, y] id) := by
    have hD : ∀ x : ↥S.carrier,
        (Rewriting.emb IsOrdinal.dfn : SetTheorySemiformula ↥S.carrier 1).Eval ![x] id ↔
          IsOrdinal x := by
      intro x; simp
    have hR : ∀ x y : ↥S.carrier,
        (Rewriting.emb SSubset.dfn : SetTheorySemiformula ↥S.carrier 2).Eval ![x, y] id ↔
          x ⊊ y := by
      intro x y; simp
    refine ⟨⟨∅, (hD ∅).mpr inferInstance⟩, ?_, ?_⟩
    · intro x y z hx hy hz hxy hyz
      rw [hR] at hxy hyz ⊢
      refine ⟨subset_trans hxy.1 hyz.1, fun hxz ↦ hyz.2 ?_⟩
      exact subset_antisymm hyz.1 (hxz ▸ hxy.1)
    · intro x y hx hy
      have hx' : IsOrdinal x := (hD x).mp hx
      have hy' : IsOrdinal y := (hD y).mp hy
      obtain ⟨w, hw, hxw, hyw⟩ : ∃ w : ↥S.carrier, IsOrdinal w ∧ x ⊆ w ∧ y ⊆ w := by
        rcases IsOrdinal.subset_or_supset (α := x) (β := y) with h | h
        · exact ⟨y, hy', h, subset_refl y⟩
        · exact ⟨x, hx', subset_refl x, h⟩
      have hws : w ⊆ succ w := fun z hz ↦ mem_succ_iff.mpr (Or.inr hz)
      have hsub' : ∀ u : ↥S.carrier, u ⊆ w → u ⊊ succ w := by
        intro u hu
        refine ⟨subset_trans hu hws, fun huw ↦ ?_⟩
        exact mem_irrefl w (hu w (huw ▸ mem_succ_self w))
      refine ⟨succ w, (hD _).mpr (by have := hw; exact IsOrdinal.succ), ?_, ?_⟩ <;>
        rw [hR]
      · exact hsub' x hxw
      · exact hsub' y hyw
  obtain ⟨t, ht, htb⟩ := hbound _ _ hdir
  refine ⟨(t : Ω), t.2, fun htS ↦ ?_⟩
  -- if the witness were an old point, elementarity would make it an ordinal of `S`
  set m₀ : ↥S.carrier := ⟨(t : Ω), htS⟩ with hm₀
  have hincl : StageModel.incl hsub m₀ = t := Subtype.ext rfl
  have hjm : j m₀ = t := by rw [hj, hincl]
  have htord : Semiformula.Evalb ![t] (IsOrdinal.dfn : SetTheorySemisentence 1) := by
    rw [← Semiformula.eval_emb (ξ := ↥S.carrier) (f := fun m ↦ StageModel.incl hsub m)]
    exact ht
  have hm₀ord : IsOrdinal m₀ := by
    have helem := j.elementary (IsOrdinal.dfn : SetTheorySemisentence 1) ![m₀]
      (Empty.elim : Empty → ↥S.carrier)
    have hb : (⇑j ∘ ![m₀]) = ![t] := by rw [comp_vec_one, hjm]
    have hf : (⇑j ∘ (Empty.elim : Empty → ↥S.carrier)) = (Empty.elim : Empty → ↥T.carrier) := by
      funext i; exact i.elim
    rw [hb, hf] at helem
    have : Semiformula.Evalb ![m₀] (IsOrdinal.dfn : SetTheorySemisentence 1) := helem.mpr htord
    simpa using this
  have hlt := htb m₀ (by simpa using hm₀ord)
  rw [hincl] at hlt
  simp at hlt

/-! ## The successor step with a prescribed point -/

/-- The successor step of Enayat's `ω₁`-length construction, with one point `x₀` of the carrier
required to be in the new stage.

This is `ZFVP.exists_stage_successor_all` followed, when `x₀` was missed, by the relabelling of the
carrier along the transposition of `x₀` with a point of `T` outside `S.carrier`, which
`ZFVP.exists_new_point` provides. The transposition fixes `S.carrier` pointwise, so it carries the
membership relation of `T` to a stage with the same properties over the same `S`. -/
theorem exists_stage_successor_point {Ω : Type u} (hΩ : Cardinal.mk Ω = Cardinal.aleph 1)
    (S : StageModel Ω) (hcount : S.carrier.Countable) [Nonempty ↥S.carrier]
    [(↥S.carrier)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (O : Set (Set Ω × Set Ω)) (hO : O.Countable)
    (hOsub : ∀ p ∈ O, p.1 ⊆ S.carrier ∧ p.2 ⊆ S.carrier) (x₀ : Ω) :
    ∃ (T : StageModel Ω) (hsub : S.carrier ⊆ T.carrier),
      T.carrier.Countable ∧ x₀ ∈ T.carrier ∧
      (∀ x y : ↥S.carrier, x ∈ y ↔ StageModel.incl hsub x ∈ StageModel.incl hsub y) ∧
      (∃ j : ElementaryMap ↥S.carrier ↥T.carrier, ∀ x, j x = StageModel.incl hsub x) ∧
      (∀ p ∈ O, Inseparable ↥S.carrier (fun x ↦ (x : Ω) ∈ p.1) (fun x ↦ (x : Ω) ∈ p.2) →
        Inseparable ↥T.carrier (fun y ↦ (y : Ω) ∈ p.1) (fun y ↦ (y : Ω) ∈ p.2)) ∧
      (∀ (dφ : SetTheorySemiformula ↥S.carrier 1) (rφ : SetTheorySemiformula ↥S.carrier 2),
        DirectedNoLast (fun x ↦ dφ.Eval ![x] id) (fun x y ↦ rφ.Eval ![x, y] id) →
        ∃ t : ↥T.carrier,
          dφ.Eval ![t] (fun m ↦ StageModel.incl hsub m) ∧
          ∀ m : ↥S.carrier, dφ.Eval ![m] id →
            rφ.Eval ![StageModel.incl hsub m, t] (fun m ↦ StageModel.incl hsub m)) := by
  classical
  obtain ⟨T, hsub, hTc, hmem, ⟨j, hj⟩, hins, hbnd⟩ :=
    exists_stage_successor_all hΩ S hcount O hO hOsub
  by_cases hx₀T : x₀ ∈ T.carrier
  · exact ⟨T, hsub, hTc, hx₀T, hmem, ⟨j, hj⟩, hins, hbnd⟩
  obtain ⟨y₀, hy₀T, hy₀S⟩ := exists_new_point S T hsub j hj hbnd
  have hx₀S : x₀ ∉ S.carrier := fun h ↦ hx₀T (hsub h)
  set σ : Ω ≃ Ω := Equiv.swap y₀ x₀ with hσ
  have hσsymm : σ.symm = σ := by rw [hσ, Equiv.symm_swap]
  have hfix : ∀ a ∈ S.carrier, σ a = a := by
    intro a ha
    exact Equiv.swap_apply_of_ne_of_ne (fun h ↦ hy₀S (h ▸ ha)) (fun h ↦ hx₀S (h ▸ ha))
  have hfixsymm : ∀ a ∈ S.carrier, σ.symm a = a := by
    intro a ha; rw [hσsymm]; exact hfix a ha
  -- the relabelled stage
  set B : Set Ω := σ '' T.carrier with hB
  set e : ↥B ≃ ↥T.carrier := imageEquiv σ T.carrier with he
  set T' : StageModel Ω := StageModel.ofEquiv B e with hT'
  set e' : ↥T'.carrier ≃ ↥T.carrier := StageModel.ofEquivEquiv B e with he'
  have hiso' : ∀ x y : ↥T'.carrier, e' x ∈ e' y ↔ x ∈ y := fun _ _ ↦ Iff.rfl
  have hcoe : ∀ y : ↥T'.carrier, ((e' y : ↥T.carrier) : Ω) = σ.symm (y : Ω) := fun _ ↦ rfl
  have hsub' : S.carrier ⊆ T'.carrier := fun a ha ↦ ⟨a, hsub ha, hfix a ha⟩
  have hx₀' : x₀ ∈ T'.carrier := ⟨y₀, hy₀T, by rw [hσ]; exact Equiv.swap_apply_left y₀ x₀⟩
  have hcompat : ∀ a : ↥S.carrier,
      e' (StageModel.incl (S := S) (T := T') hsub' a) = StageModel.incl hsub a := by
    intro a
    apply Subtype.ext
    show σ.symm (a : Ω) = (a : Ω)
    exact hfixsymm (a : Ω) a.2
  have hcomp : (⇑e' ∘ fun m : ↥S.carrier ↦ StageModel.incl (S := S) (T := T') hsub' m) =
      fun m ↦ StageModel.incl hsub m := funext hcompat
  -- a subset of `S.carrier` is not moved by the relabelling
  have hkey : ∀ P : Set Ω, P ⊆ S.carrier → ∀ y : ↥T'.carrier,
      ((y : Ω) ∈ P ↔ ((e' y : ↥T.carrier) : Ω) ∈ P) := by
    intro P hP y
    rw [hcoe y]
    constructor
    · intro hy; rw [hfixsymm (y : Ω) (hP hy)]; exact hy
    · intro hy
      have h1 : σ.symm ((y : Ω)) = (y : Ω) := by
        have h2 : σ.symm (σ.symm (y : Ω)) = σ.symm (y : Ω) := hfixsymm _ (hP hy)
        have h3 : σ.symm (σ.symm (y : Ω)) = (y : Ω) := by
          rw [hσsymm, hσ]; exact Equiv.swap_apply_self y₀ x₀ (y : Ω)
        rw [h3] at h2
        exact h2.symm
      rw [h1] at hy
      exact hy
  refine ⟨T', hsub', hTc.image σ, hx₀', ?_, ⟨(StageModel.ofEquivSymmMap B e).comp j, ?_⟩, ?_, ?_⟩
  · intro x y
    rw [hmem x y, ← hcompat x, ← hcompat y]
    exact Iff.rfl
  · intro x
    show e'.symm (j x) = StageModel.incl (S := S) (T := T') hsub' x
    rw [hj x, ← hcompat x, Equiv.symm_apply_apply]
  · intro p hp hpins
    exact ((hins p hp hpins).comp_memEquiv e' hiso').congr
      (hkey p.1 (hOsub p hp).1) (hkey p.2 (hOsub p hp).2)
  · intro dφ rφ hdd
    obtain ⟨t, ht, htb⟩ := hbnd dφ rφ hdd
    refine ⟨e'.symm t, ?_, fun m hm ↦ ?_⟩
    · rw [eval_membershipIso e' hiso' dφ ![e'.symm t]
          (fun m ↦ StageModel.incl (S := S) (T := T') hsub' m),
        comp_vec_one, Equiv.apply_symm_apply, hcomp]
      exact ht
    · rw [eval_membershipIso e' hiso' rφ
          ![StageModel.incl (S := S) (T := T') hsub' m, e'.symm t]
          (fun m ↦ StageModel.incl (S := S) (T := T') hsub' m),
        comp_vec_two, hcompat m, Equiv.apply_symm_apply, hcomp]
      exact htb m hm

end ZFVP
