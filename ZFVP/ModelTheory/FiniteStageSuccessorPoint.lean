import ZFVP.ModelTheory.StageSuccessorPoint
import ZFVP.ModelTheory.FiniteStageSuccessorAll

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

/-- Absorbing a prescribed carrier point while preserving all old internally finite sets. -/
theorem exists_finite_stage_successor_point {Ω : Type u} (hΩ : Cardinal.mk Ω = Cardinal.aleph 1)
    (S : StageModel Ω) (hcount : S.carrier.Countable) [Nonempty ↥S.carrier]
    [(↥S.carrier)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (O : Set (Set Ω × Set Ω)) (hO : O.Countable)
    (hOsub : ∀ p ∈ O, p.1 ⊆ S.carrier ∧ p.2 ⊆ S.carrier) (x₀ : Ω) :
    ∃ (T : StageModel Ω) (hsub : S.carrier ⊆ T.carrier),
      T.carrier.Countable ∧ x₀ ∈ T.carrier ∧
      (∀ a : ↥S.carrier, IsInternallyFinite a → ∀ b : ↥T.carrier,
        b ∈ StageModel.incl hsub a → ∃ m ∈ a, StageModel.incl hsub m = b) ∧
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
  obtain ⟨T, hsub, hTc, hfinite, hmem, ⟨j, hj⟩, hins, hbnd⟩ :=
    exists_finite_stage_successor_all hΩ S hcount O hO hOsub
  by_cases hx₀T : x₀ ∈ T.carrier
  · exact ⟨T, hsub, hTc, hx₀T, hfinite, hmem, ⟨j, hj⟩, hins, hbnd⟩
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
  refine ⟨T', hsub', hTc.image σ, hx₀', ?_, ?_, ⟨(StageModel.ofEquivSymmMap B e).comp j, ?_⟩, ?_, ?_⟩
  · intro a ha b hb
    have hb' : e' b ∈ StageModel.incl hsub a := by
      rw [← hcompat a]
      exact hb
    obtain ⟨m, hm, heq⟩ := hfinite a ha (e' b) hb'
    exact ⟨m, hm, e'.injective (by rw [hcompat]; exact heq)⟩
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
