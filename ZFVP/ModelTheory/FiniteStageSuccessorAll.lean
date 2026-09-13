import ZFVP.ModelTheory.StageSuccessorAll
import ZFVP.ModelTheory.FiniteStageObligations

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

/-- The stage successor also preserves the members of every old internally finite set. -/
theorem exists_finite_stage_successor_all {Ω : Type u} (hΩ : Cardinal.mk Ω = Cardinal.aleph 1)
    (S : StageModel Ω) (hcount : S.carrier.Countable) [Nonempty ↥S.carrier] [(↥S.carrier)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (O : Set (Set Ω × Set Ω)) (hO : O.Countable)
    (hOsub : ∀ p ∈ O, p.1 ⊆ S.carrier ∧ p.2 ⊆ S.carrier) :
    ∃ (T : StageModel Ω) (hsub : S.carrier ⊆ T.carrier),
      T.carrier.Countable ∧
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
  have : Countable ↥S.carrier := hcount.to_subtype
  -- the pairs of `O` that are inseparable in `S`, read as pairs of predicates on `↥S.carrier`
  set F : Set Ω × Set Ω → (↥S.carrier → Prop) × (↥S.carrier → Prop) := fun p ↦
    (fun x : ↥S.carrier ↦ (x : Ω) ∈ p.1, fun x : ↥S.carrier ↦ (x : Ω) ∈ p.2) with hFdef
  set O₀ : Set (Set Ω × Set Ω) :=
    {p | p ∈ O ∧ Inseparable ↥S.carrier (F p).1 (F p).2} with hO₀def
  have hO₀ : O₀.Countable := hO.mono fun p hp ↦ hp.1
  obtain ⟨N, _, _, _, j, hfinite, hins, hbound⟩ :=
    exists_finite_extension_all_directed (M := ↥S.carrier) (F '' O₀) (hO₀.image F)
      (by rintro q ⟨p, hp, rfl⟩; exact hp.2)
  obtain ⟨B, hAB, e, hBcount, hcompat⟩ :=
    exists_carrier_extension hΩ S.carrier hcount N (fun x ↦ j x) j.injective
  -- the new stage and its bijection with the model coming from Lemma A.2
  set T : StageModel Ω := StageModel.ofEquiv B e with hT
  set e' : ↥T.carrier ≃ N := StageModel.ofEquivEquiv B e with he'
  have hcompat' : ∀ x : ↥S.carrier,
      e' (StageModel.incl (S := S) (T := T) hAB x) = j x := hcompat
  have hiso' : ∀ x y : ↥T.carrier, e' x ∈ e' y ↔ x ∈ y := fun _ _ ↦ Iff.rfl
  have hcomp : (⇑e' ∘ fun m : ↥S.carrier ↦ StageModel.incl (S := S) (T := T) hAB m) =
      fun m ↦ j m := funext hcompat'
  -- a subset of `S.carrier`, read in `T`, is the image along the inclusion of its reading in `S`
  have key : ∀ P : Set Ω, P ⊆ S.carrier → ∀ y : ↥T.carrier,
      ((y : Ω) ∈ P ↔ ∃ a : ↥S.carrier, (a : Ω) ∈ P ∧ e' y = j a) := by
    intro P hPsub y
    constructor
    · intro hy
      have hyS : (y : Ω) ∈ S.carrier := hPsub hy
      refine ⟨⟨(y : Ω), hyS⟩, hy, ?_⟩
      have hyy : StageModel.incl (S := S) (T := T) hAB ⟨(y : Ω), hyS⟩ = y := Subtype.ext rfl
      rw [← hcompat', hyy]
    · rintro ⟨a, ha, hya⟩
      have hy : y = StageModel.incl (S := S) (T := T) hAB a :=
        e'.injective (by rw [hya, hcompat'])
      rw [hy]
      exact ha
  refine ⟨T, hAB, hBcount, ?_, ?_, ⟨(StageModel.ofEquivSymmMap B e).comp j, fun x ↦ ?_⟩, ?_, ?_⟩
  · intro a ha b hb
    have hb' : e' b ∈ j a := by
      rw [← hcompat' a]
      exact hb
    obtain ⟨m, hm, heq⟩ := hfinite a ha (e' b) hb'
    exact ⟨m, hm, e'.injective (by rw [hcompat']; exact heq)⟩
  · intro x y
    rw [StageModel.ofEquiv_mem_iff, ← he', hcompat' x, hcompat' y, j.map_mem_iff]
  · show e'.symm (j x) = StageModel.incl (S := S) (T := T) hAB x
    exact e'.symm_apply_eq.mpr (hcompat' x).symm
  · intro p hp hpins
    exact ((hins (F p) ⟨p, ⟨hp, hpins⟩, rfl⟩).comp_memEquiv e' hiso').congr
      (key p.1 (hOsub p hp).1) (key p.2 (hOsub p hp).2)
  · intro dφ rφ hdd
    obtain ⟨t, ht, htb⟩ := hbound dφ rφ hdd
    refine ⟨e'.symm t, ?_, fun m hm ↦ ?_⟩
    · rw [eval_membershipIso e' hiso' dφ ![e'.symm t]
          (fun m ↦ StageModel.incl (S := S) (T := T) hAB m),
        comp_vec_one, Equiv.apply_symm_apply, hcomp]
      exact ht
    · rw [eval_membershipIso e' hiso' rφ ![StageModel.incl (S := S) (T := T) hAB m, e'.symm t]
          (fun m ↦ StageModel.incl (S := S) (T := T) hAB m),
        comp_vec_two, hcompat' m, Equiv.apply_symm_apply, hcomp]
      exact htb m hm

end ZFVP

