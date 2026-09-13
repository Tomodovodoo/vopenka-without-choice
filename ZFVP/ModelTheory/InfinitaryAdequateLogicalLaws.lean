import ZFVP.ModelTheory.InfinitaryAdequateEvaluation

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakModel.AdequateGenericChain
open AdequateFiniteCondition
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}
  {p₀ : AdequateFiniteCondition M S} (C : AdequateGenericChain M S p₀)

@[simp] theorem eval_rename {n m} (φ : ParameterInstance M S n) (ρ : Fin n → Fin m)
    (ts : Fin m → ℕ) : C.Eval (φ.rename ρ) ts ↔ C.Eval φ (ts ∘ ρ) := by
  constructor
  · rintro ⟨k, hk, hh⟩
    refine ⟨k, fun i ↦ hk (ρ i), ?_⟩
    intro b hb
    exact (ParameterInstance.eval_rename φ ρ (fun i ↦ b (RightCoordinate.index (hk i)))).mp (hh b hb)
  · rintro ⟨k, hk⟩
    obtain ⟨l, hl⟩ := C.coordinate_cofinal (RightCoordinate.width ts)
    obtain ⟨g, hg⟩ := evalAt_persistent (C.refines (Nat.le_max_left k l)) hk
    have hh := (C.refines (Nat.le_max_right k l)).choose
    have ht (i : Fin m) : ts i < 1 + (C.point (max k l)).1 :=
      (RightCoordinate.lt_width ts i).trans_le (hl.trans (Nat.add_le_add_left hh 1))
    refine ⟨max k l, ht, ?_⟩
    intro b hb
    exact (ParameterInstance.eval_rename _ _ _).mpr (hg b hb)

@[simp] theorem eval_conj {n} (s : ParameterSequence M S n) (ts : Fin n → ℕ) :
    C.Eval s.conj ts ↔ ∀ i, C.Eval (s.component i) ts := by
  constructor
  · intro h i
    exact C.eval_mono (fun b hb ↦ (ParameterSequence.eval_conj _ b).mp hb i) h
  · intro h
    let ht := RightCoordinate.lt_width ts
    obtain ⟨k, hk⟩ := C.conjunction (s.rename (fun i ↦ RightCoordinate.index (ht i)))
    rcases hk k (le_refl k) with hp | ⟨i, hn⟩
    · exact C.eval_of_forces_rename s.conj ts ht hp
    · have hn' := C.eval_of_forces_rename (s.component i).neg ts ht hn
      exact ((C.eval_neg _ _).mp hn' (h i)).elim

@[simp] theorem eval_exs {n} (φ : ParameterInstance M S (n + 1)) (ts : Fin n → ℕ) :
    C.Eval φ.exs ts ↔ ∃ t : ℕ, C.Eval φ (t :> ts) := by
  constructor
  · intro hex
    let m := RightCoordinate.width ts
    let ht := RightCoordinate.lt_width ts
    let ρ : Fin n → Fin m := fun i ↦ RightCoordinate.index (ht i)
    let ψ := φ.rename (liftRenaming ρ)
    obtain ⟨k, hk⟩ := C.existential ψ
    rcases hk k (le_refl k) with hn | hw
    · have hn' : Forces (C.point k) (φ.exs.neg.rename ρ) := by
        obtain ⟨h, hh⟩ := hn
        refine ⟨h, ?_⟩
        intro b hb
        have hh' := hh b hb
        simpa only [ParameterInstance.eval_neg, ParameterInstance.eval_exs,
          ParameterInstance.eval_rename, compose_liftRenaming, ψ] using hh'
      have hn'' := C.eval_of_forces_rename φ.exs.neg ts ht hn'
      exact ((C.eval_neg _ _).mp hn'' hex).elim
    · obtain ⟨h, i, hh⟩ := hw
      let t := (1 + (C.point k).1) - (i.val + 1)
      have hi : t < 1 + (C.point k).1 := by dsimp [t]; omega
      have hei : RightCoordinate.index hi = i := by
        apply Fin.ext
        dsimp [RightCoordinate.index, t]
        omega
      have hts (j : Fin n) : ts j < 1 + (C.point k).1 := (ht j).trans_le h
      have hfit : ∀ j, (t :> ts) j < 1 + (C.point k).1 := Fin.cases hi hts
      refine ⟨t, k, hfit, ?_⟩
      intro b hb
      have hh' := (ParameterInstance.eval_rename _ _ _).mp (hh b hb)
      rw [compose_liftRenaming] at hh'
      have he : (b ∘ Formula.rightEmbed h) ∘ ρ = fun j ↦ b (RightCoordinate.index (hts j)) := by
        funext j
        exact congrArg b (RightCoordinate.embed_index (ht j) h)
      rw [he] at hh'
      have he' : (fun j ↦ b (RightCoordinate.index (hfit j))) =
          b i :> fun j ↦ b (RightCoordinate.index (hts j)) := by
        funext j
        cases j using Fin.cases with
        | zero => exact congrArg b hei
        | succ j => rfl
      rwa [he']
  · rintro ⟨t, k, ht, hh⟩
    refine ⟨k, fun i ↦ ht i.succ, ?_⟩
    intro b hb
    apply (ParameterInstance.eval_exs _ _).mpr
    refine ⟨b (RightCoordinate.index (ht 0)), ?_⟩
    have he : (fun j ↦ b (RightCoordinate.index (ht j))) =
        b (RightCoordinate.index (ht 0)) :> fun j ↦ b (RightCoordinate.index (ht j.succ)) := by
      funext j
      cases j using Fin.cases <;> rfl
    exact he ▸ hh b hb

@[simp] theorem eval_all {n} (φ : ParameterInstance M S (n + 1)) (ts : Fin n → ℕ) :
    C.Eval φ.all ts ↔ ∀ t : ℕ, C.Eval φ (t :> ts) := by
  simp only [ParameterInstance.all, C.eval_neg, C.eval_exs, not_exists, not_not]

end WeakModel.AdequateGenericChain
end ZFVP.Infinitary

