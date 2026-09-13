import ZFVP.ModelTheory.InfinitaryAdequateConditions

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakModel
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}

namespace ParameterInstance

def atCoordinate {n} (ψ : ParameterInstance M S 1) (i : Fin n) : ParameterInstance M S n :=
  ψ.rename (fun _ ↦ i)

@[simp] theorem eval_atCoordinate {n} (ψ : ParameterInstance M S 1) (i : Fin n) (b : Fin n → M.Domain) :
    (ψ.atCoordinate i).Eval b ↔ ψ.Eval (b i :> Fin.elim0) := by
  rw [atCoordinate, eval_rename]
  have he : b ∘ (fun _ : Fin 1 ↦ i) = b i :> Fin.elim0 := by
    funext j
    cases j using Fin.cases with
    | zero => rfl
    | succ j => exact j.elim0
  rw [he]

/-- Relate a coordinate value to the distinguished last coordinate of a condition. -/
def coordinateMatrix {k} (p : ParameterInstance M S (1 + k)) (i : Fin (1 + k)) :
    ParameterInstance M S 2 :=
  ((p.rename (WitnessCoordinates.embed k)).and
    (ofFormula (Formula.equal (WitnessCoordinates.witness k) (WitnessCoordinates.embed k i))
      (FragmentClosure.fo_closed _))).exsN k

theorem eval_coordinateMatrix {k} (p : ParameterInstance M S (1 + k)) (i : Fin (1 + k))
    (y x : M.Domain) : (p.coordinateMatrix i).Eval (y :> x :> Fin.elim0) ↔
      ∃ b : Fin (1 + k) → M.Domain, b (Formula.lastCoordinate k) = x ∧ p.Eval b ∧ y = b i := by
  rw [coordinateMatrix, eval_exsN_iff]
  constructor
  · rintro ⟨b, hb, hp⟩
    have hz := congrFun hb 0
    have ho := congrFun hb 1
    rw [Formula.dropFirst_apply, WitnessCoordinates.tail_zero] at hz
    rw [Formula.dropFirst_apply, WitnessCoordinates.tail_one] at ho
    obtain ⟨hp, he⟩ := (eval_and _ _ b).mp hp
    rw [eval_rename] at hp
    have he' := (ParameterInstance.eval_ofFormula (M := M) (S := S)
      (Formula.equal (L := L) (WitnessCoordinates.witness k) (WitnessCoordinates.embed k i))
      (FragmentClosure.fo_closed _) b).mp he
    rw [Formula.weakEval_equal] at he'
    exact ⟨b ∘ WitnessCoordinates.embed k, ho, hp, hz.symm.trans he'⟩
  · rintro ⟨b, hb, hp, he⟩
    refine ⟨WitnessCoordinates.insert k b y, ?_, ?_⟩
    · rw [WitnessCoordinates.drop_insert, hb]
    · rw [eval_and, eval_rename, WitnessCoordinates.insert_comp_embed]
      refine ⟨hp, ?_⟩
      apply (ParameterInstance.eval_ofFormula (M := M) (S := S)
        (Formula.equal (L := L) (WitnessCoordinates.witness k) (WitnessCoordinates.embed k i))
        (FragmentClosure.fo_closed _) _).mpr
      simpa only [Formula.weakEval_equal, WitnessCoordinates.insert_witness,
        WitnessCoordinates.insert_embed] using he

end ParameterInstance
namespace AdequateCondition

/-- Interchange freezes a selected coordinate already confined to an old small fiber. -/
theorem freeze_positive (hM : M.Adequate S) {n} (p : AdequateCondition M S n)
    (i : Fin (1 + n)) (ψ : ParameterInstance M S 1)
    (hs : ¬M.Q {x | ψ.Eval (x :> Fin.elim0)})
    (hbound : ∀ b, p.formula.Eval b → ψ.Eval (b i :> Fin.elim0)) :
    ∃ a : M.Domain, M.Q (p.formula.and (ParameterInstance.equalName i a)).projection := by
  let θ := p.formula.coordinateMatrix i
  have hq : M.Q {y | ∃ x, θ.Eval (x :> y :> Fin.elim0)} := by
    have he : p.formula.projection = {y | ∃ x, θ.Eval (x :> y :> Fin.elim0)} := by
      ext y
      rw [ParameterInstance.mem_projection]
      constructor
      · rintro ⟨b, hb, hp⟩
        exact ⟨b i, (p.formula.eval_coordinateMatrix i _ _).mpr ⟨b, hb, hp, rfl⟩⟩
      · rintro ⟨x, hx⟩
        obtain ⟨b, hb, hp, _⟩ := (p.formula.eval_coordinateMatrix i _ _).mp hx
        exact ⟨b, hb, hp⟩
    exact he ▸ p.large
  have hsmall : ¬M.Q {x | ∃ y, θ.Eval (x :> y :> Fin.elim0)} := by
    intro hh
    apply hs
    apply M.mono ?_ hh
    rintro x ⟨y, hy⟩
    obtain ⟨b, hb, hp, hx⟩ := (p.formula.eval_coordinateMatrix i _ _).mp hy
    exact hx.symm ▸ hbound b hp
  obtain ⟨a, ha⟩ := hM.parameter_large_witness θ Fin.elim0 hq hsmall
  refine ⟨a, M.mono ?_ ha⟩
  intro y hy
  obtain ⟨b, hb, hp, he⟩ := (p.formula.eval_coordinateMatrix i _ _).mp hy
  apply (ParameterInstance.mem_projection _ y).mpr
  exact ⟨b, hb, (ParameterInstance.eval_and _ _ b).mpr
    ⟨hp, (ParameterInstance.eval_equalName _ _ b).mpr he.symm⟩⟩

/-- Every coordinate can be rejected from a named small fiber or fixed to an old point. -/
theorem freeze (hM : M.Adequate S) {n} (p : AdequateCondition M S n)
    (i : Fin (1 + n)) (ψ : ParameterInstance M S 1)
    (hs : ¬M.Q {x | ψ.Eval (x :> Fin.elim0)}) :
    ∃ q : AdequateCondition M S n, Refines p q ∧
      ((∀ b, q.formula.Eval b → ¬ψ.Eval (b i :> Fin.elim0)) ∨
        ∃ a : M.Domain, ∀ b, q.formula.Eval b → b i = a) := by
  rcases hM.parameter_projected_split p.formula (ψ.atCoordinate i) p.large with hp | hn
  · let r : AdequateCondition M S n := ⟨p.formula.and (ψ.atCoordinate i), hp⟩
    have hb : ∀ b, r.formula.Eval b → ψ.Eval (b i :> Fin.elim0) := by
      intro b ht
      exact (ParameterInstance.eval_atCoordinate ψ i b).mp ((ParameterInstance.eval_and _ _ b).mp ht).2
    obtain ⟨a, ha⟩ := r.freeze_positive hM i ψ hs hb
    refine ⟨⟨r.formula.and (ParameterInstance.equalName i a), ha⟩, ?_, Or.inr ⟨a, ?_⟩⟩
    · intro b ht
      exact (ParameterInstance.eval_and _ _ b).mp ((ParameterInstance.eval_and _ _ b).mp ht).1 |>.1
    · intro b ht
      exact (ParameterInstance.eval_equalName _ _ b).mp ((ParameterInstance.eval_and _ _ b).mp ht).2
  · refine ⟨⟨p.formula.and (ψ.atCoordinate i).neg, hn⟩, ?_, Or.inl ?_⟩
    · intro b ht
      exact (ParameterInstance.eval_and _ _ b).mp ht |>.1
    · intro b ht hh
      exact ((ParameterInstance.eval_and _ _ b).mp ht).2 ((ParameterInstance.eval_atCoordinate ψ i b).mpr hh)

end AdequateCondition
end WeakModel
end ZFVP.Infinitary


