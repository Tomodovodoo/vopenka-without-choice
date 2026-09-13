import ZFVP.SetTheory.PiOneForcingInverseLimit

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneThreadOrderCoordinateFormula : SetTheorySemisentence 4 :=
  “R f g i. ∃ x, ∃ y, ∃ S, !boundedValueFormula x f i ∧ !boundedValueFormula y g i ∧
    !boundedValueFormula S R i ∧ !boundedPairMemberFormula S x y”

def piOneThreadOrderCoordinateFormula : SetTheorySemisentence 4 :=
  “R f g i. ∀ x, ∀ y, ∀ S, !boundedValueFormula x f i → !boundedValueFormula y g i →
    !boundedValueFormula S R i → !boundedPairMemberFormula S x y”

theorem sigmaOneThreadOrderCoordinateFormula_sigmaOne : IsSigmaFormula 1 sigmaOneThreadOrderCoordinateFormula :=
  .exs (.exs (.exs (.bounded (.and (boundedValueFormula_bounded.subst _)
    (.and (boundedValueFormula_bounded.subst _) (.and (boundedValueFormula_bounded.subst _)
      (boundedPairMemberFormula_bounded.subst _)))))))

theorem piOneThreadOrderCoordinateFormula_piOne : IsPiFormula 1 piOneThreadOrderCoordinateFormula :=
  .all (.all (.all (.bounded (.or (boundedValueFormula_bounded.subst _).neg
    (.or (boundedValueFormula_bounded.subst _).neg (.or (boundedValueFormula_bounded.subst _).neg
      (boundedPairMemberFormula_bounded.subst _)))))))

def threadOrderGraphFormula (pos neg : SetTheorySemisentence 4) : SetTheorySemisentence 4 :=
  “S θ R C. (∀ z ∈ S, ∃ f ∈ C, ∃ g ∈ C, !boundedKpairFormula z f g ∧ ∀ i ∈ θ, !pos R f g i) ∧
    ∀ f ∈ C, ∀ g ∈ C, (∀ i ∈ θ, !neg R f g i) → !boundedPairMemberFormula S f g”

theorem threadOrderGraphFormula_levy {s : LevyPolarity} {k : ℕ} {pos neg : SetTheorySemisentence 4}
    (hp : IsLevyFormula s k pos) (hn : IsLevyFormula s.dual k neg) :
    IsLevyFormula s k (threadOrderGraphFormula pos neg) := by
  cases s <;> exact
    .and (.boundedAll (.bvar 0) (.boundedExs (.bvar 4) (.boundedExs (.bvar 5)
      (.and (.bounded (boundedKpairFormula_bounded.subst _)) (.boundedAll (.bvar 4) (hp.subst _))))))
      (.boundedAll (.bvar 3) (.boundedAll (.bvar 4) (.or
        (IsLevyFormula.boundedAll (.bvar 3) (hn.subst _)).neg
        (.bounded (boundedPairMemberFormula_bounded.subst _)))))

def sigmaOneThreadOrderGraphFormula : SetTheorySemisentence 4 :=
  threadOrderGraphFormula sigmaOneThreadOrderCoordinateFormula piOneThreadOrderCoordinateFormula

def piOneThreadOrderGraphFormula : SetTheorySemisentence 4 :=
  threadOrderGraphFormula piOneThreadOrderCoordinateFormula sigmaOneThreadOrderCoordinateFormula

theorem sigmaOneThreadOrderGraphFormula_sigmaOne : IsSigmaFormula 1 sigmaOneThreadOrderGraphFormula :=
  threadOrderGraphFormula_levy sigmaOneThreadOrderCoordinateFormula_sigmaOne piOneThreadOrderCoordinateFormula_piOne

theorem piOneThreadOrderGraphFormula_piOne : IsPiFormula 1 piOneThreadOrderGraphFormula :=
  threadOrderGraphFormula_levy piOneThreadOrderCoordinateFormula_piOne sigmaOneThreadOrderCoordinateFormula_sigmaOne

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaOneThreadOrderCoordinateFormula (R f g i : V) :
    sigmaOneThreadOrderCoordinateFormula.Evalb ![R, f, g, i] ↔ ⟨f ‘ i, g ‘ i⟩ₖ ∈ R ‘ i := by
  simp [sigmaOneThreadOrderCoordinateFormula]

theorem eval_piOneThreadOrderCoordinateFormula (R f g i : V) :
    piOneThreadOrderCoordinateFormula.Evalb ![R, f, g, i] ↔ ⟨f ‘ i, g ‘ i⟩ₖ ∈ R ‘ i := by
  simp [piOneThreadOrderCoordinateFormula]
  constructor
  · intro h
    exact h _ _ _ rfl rfl rfl
  · rintro h x y S rfl rfl rfl
    exact h

theorem eval_threadOrderGraphFormula (pos neg : SetTheorySemisentence 4) (S θ R C : V)
    (hp : ∀ f g i : V, pos.Evalb ![R, f, g, i] ↔ ⟨f ‘ i, g ‘ i⟩ₖ ∈ R ‘ i)
    (hn : ∀ f g i : V, neg.Evalb ![R, f, g, i] ↔ ⟨f ‘ i, g ‘ i⟩ₖ ∈ R ‘ i) :
    (threadOrderGraphFormula pos neg).Evalb ![S, θ, R, C] ↔ S = forcingThreadOrder θ R C := by
  have he : (threadOrderGraphFormula pos neg).Evalb ![S, θ, R, C] ↔
      (∀ z ∈ S, ∃ f ∈ C, ∃ g ∈ C, z = ⟨f, g⟩ₖ ∧ ∀ i ∈ θ, ⟨f ‘ i, g ‘ i⟩ₖ ∈ R ‘ i) ∧
      ∀ f ∈ C, ∀ g ∈ C, (∀ i ∈ θ, ⟨f ‘ i, g ‘ i⟩ₖ ∈ R ‘ i) → ⟨f, g⟩ₖ ∈ S := by
    simp [threadOrderGraphFormula, hp, hn, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  rw [he]
  constructor
  · rintro ⟨hf, hb⟩
    apply mem_ext
    intro z
    constructor
    · intro hz
      obtain ⟨f, hf, g, hg, rfl, h⟩ := hf z hz
      exact (mem_forcingThreadOrder_iff θ R C f g).mpr ⟨hf, hg, h⟩
    · intro hz
      obtain ⟨f, hf, g, hg, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
      exact hb f hf g hg ((mem_forcingThreadOrder_iff θ R C f g).mp hz).2.2
  · rintro rfl
    constructor
    · intro z hz
      obtain ⟨f, hf, g, hg, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
      exact ⟨f, hf, g, hg, rfl, ((mem_forcingThreadOrder_iff θ R C f g).mp hz).2.2⟩
    · intro f hf g hg h
      exact (mem_forcingThreadOrder_iff θ R C f g).mpr ⟨hf, hg, h⟩

theorem eval_sigmaOneThreadOrderGraphFormula (S θ R C : V) :
    sigmaOneThreadOrderGraphFormula.Evalb ![S, θ, R, C] ↔ S = forcingThreadOrder θ R C :=
  eval_threadOrderGraphFormula _ _ S θ R C
    (fun f g i ↦ eval_sigmaOneThreadOrderCoordinateFormula R f g i)
    (fun f g i ↦ eval_piOneThreadOrderCoordinateFormula R f g i)

theorem eval_piOneThreadOrderGraphFormula (S θ R C : V) :
    piOneThreadOrderGraphFormula.Evalb ![S, θ, R, C] ↔ S = forcingThreadOrder θ R C :=
  eval_threadOrderGraphFormula _ _ S θ R C
    (fun f g i ↦ eval_piOneThreadOrderCoordinateFormula R f g i)
    (fun f g i ↦ eval_sigmaOneThreadOrderCoordinateFormula R f g i)

instance sigmaOneThreadOrderGraphFormula_defined : ℒₛₑₜ-function₃[V] forcingThreadOrder via sigmaOneThreadOrderGraphFormula :=
  ⟨fun v ↦ by
    change sigmaOneThreadOrderGraphFormula.Evalb v ↔ v 0 = forcingThreadOrder (v 1) (v 2) (v 3)
    have hv : v = ![v 0, v 1, v 2, v 3] := by
      funext i
      exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.elim0 i) i) i) i) i
    exact (Iff.of_eq (congrArg (fun w ↦ sigmaOneThreadOrderGraphFormula.Evalb w) hv)).trans
      (eval_sigmaOneThreadOrderGraphFormula (v 0) (v 1) (v 2) (v 3))⟩

instance piOneThreadOrderGraphFormula_defined : ℒₛₑₜ-function₃[V] forcingThreadOrder via piOneThreadOrderGraphFormula :=
  ⟨fun v ↦ by
    change piOneThreadOrderGraphFormula.Evalb v ↔ v 0 = forcingThreadOrder (v 1) (v 2) (v 3)
    have hv : v = ![v 0, v 1, v 2, v 3] := by
      funext i
      exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.elim0 i) i) i) i) i
    exact (Iff.of_eq (congrArg (fun w ↦ piOneThreadOrderGraphFormula.Evalb w) hv)).trans
      (eval_piOneThreadOrderGraphFormula (v 0) (v 1) (v 2) (v 3))⟩

end ZFVP
