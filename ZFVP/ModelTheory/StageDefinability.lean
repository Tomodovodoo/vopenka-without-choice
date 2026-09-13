import ZFVP.ModelTheory.StageChainUnion
import ZFVP.ModelTheory.StageLimit

/-! # Definability along a chain of submodels

Enayat's ω₁-length construction (Stage 1 of Theorem A.1) builds its final model as the union of an
increasing chain of countable elementary submodels. Two facts about definability along such a chain
are proved here.

* `exists_definableOver_of_definable_chain` puts the parameters of any predicate definable over the
  ambient model into a single stage. It is `ZFVP.exists_definableOver_of_definable` with `OmegaOne`
  replaced by an arbitrary nonempty linear order; the private helper `exists_params_in_stage'` is
  the same generalization of `ZFVP.exists_params_in_stage`.
* `exists_definableOver_of_definable_elementary` pushes a predicate definable inside a submodel `N`
  up to a predicate definable over the ambient model with parameters in the image of `N`. It is the
  converse of `ZFVP.DefinableOver.pullback`.
* `inseparable_of_stages` transfers inseparability from all late stages of a `SubmodelChain` to the
  ambient model: a definable separator has its parameters in one stage, and there it separates the
  traces of the two sets.
* `StageFamily.inseparable_limit` and `StageChain.inseparable_union` are the two shapes the
  construction uses, for the limit step and for the union of the whole ω₁-chain.

## Which membership structure

A `StageModel` carries `ZFVP.stageSetStructure`, which is the instance typeclass search picks on
`↥(S i).carrier`, while `SubmodelChain` works with Foundation's `submodel`. The two are bridged by
`ZFVP.limitEquiv` together with `ZFVP.Inseparable.comp_memEquiv` in the limit case, and by
`ZFVP.StageChain.stageSetStructure_eq` in the union case.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

/-! ## Parameters into one stage of a chain indexed by any linear order -/

/-- The free variables of a formula can be replaced by an explicitly indexed tuple of parameters
lying in a single stage of an increasing family that covers the model. This is
`ZFVP.exists_params_in_stage` with `OmegaOne` replaced by any nonempty linear order: the proof uses
only that finitely many indices have an upper bound. -/
private theorem exists_params_in_stage' {U : Type u} [SetStructure U] {I : Type} [LinearOrder I]
    [Nonempty I] {A : I → Set U} (hmono : Monotone A) (hcover : ∀ x : U, ∃ i, x ∈ A i) {k : ℕ}
    (φ : SetTheorySemiformula U k) :
    ∃ (i : I) (n : ℕ) (ψ : SetTheorySemiformula (Fin n) k) (f : Fin n → U),
      (∀ t, f t ∈ A i) ∧ ∀ v : Fin k → U, φ.Eval v id ↔ ψ.Eval v f := by
  classical
  rcases isEmpty_or_nonempty U with hU | hU
  · refine ⟨Classical.arbitrary I, 0,
      Rew.rewriteMap (fun x : U ↦ (isEmptyElim x : Fin 0)) ▹ φ,
      (fun t : Fin 0 ↦ t.elim0 : Fin 0 → U), fun t ↦ t.elim0, ?_⟩
    intro v
    rw [Semiformula.eval_rewriteMap]
    have hid : (fun x : U ↦ ((fun t : Fin 0 ↦ t.elim0 : Fin 0 → U) (isEmptyElim x))) = id := by
      funext x; exact isEmptyElim x
    rw [hid]
  · have : Inhabited U := Classical.inhabited_of_nonempty hU
    set L : List U := φ.fvarList with hLdef
    set n : ℕ := L.length + 1 with hn
    set f : Fin n → U := fun t ↦ L.getD (t : ℕ) default with hf
    set e : U → Fin n := fun x ↦ ⟨min (L.idxOf x) L.length, by omega⟩ with he
    choose c hc using hcover
    obtain ⟨i, hi⟩ := Finite.exists_le (fun t : Fin n ↦ c (f t))
    refine ⟨i, n, Rew.rewriteMap e ▹ φ, f, fun t ↦ hmono (hi t) (hc (f t)), ?_⟩
    intro v
    rw [Semiformula.eval_rewriteMap]
    refine (Semiformula.eval_iff_of_funEqOn φ ?_).symm
    intro x hx
    have hxL : x ∈ L := Semiformula.mem_fvarList_iff_fvar?.mpr hx
    have hlt : L.idxOf x < L.length := List.idxOf_lt_length_of_mem hxL
    have hmin : min (L.idxOf x) L.length = L.idxOf x := min_eq_left hlt.le
    show f (e x) = id x
    simp only [he, hf, hmin, id_eq]
    rw [List.getD_eq_getElem L default hlt]
    exact List.getElem_idxOf hlt

/-- A formula with parameters from the model can be rewritten with the parameters carried by a
tuple indexed by `Fin n`. This is the degenerate case of `exists_params_in_stage'` with the constant
family `Set.univ`. -/
private theorem exists_fin_params {N : Type u} [SetStructure N] {k : ℕ}
    (φ : SetTheorySemiformula N k) :
    ∃ (n : ℕ) (ψ : SetTheorySemiformula (Fin n) k) (f : Fin n → N),
      ∀ v : Fin k → N, φ.Eval v id ↔ ψ.Eval v f := by
  obtain ⟨-, n, ψ, f, -, h⟩ :=
    exists_params_in_stage' (A := fun _ : ℕ ↦ (Set.univ : Set N)) monotone_const
      (fun x ↦ ⟨0, Set.mem_univ x⟩) φ
  exact ⟨n, ψ, f, h⟩

/-- Every predicate definable over the ambient model has all of its parameters inside a single
stage of a `SubmodelChain`. -/
theorem exists_definableOver_of_definable_chain {U : Type u} [SetStructure U] {I : Type}
    [LinearOrder I] [Nonempty I] (C : SubmodelChain U I) {P : U → Prop}
    (hP : ℒₛₑₜ-predicate[U] P) : ∃ i, DefinableOver (C.carrier i) P := by
  obtain ⟨φ, hφ⟩ := hP.definable
  obtain ⟨i, n, ψ, f, hf, hev⟩ := exists_params_in_stage' C.mono C.cover φ
  refine ⟨i, n, ψ, f, hf, fun x ↦ ?_⟩
  rw [← hev ![x]]
  simpa using (hφ ![x]).symm

/-! ## Pushing a predicate up along an elementary map -/

/-- A predicate definable inside a submodel `N` is the restriction of a predicate definable over
the ambient model with parameters in the image of `N`. Take the formula defining the predicate in
`N`, replace its parameters by their images under `j`, and use elementarity of `j`.

This is the converse of `ZFVP.DefinableOver.pullback`. The hypothesis `hAj`, that `A` is contained
in the image of `j`, is not needed for this direction; it is kept because it is part of the
situation the construction supplies. -/
theorem exists_definableOver_of_definable_elementary {U N : Type u} [SetStructure U]
    [SetStructure N] (j : ElementaryMap N U) (A : Set U) (hjA : ∀ x : N, j x ∈ A)
    (hAj : ∀ a ∈ A, ∃ x : N, j x = a) {X : N → Prop} (hX : ℒₛₑₜ-predicate[N] X) :
    ∃ D : U → Prop, DefinableOver A D ∧ ∀ x : N, D (j x) ↔ X x := by
  obtain ⟨φ, hφ⟩ := hX.definable
  obtain ⟨n, ψ, f, hev⟩ := exists_fin_params φ
  refine ⟨fun y ↦ ψ.Eval ![y] (fun t ↦ j (f t)),
    ⟨n, ψ, fun t ↦ j (f t), fun t ↦ hjA (f t), fun _ ↦ Iff.rfl⟩, fun x ↦ ?_⟩
  have h1 := j.elementary ψ ![x] f
  have hb : (j.toFun ∘ ![x]) = ![j x] := Matrix.fun_eq_vec_one _
  rw [hb] at h1
  have h2 : ψ.Eval ![j x] (fun t ↦ j (f t)) ↔ ψ.Eval ![x] f := h1.symm
  refine h2.trans ((hev ![x]).symm.trans ?_)
  simpa using hφ ![x]

/-! ## Inseparability along a chain -/

/-- Inseparability transfers from the late stages of a chain to the ambient model. A definable
predicate separating `V` from `W` in the ambient model has all of its parameters in a single stage,
and its restriction to that stage separates the traces of `V` and `W` there. -/
theorem inseparable_of_stages {U : Type u} [SetStructure U] {I : Type} [LinearOrder I] [Nonempty I]
    (C : SubmodelChain U I) (V W : U → Prop) (i₀ : I)
    (hV : ∀ x, V x → x ∈ C.carrier i₀) (hW : ∀ x, W x → x ∈ C.carrier i₀)
    (h : ∀ i, i₀ ≤ i → Inseparable ↥(C.carrier i) (fun x ↦ V (x : U)) (fun x ↦ W (x : U))) :
    Inseparable U V W := by
  rintro ⟨X, hX, hVX, hWX⟩
  obtain ⟨i₁, hi₁⟩ := exists_definableOver_of_definable_chain C hX
  have hdef : DefinableOver (C.carrier (max i₀ i₁)) X :=
    hi₁.mono (C.mono (le_max_right i₀ i₁))
  have hpull : ℒₛₑₜ-predicate[↥(C.carrier (max i₀ i₁))]
      (fun y ↦ X (C.embedding (max i₀ i₁) y)) :=
    DefinableOver.pullback (C.embedding (max i₀ i₁)) (C.carrier (max i₀ i₁))
      (fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩) hdef
  exact h (max i₀ i₁) (le_max_left i₀ i₁)
    ⟨fun y ↦ X (y : U), hpull, fun y hy ↦ hVX _ hy, fun y hy ↦ hWX _ hy⟩

/-- Inseparability passes to the limit of a `StageFamily`: if two subsets of the carrier that live
inside stage `i₀` are inseparable in every later stage, they are inseparable in the union. The
stages are compared with the union through `ZFVP.limitEquiv`. -/
theorem StageFamily.inseparable_limit {Ω : Type u} {J : Type} [LinearOrder J] [Nonempty J]
    (F : StageFamily Ω J) (V W : Set Ω) (i₀ : J)
    (hV : V ⊆ (F.stage i₀).carrier) (hW : W ⊆ (F.stage i₀).carrier)
    (h : ∀ i, i₀ ≤ i →
      Inseparable ↥(F.stage i).carrier (fun x ↦ (x : Ω) ∈ V) (fun x ↦ (x : Ω) ∈ W)) :
    Inseparable ↥(limitStage F.stage).carrier (fun x ↦ (x : Ω) ∈ V) (fun x ↦ (x : Ω) ∈ W) := by
  refine inseparable_of_stages F.toSubmodelChain _ _ i₀ (fun x hx ↦ hV hx) (fun x hx ↦ hW hx) ?_
  intro i hi
  exact (h i hi).comp_memEquiv (limitEquiv F.stage i).symm
    (limitEquiv_symm_mem_iff F.inc F.agree i)

/-- Inseparability passes to the union of a `StageChain`: if two subsets of the carrier that live
inside stage `α` are inseparable in every later stage, they are inseparable in `Ω`. The hypothesis
is read with the stages' own membership structures and moved to Foundation's `submodel` by
`ZFVP.StageChain.stageSetStructure_eq`. -/
theorem StageChain.inseparable_union {Ω : Type u} [SetStructure Ω] (C : StageChain Ω)
    (V W : Set Ω) (α : OmegaOne) (hV : V ⊆ (C.stage α).carrier) (hW : W ⊆ (C.stage α).carrier)
    (h : ∀ β, α ≤ β →
      Inseparable ↥(C.stage β).carrier (fun x ↦ (x : Ω) ∈ V) (fun x ↦ (x : Ω) ∈ W)) :
    Inseparable Ω (fun x ↦ x ∈ V) (fun x ↦ x ∈ W) := by
  refine inseparable_of_stages C.toSubmodelChain _ _ α (fun x hx ↦ hV hx) (fun x hx ↦ hW hx) ?_
  intro β hβ
  have hins := h β hβ
  rw [C.stageSetStructure_eq β] at hins
  exact hins

end ZFVP
