import ZFVP.ModelTheory.StageRun
import ZFVP.ModelTheory.StageDefinability

/-! # The upper bound clause of a Rubin chain, from the successor step of a stage run

`ZFVP.RubinChain` has a field `upper`, Enayat's clause (2): a directed poset with no last element
that is definable with parameters from stage `α` gets, at every later index `γ`, an element of the
poset strictly above everything stage `γ` contributes to it, and that element enters every stage
past `γ`. `ZFVP.StageRun.upper` derives that field from the field `succ_bound` of
`ZFVP.StageRun`.

The work is the translation between the two shapes. `succ_bound` speaks about two formulas whose
free variables are indexed by the points of stage `γ` and about `ZFVP.DirectedNoLast` for those
formulas read inside the stage; `upper` speaks about a predicate and a relation on the whole
carrier `Ω`, definable with parameters from a stage.

* `exists_stageFormulasParams` is the construction of the two formulas. It keeps the finite
  parameter type `ξ` through which every evaluation factors, because `ZFVP.ElementaryMap.elementary`
  quantifies over parameter types in `Type 0` while the points of a stage live in the universe of
  the carrier. `exists_stageFormulas` is the same statement with the parameter type already
  rewritten to the points of the stage, which is the form `succ_bound` reads.
* The formulas are built from the definability witnesses rather than by pulling the predicate back
  into the stage. A pullback would only be correct at points of the stage; the last step of the
  proof needs correctness at the new point, which is outside stage `γ`.
* `directedFormula` says "any two elements of the set have a common strict upper bound in it". It
  is the sentence whose reflection into the stage turns `IsDirectedNoMaxOn` on `Ω` into
  `DirectedNoLast` inside the stage.
* `exists_strict_upper_bound` is the one order-theoretic step: in a directed poset with no maximum,
  two elements have a common upper bound that is distinct from both.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

/-! ## Formulas for a predicate and a strict order definable over a stage -/

section Formulas

variable {W : Type u} [SetStructure W]

/-- From a predicate and a relation definable with parameters in `A`: a parameter type `ξ` in
`Type 0`, a tuple `G` of parameters lying in `A`, a formula `Φ` defining `P` and a formula `Ψ`
defining the strict part of `le`, both correct at every point of `W`.

The parameter type is kept small on purpose: `ZFVP.ElementaryMap.elementary` only accepts formulas
whose parameters are indexed by a type in `Type 0`, and `↥A` lives in the universe of `W`. -/
theorem exists_stageFormulasParams {A : Set W} {P : W → Prop} {le : W → W → Prop}
    (hP : DefinableOver A P) (hle : DefinableOverRel A le) :
    ∃ (ξ : Type) (Φ : SetTheorySemiformula ξ 1) (Ψ : SetTheorySemiformula ξ 2) (G : ξ → ↥A),
      (∀ z : W, Φ.Eval ![z] (fun s ↦ ((G s : ↥A) : W)) ↔ P z) ∧
      ∀ z w : W, Ψ.Eval ![z, w] (fun s ↦ ((G s : ↥A) : W)) ↔ (le z w ∧ z ≠ w) := by
  obtain ⟨n₁, φ₁, f₁, hf₁, hP₁⟩ := hP
  obtain ⟨n₂, φ₂, f₂, hf₂, hle₂⟩ := hle
  refine ⟨Fin n₁ ⊕ Fin n₂, Rew.rewriteMap Sum.inl ▹ φ₁,
    Rew.rewriteMap Sum.inr ▹ (φ₂ ⋏ (Semiformula.nrel Language.Set.Rel.eq
      ![Semiterm.bvar 0, Semiterm.bvar 1] : SetTheorySemiformula (Fin n₂) 2)),
    Sum.elim (fun i ↦ (⟨f₁ i, hf₁ i⟩ : ↥A)) (fun i ↦ (⟨f₂ i, hf₂ i⟩ : ↥A)), ?_, ?_⟩
  · intro z
    rw [Semiformula.eval_rewriteMap]
    exact (hP₁ z).symm
  · intro z w
    rw [Semiformula.eval_rewriteMap]
    exact and_congr (hle₂ z w).symm Iff.rfl

/-- The two formulas of `exists_stageFormulasParams`, with their parameters indexed by the points
of `A` itself. This is the shape `ZFVP.StageRun.succ_bound` reads. -/
theorem exists_stageFormulas {A : Set W} {P : W → Prop} {le : W → W → Prop}
    (hP : DefinableOver A P) (hle : DefinableOverRel A le) :
    ∃ (dφ : SetTheorySemiformula ↥A 1) (rφ : SetTheorySemiformula ↥A 2),
      (∀ z : W, dφ.Eval ![z] (fun m : ↥A ↦ (m : W)) ↔ P z) ∧
      ∀ z w : W, rφ.Eval ![z, w] (fun m : ↥A ↦ (m : W)) ↔ (le z w ∧ z ≠ w) := by
  obtain ⟨ξ, Φ, Ψ, G, hΦ, hΨ⟩ := exists_stageFormulasParams hP hle
  refine ⟨Rew.rewriteMap G ▹ Φ, Rew.rewriteMap G ▹ Ψ, fun z ↦ ?_, fun z w ↦ ?_⟩
  · rw [Semiformula.eval_rewriteMap]; exact hΦ z
  · rw [Semiformula.eval_rewriteMap]; exact hΨ z w

variable {ξ : Type}

/-- Evaluating an existential quantification of a one-variable formula. -/
theorem eval_ex_zero (f : ξ → W) (Φ : SetTheorySemiformula ξ 1) :
    (∃¹ Φ).Eval ![] f ↔ ∃ z : W, Φ.Eval ![z] f := by simp

/-- "Any two elements satisfying `Φ` have a common `Ψ`-upper bound satisfying `Φ`", as a formula
with no free bound variables. -/
def directedFormula (Φ : SetTheorySemiformula ξ 1) (Ψ : SetTheorySemiformula ξ 2) :
    SetTheorySemiformula ξ 0 :=
  ∀¹ ∀¹ ((Φ ⇜ ![Semiterm.bvar 1]) 🡒 (Φ ⇜ ![Semiterm.bvar 0]) 🡒
    ∃¹ ((Φ ⇜ ![Semiterm.bvar 0]) ⋏ (Ψ ⇜ ![Semiterm.bvar 2, Semiterm.bvar 0]) ⋏
      (Ψ ⇜ ![Semiterm.bvar 1, Semiterm.bvar 0])))

theorem eval_directedFormula (f : ξ → W) (Φ : SetTheorySemiformula ξ 1)
    (Ψ : SetTheorySemiformula ξ 2) :
    (directedFormula Φ Ψ).Eval ![] f ↔
      ∀ x y : W, Φ.Eval ![x] f → Φ.Eval ![y] f →
        ∃ z : W, Φ.Eval ![z] f ∧ Ψ.Eval ![x, z] f ∧ Ψ.Eval ![y, z] f := by
  have e1 : ∀ b : Fin 2 → W,
      (Semiterm.val (L := ℒₛₑₜ) (ξ := ξ) b f ∘ ![Semiterm.bvar 1]) = ![b 1] := by
    intro b; funext i; match i with | 0 => rfl
  have e2 : ∀ b : Fin 2 → W,
      (Semiterm.val (L := ℒₛₑₜ) (ξ := ξ) b f ∘ ![Semiterm.bvar 0]) = ![b 0] := by
    intro b; funext i; match i with | 0 => rfl
  have e3 : ∀ b : Fin 3 → W,
      (Semiterm.val (L := ℒₛₑₜ) (ξ := ξ) b f ∘ ![Semiterm.bvar 0]) = ![b 0] := by
    intro b; funext i; match i with | 0 => rfl
  have e4 : ∀ b : Fin 3 → W,
      (Semiterm.val (L := ℒₛₑₜ) (ξ := ξ) b f ∘ ![Semiterm.bvar 2, Semiterm.bvar 0])
        = ![b 2, b 0] := by
    intro b; funext i; match i with | 0 => rfl | 1 => rfl
  have e5 : ∀ b : Fin 3 → W,
      (Semiterm.val (L := ℒₛₑₜ) (ξ := ξ) b f ∘ ![Semiterm.bvar 1, Semiterm.bvar 0])
        = ![b 1, b 0] := by
    intro b; funext i; match i with | 0 => rfl | 1 => rfl
  simp only [directedFormula, Semiformula.eval_all, Semiformula.eval_ex,
    Semiformula.eval_substs, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_and, e1, e2, e3, e4, e5,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  exact Iff.rfl

end Formulas

/-! ## The order-theoretic step -/

/-- In a directed poset with no maximum element, two elements have a common upper bound that is
different from both of them. Take a common upper bound `z`; since `z` is not a maximum some `w` in
the poset is not below `z`; a common upper bound `u` of `z` and `w` then works, because `u = x` or
`u = y` would force `u = z` by antisymmetry and put `w` below `z`. -/
theorem exists_strict_upper_bound {V : Type u} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {P : V → Prop} {le : V → V → Prop} (hpo : IsPartialOrderOn P le)
    (hdir : IsDirectedNoMaxOn P le) (x y : V) (hx : P x) (hy : P y) :
    ∃ z, P z ∧ (le x z ∧ x ≠ z) ∧ (le y z ∧ y ≠ z) := by
  obtain ⟨-, hd, hmax⟩ := hdir
  obtain ⟨-, htrans, hanti⟩ := hpo
  obtain ⟨z, hz, hxz, hyz⟩ := hd x y hx hy
  obtain ⟨w, hw, hwz⟩ : ∃ w, P w ∧ ¬ le w z := by
    by_contra hcon
    exact hmax ⟨z, hz, fun w hw ↦ not_not.mp fun hnle ↦ hcon ⟨w, hw, hnle⟩⟩
  obtain ⟨u, hu, hzu, hwu⟩ := hd z w hz hw
  refine ⟨u, hu, ⟨htrans x z u hx hz hu hxz hzu, ?_⟩, htrans y z u hy hz hu hyz hzu, ?_⟩
  · rintro rfl
    have hxeq : x = z := hanti x z hx hz hxz hzu
    subst hxeq
    exact hwz hwu
  · rintro rfl
    have hyeq : y = z := hanti y z hy hz hyz hzu
    subst hyeq
    exact hwz hwu

/-! ## The clause itself -/

namespace StageRun

variable {M Ω : Type u} [SetStructure M] [SetStructure Ω]

/-- Enayat's clause (2) for a stage run, that is the field `upper` of `ZFVP.RubinChain`. A
directed poset with no maximum, definable with parameters from stage `α`, has at every later index
`γ` an element strictly above every point of stage `γ` in the poset, and that element lies in every
stage past `γ`. -/
theorem upper [Nonempty Ω] [Ω↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (R : StageRun M Ω) (α γ : OmegaOne) (hαγ : α ≤ γ)
    (P : Ω → Prop) (le : Ω → Ω → Prop)
    (hP : DefinableOver ((R.stage α).carrier) P) (hle : DefinableOverRel ((R.stage α).carrier) le)
    (hpo : IsPartialOrderOn P le) (hdir : IsDirectedNoMaxOn P le) :
    ∃ d, P d ∧ (∀ x, x ∈ (R.stage γ).carrier → P x → le x d ∧ x ≠ d) ∧
      ∀ γ', γ < γ' → d ∈ (R.stage γ').carrier := by
  obtain ⟨ξ, Φ, Ψ, G, hΦ, hΨ⟩ :=
    exists_stageFormulasParams (hP.mono (R.inc hαγ)) (hle.mono (R.inc hαγ))
  set F : ξ → Ω := fun s ↦ ((G s : ↥(R.stage γ).carrier) : Ω) with hF
  -- The two formulas are correct inside stage `γ`, by elementarity of the stage.
  have hB3 : ∀ x : ↥(R.stage γ).carrier, Φ.Eval ![x] G ↔ P (x : Ω) := by
    intro x
    have h := (R.stageEmbedding γ).elementary Φ ![x] G
    have hb : ((R.stageEmbedding γ).toFun ∘ ![x]) = ![(x : Ω)] := Matrix.fun_eq_vec_one _
    rw [hb] at h
    rw [h]
    exact hΦ (x : Ω)
  have hB4 : ∀ x y : ↥(R.stage γ).carrier,
      Ψ.Eval ![x, y] G ↔ (le (x : Ω) (y : Ω) ∧ (x : Ω) ≠ (y : Ω)) := by
    intro x y
    have h := (R.stageEmbedding γ).elementary Ψ ![x, y] G
    have hb : ((R.stageEmbedding γ).toFun ∘ ![x, y]) = ![(x : Ω), (y : Ω)] :=
      Matrix.fun_eq_vec_two _
    rw [hb] at h
    rw [h]
    exact hΨ (x : Ω) (y : Ω)
  have hb0 : ((R.stageEmbedding γ).toFun ∘ (![] : Fin 0 → ↥(R.stage γ).carrier)) = ![] :=
    funext fun i ↦ i.elim0
  -- The two formulas, with their parameters indexed by the points of stage `γ`.
  have hD : ∀ x : ↥(R.stage γ).carrier,
      (Rew.rewriteMap G ▹ Φ).Eval ![x] id ↔ P (x : Ω) := by
    intro x
    rw [Semiformula.eval_rewriteMap]
    exact hB3 x
  have hL : ∀ x y : ↥(R.stage γ).carrier,
      (Rew.rewriteMap G ▹ Ψ).Eval ![x, y] id ↔ (le (x : Ω) (y : Ω) ∧ (x : Ω) ≠ (y : Ω)) := by
    intro x y
    rw [Semiformula.eval_rewriteMap]
    exact hB4 x y
  -- Inside stage `γ` the pair is a directed set with no last element.
  have hdnl : DirectedNoLast (fun x ↦ (Rew.rewriteMap G ▹ Φ).Eval ![x] id)
      (fun x y ↦ (Rew.rewriteMap G ▹ Ψ).Eval ![x, y] id) := by
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := hdir.1
      have h := (R.stageEmbedding γ).elementary (∃¹ Φ) ![] G
      rw [hb0] at h
      have hex : (∃¹ Φ).Eval ![] F := (eval_ex_zero F Φ).mpr ⟨z, (hΦ z).mpr hz⟩
      obtain ⟨x, hx⟩ := (eval_ex_zero G Φ).mp (h.mpr hex)
      exact ⟨x, (hD x).mpr ((hB3 x).mp hx)⟩
    · intro x y z hx hy hz hxy hyz
      rw [hD] at hx hy hz
      rw [hL] at hxy hyz ⊢
      obtain ⟨-, htrans, hanti⟩ := hpo
      refine ⟨htrans _ _ _ hx hy hz hxy.1 hyz.1, ?_⟩
      intro hxz
      refine hxy.2 (hanti _ _ hx hy hxy.1 ?_)
      rw [hxz]
      exact hyz.1
    · intro x y hx hy
      rw [hD] at hx hy
      have hΩ : ∀ a b : Ω, Φ.Eval ![a] F → Φ.Eval ![b] F →
          ∃ z : Ω, Φ.Eval ![z] F ∧ Ψ.Eval ![a, z] F ∧ Ψ.Eval ![b, z] F := by
        intro a b ha hb
        obtain ⟨z, hz, h1, h2⟩ :=
          exists_strict_upper_bound hpo hdir a b ((hΦ a).mp ha) ((hΦ b).mp hb)
        exact ⟨z, (hΦ z).mpr hz, (hΨ a z).mpr h1, (hΨ b z).mpr h2⟩
      have hsent : (directedFormula Φ Ψ).Eval ![] F := (eval_directedFormula F Φ Ψ).mpr hΩ
      have h := (R.stageEmbedding γ).elementary (directedFormula Φ Ψ) ![] G
      rw [hb0] at h
      obtain ⟨z, hz, h1, h2⟩ :=
        (eval_directedFormula G Φ Ψ).mp (h.mpr hsent) x y ((hB3 x).mpr hx) ((hB3 y).mpr hy)
      exact ⟨z, (hD z).mpr ((hB3 z).mp hz), (hL x z).mpr ((hB4 x z).mp h1),
        (hL y z).mpr ((hB4 y z).mp h2)⟩
  -- The successor step of the run.
  obtain ⟨β, hβ, t, hts, h1, h2⟩ :=
    R.succ_bound γ (Rew.rewriteMap G ▹ Φ) (Rew.rewriteMap G ▹ Ψ) hdnl
  have hk : ((R.stageEmbedding β).toFun ∘
      (fun s ↦ (R.elem hβ.le (G s) : ↥(R.stage β).carrier))) = F := by
    rw [hF]
    funext s
    show ((R.elem hβ.le (G s) : ↥(R.stage β).carrier) : Ω)
      = ((G s : ↥(R.stage γ).carrier) : Ω)
    rw [R.elem_apply]
    exact StageModel.coe_incl _ _
  refine ⟨(t : Ω), ?_, ?_, hts⟩
  · rw [Semiformula.eval_rewriteMap] at h1
    have he := (R.stageEmbedding β).elementary Φ ![t]
      (fun s ↦ (R.elem hβ.le (G s) : ↥(R.stage β).carrier))
    refine (hΦ (t : Ω)).mp (Semiformula.Eval.of_eq (he.mp h1) ?_ hk)
    exact Matrix.fun_eq_vec_one _
  · intro x hx hPx
    have hm : (Rew.rewriteMap G ▹ Φ).Eval ![(⟨x, hx⟩ : ↥(R.stage γ).carrier)] id :=
      (hD ⟨x, hx⟩).mpr hPx
    have h3 := h2 ⟨x, hx⟩ hm
    rw [Semiformula.eval_rewriteMap] at h3
    have he := (R.stageEmbedding β).elementary Ψ
      ![R.elem hβ.le (⟨x, hx⟩ : ↥(R.stage γ).carrier), t]
      (fun s ↦ (R.elem hβ.le (G s) : ↥(R.stage β).carrier))
    have hcoe : ((R.elem hβ.le (⟨x, hx⟩ : ↥(R.stage γ).carrier) : ↥(R.stage β).carrier) : Ω)
        = x := by rw [R.elem_apply]; exact StageModel.coe_incl _ _
    have hbx : ((R.stageEmbedding β).toFun ∘
        ![R.elem hβ.le (⟨x, hx⟩ : ↥(R.stage γ).carrier), t]) = ![x, (t : Ω)] := by
      funext i
      match i with
      | 0 => exact hcoe
      | 1 => rfl
    exact (hΨ x (t : Ω)).mp (Semiformula.Eval.of_eq (he.mp h3) hbx hk)

end StageRun

end ZFVP
