import ZFVP.SetTheory.ElementaryMap

/-! # Tarski-Vaught for an increasing chain of subsets of one model

Enayat's ω₁-length construction (Stage 1 of Theorem A.1) builds its final model as the union of an
increasing chain of countable submodels of a fixed structure `W`. The stages are subsets of `W`,
not separate models glued along a colimit, so the elementary chain theorem is needed in the form
proved here: if every inclusion of one stage into a later stage is elementary and the stages cover
`W`, then every stage is an elementary substructure of `W` itself.

* `SubmodelChain W I` packages the data: subsets `carrier i ⊆ W` increasing in `i`, covering `W`,
  with an elementary map `step h : ↥(carrier i) → ↥(carrier j)` for `i ≤ j` whose underlying
  function is the inclusion. No coherence conditions are needed, since inclusions compose on the
  nose.
* `SubmodelChain.eval_incl` is the elementary chain theorem: a formula holds of parameters in a
  stage exactly when it holds of the same elements in `W`.
* `SubmodelChain.embedding` repackages it as an `ElementaryMap ↥(carrier i) W`.
* `SubmodelChain.models_zf` transfers ZF from any one stage to `W`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

/-- An increasing chain of subsets of a fixed structure `W`, covering `W`, along which the
inclusions are elementary.

`step h` is the elementary map from stage `i` to stage `j` for `i ≤ j`, and `step_apply` says its
underlying function is the inclusion: it does not move the underlying element of `W`. That is the
only coherence needed, because inclusions compose and are the identity on the nose. -/
structure SubmodelChain (W : Type u) [SetStructure W] (I : Type) [LinearOrder I] where
  /-- The stage at index `i`, a subset of `W`. -/
  carrier : I → Set W
  /-- The stages increase along the index order. -/
  mono : Monotone carrier
  /-- Every element of `W` lies in some stage. -/
  cover : ∀ x : W, ∃ i, x ∈ carrier i
  /-- The inclusion of an earlier stage into a later one, as an elementary map. -/
  step : ∀ {i j : I}, i ≤ j → ElementaryMap ↥(carrier i) ↥(carrier j)
  /-- `step` really is the inclusion: it does not change the underlying element of `W`. -/
  step_apply : ∀ {i j : I} (h : i ≤ j) (x : ↥(carrier i)), ((step h x : ↥(carrier j)) : W) = (x : W)

namespace SubmodelChain

variable {W : Type u} [SetStructure W] {I : Type} [LinearOrder I]

/-- Composing with a cons of vectors. Proved here so this file does not have to import
`ZFVP.ModelTheory.ElementaryChain`. -/
theorem comp_vecCons {V U : Type*} {n : ℕ} (g : V → U) (x : V) (b : Fin n → V) :
    (fun l ↦ g ((x :> b) l)) = (g x :> fun l ↦ g (b l)) := by
  funext l
  refine Fin.cases ?_ (fun m ↦ ?_) l <;> rfl

variable (C : SubmodelChain W I)

/-- The underlying element of `W` of a term evaluated in a stage is the term evaluated in `W`. -/
theorem val_incl_term {ξ : Type*} {n : ℕ} {i : I} (b : Fin n → ↥(C.carrier i))
    (f : ξ → ↥(C.carrier i)) (t : SetTheorySemiterm ξ n) :
    t.val (fun l ↦ (b l : W)) (fun x ↦ (f x : W)) = ((t.val b f : ↥(C.carrier i)) : W) := by
  cases t with
  | bvar l => rfl
  | fvar x => rfl
  | func h _ => exact Empty.elim h

/-- Tarski-Vaught elementary chain theorem for a chain of subsets of one structure: every stage is
an elementary substructure of the ambient model `W`. -/
theorem eval_incl {ξ : Type} :
    ∀ {n : ℕ} (φ : SetTheorySemiformula ξ n) (i : I) (b : Fin n → ↥(C.carrier i))
      (f : ξ → ↥(C.carrier i)),
      φ.Eval b f ↔ φ.Eval (fun l ↦ (b l : W)) (fun x ↦ (f x : W)) := by
  intro n φ
  induction φ with
  | verum => intro i b f; rfl
  | falsum => intro i b f; rfl
  | rel r ts =>
    intro i b f
    cases r <;>
      simp only [Semiformula.eval_rel, Structure.rel, Function.comp_def, val_incl_term]
    · exact Subtype.coe_inj.symm
    · exact Iff.rfl
  | nrel r ts =>
    intro i b f
    cases r <;>
      simp only [Semiformula.eval_nrel, Structure.rel, Function.comp_def, val_incl_term]
    · exact not_congr Subtype.coe_inj.symm
    · exact Iff.rfl
  | and φ ψ ihφ ihψ => intro i b f; exact and_congr (ihφ i b f) (ihψ i b f)
  | or φ ψ ihφ ihψ => intro i b f; exact or_congr (ihφ i b f) (ihψ i b f)
  | all φ ih =>
    intro i b f
    change (∀ x : ↥(C.carrier i), φ.Eval (x :> b) f) ↔
      ∀ z : W, φ.Eval (z :> fun l ↦ (b l : W)) (fun x ↦ (f x : W))
    constructor
    · intro h z
      obtain ⟨j, hz⟩ := C.cover z
      have hik : i ≤ max i j := le_max_left i j
      have hjk : j ≤ max i j := le_max_right i j
      have hzk : z ∈ C.carrier (max i j) := C.mono hjk hz
      have hall : ∀ x : ↥(C.carrier (max i j)),
          φ.Eval (x :> fun l ↦ C.step hik (b l)) (fun x ↦ C.step hik (f x)) :=
        ((C.step hik).elementary (.all φ) b f).mp h
      have hy := (ih (max i j)
        (⟨z, hzk⟩ :> fun l ↦ C.step hik (b l)) (fun x ↦ C.step hik (f x))).mp
        (hall ⟨z, hzk⟩)
      rw [comp_vecCons (fun x : ↥(C.carrier (max i j)) ↦ (x : W))] at hy
      simp only [C.step_apply hik] at hy
      exact hy
    · intro h x
      refine (ih i (x :> b) f).mpr ?_
      rw [comp_vecCons (fun x : ↥(C.carrier i) ↦ (x : W))]
      exact h (x : W)
  | exs φ ih =>
    intro i b f
    change (∃ x : ↥(C.carrier i), φ.Eval (x :> b) f) ↔
      ∃ z : W, φ.Eval (z :> fun l ↦ (b l : W)) (fun x ↦ (f x : W))
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨(x : W), ?_⟩
      have := (ih i (x :> b) f).mp hx
      rwa [comp_vecCons (fun x : ↥(C.carrier i) ↦ (x : W))] at this
    · rintro ⟨z, hz⟩
      obtain ⟨j, hzj⟩ := C.cover z
      have hik : i ≤ max i j := le_max_left i j
      have hjk : j ≤ max i j := le_max_right i j
      have hzk : z ∈ C.carrier (max i j) := C.mono hjk hzj
      have hy : φ.Eval (⟨z, hzk⟩ :> fun l ↦ C.step hik (b l))
          (fun x ↦ C.step hik (f x)) := by
        refine (ih (max i j) (⟨z, hzk⟩ :> fun l ↦ C.step hik (b l))
          (fun x ↦ C.step hik (f x))).mpr ?_
        rw [comp_vecCons (fun x : ↥(C.carrier (max i j)) ↦ (x : W))]
        simp only [C.step_apply hik]
        exact hz
      exact ((C.step hik).elementary (.exs φ) b f).mpr ⟨⟨z, hzk⟩, hy⟩

/-- The inclusion of a stage into the ambient model, as an elementary map. -/
def embedding (i : I) : ElementaryMap ↥(C.carrier i) W where
  toFun := fun x ↦ (x : W)
  elementary φ b f := C.eval_incl φ i b f

@[simp] theorem embedding_apply (i : I) (x : ↥(C.carrier i)) :
    C.embedding i x = (x : W) := rfl

/-- If one stage models ZF, so does the ambient model. -/
theorem models_zf [Nonempty W] (i : I) [Nonempty ↥(C.carrier i)]
    (h : (↥(C.carrier i))↓[ℒₛₑₜ] ⊧* 𝗭𝗙) : W↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  refine ⟨?_⟩
  intro φ hφ
  have hs := Theory.models (↥(C.carrier i)) 𝗭𝗙 hφ
  change φ.Eval ![] Empty.elim at hs
  have he := (C.eval_incl φ i ![] Empty.elim).mp hs
  have hf : (fun x : Empty ↦ ((Empty.elim x : ↥(C.carrier i)) : W)) = Empty.elim := by
    funext x
    exact Empty.elim x
  have hb : (fun l : Fin 0 ↦ (((![] : Fin 0 → ↥(C.carrier i)) l : ↥(C.carrier i)) : W)) = ![] := by
    funext l
    exact Fin.elim0 l
  rw [hf, hb] at he
  exact he

/-- Every element of `W` lies in the range of the inclusion of some stage. -/
theorem exists_stage (x : W) : ∃ (i : I) (y : ↥(C.carrier i)), (y : W) = x := by
  obtain ⟨i, hi⟩ := C.cover x
  exact ⟨i, ⟨x, hi⟩, rfl⟩

end SubmodelChain
end ZFVP
