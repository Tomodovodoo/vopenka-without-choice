import ZFVP.ModelTheory.StageChainUnion

/-! # The data produced by Enayat's ω₁-length construction

Stage 1 of the Appendix of Enayat's "Models of set theory: extensions and dead ends" builds an
increasing ω₁-chain of countable models on subsets of one carrier of size `ℵ₁`. `StageRun M Ω`
is the record of everything that construction delivers, stated so that the two closure fields of
`ZFVP.RubinChain`, `upper` and `reflect`, can be derived from it.

The fields split in three groups.

* Chain data: the stages, their countability, that they increase, agree, cover `Ω` and compute the
  membership relation of `Ω`, together with the elementary inclusions. These are the fields of
  `ZFVP.StageChain` plus countability and nonemptiness, and `StageRun.toStageChain` repackages
  them.
* Bookkeeping data: `code`, a bijection of `ω₁` with the carrier, used to read a subset of an
  ordinal as a subset of the carrier; `guess`, the subset of `Ω` consulted at stage `α`;
  `limit_carrier`, continuity of the chain at limit indices; and `keep`, the promise the successor
  step makes about the guessed pair: once inseparable at the stage where it is guessed, it stays
  inseparable at every later stage.
* The successor step itself, `succ_bound`: a directed set with no last element defined in stage
  `γ` gets an element above all of its members of stage `γ`, and that element enters every stage
  past `γ`.

`M` is the countable model the construction starts from; `baseMap` places it elementarily inside
one of the stages, and `StageRun.embedding` composes that with the inclusion of the stage into
`Ω`.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

/-- An index of `ω₁` with predecessors but no immediate predecessor. The chain of stages is
continuous at exactly these indices. -/
def IsLimitIndex (α : OmegaOne) : Prop := (∃ β, β < α) ∧ ∀ β < α, ∃ γ, β < γ ∧ γ < α

variable (M : Type u) [SetStructure M] (Ω : Type u) [SetStructure Ω]

/-- Everything Stage 1 of Enayat's Appendix produces, over a countable starting model `M` and a
carrier `Ω` of size `ℵ₁`. See the module docstring for the three groups of fields. -/
structure StageRun where
  /-- The stage of index `α`: a subset of `Ω` with a membership relation on it. -/
  stage : OmegaOne → StageModel Ω
  /-- The bijection reading an index of `ω₁` as a point of the carrier. -/
  code : OmegaOne ≃ Ω
  /-- The subset of the carrier consulted at stage `α`; in the construction it is the diamond
  guess at `α`, read through `code`. -/
  guess : OmegaOne → Set Ω
  /-- Every stage is countable. -/
  countable : ∀ α, ((stage α).carrier).Countable
  /-- Every stage is nonempty. -/
  stage_nonempty : ∀ α, Nonempty ↥(stage α).carrier
  /-- The carriers increase. -/
  inc : IsIncreasingStages stage
  /-- Later stages restrict to earlier ones. -/
  agree : StagesAgree stage
  /-- The stages cover `Ω`. -/
  cover : StagesCover stage
  /-- The membership relation of `Ω` is the union of the stage relations. -/
  union : ∀ x y : Ω, x ∈ y ↔ unionMem stage x y
  /-- The inclusion of a stage into a later one is elementary. -/
  elem : ∀ {α β : OmegaOne}, α ≤ β →
    @ElementaryMap _ _ (stageSetStructure (stage α)) (stageSetStructure (stage β))
  /-- The elementary map `elem` is the inclusion. -/
  elem_apply : ∀ {α β : OmegaOne} (h : α ≤ β) (x : ↥(stage α).carrier),
    (elem h : ↥(stage α).carrier → ↥(stage β).carrier) x =
      StageModel.incl (S := stage α) (T := stage β) (inc h) x
  /-- At a limit index the stage is the union of the earlier ones. -/
  limit_carrier : ∀ α : OmegaOne, IsLimitIndex α →
    (stage α).carrier = {x : Ω | ∃ β, β < α ∧ x ∈ (stage β).carrier}
  /-- The index of the stage the starting model is placed on. -/
  baseIndex : OmegaOne
  /-- The starting model, elementarily inside its stage. -/
  baseMap : ElementaryMap M ↥(stage baseIndex).carrier
  /-- The successor step: a directed set with no last element defined in stage `γ` gets an element
  above all of its members from stage `γ`, and that element lies in every stage past `γ`. -/
  succ_bound : ∀ (γ : OmegaOne) (dφ : SetTheorySemiformula ↥(stage γ).carrier 1)
      (rφ : SetTheorySemiformula ↥(stage γ).carrier 2),
      DirectedNoLast (fun x ↦ dφ.Eval ![x] id) (fun x y ↦ rφ.Eval ![x, y] id) →
      ∃ (β : OmegaOne) (hβ : γ < β) (t : ↥(stage β).carrier),
        (∀ γ' : OmegaOne, γ < γ' → (t : Ω) ∈ (stage γ').carrier) ∧
        dφ.Eval ![t] (fun m ↦ elem hβ.le m) ∧
        ∀ m : ↥(stage γ).carrier, dφ.Eval ![m] id →
          rφ.Eval ![elem hβ.le m, t] (fun m ↦ elem hβ.le m)
  /-- The bookkeeping promise: if the guess at `α` is inseparable from its complement inside stage
  `α`, then the pair stays inseparable inside every later stage. -/
  keep : ∀ (α β : OmegaOne), α ≤ β →
      Inseparable ↥(stage α).carrier (fun x ↦ (x : Ω) ∈ guess α) (fun x ↦ (x : Ω) ∉ guess α) →
      Inseparable ↥(stage β).carrier
        (fun x ↦ (x : Ω) ∈ (stage α).carrier ∧ (x : Ω) ∈ guess α)
        (fun x ↦ (x : Ω) ∈ (stage α).carrier ∧ (x : Ω) ∉ guess α)

namespace StageRun

variable {M Ω}
variable (R : StageRun M Ω)

/-- The chain data of a run, as a `ZFVP.StageChain`. -/
def toStageChain : StageChain Ω where
  stage := R.stage
  inc := R.inc
  agree := R.agree
  cover := R.cover
  union := R.union
  step h := R.elem h
  step_apply h x := R.elem_apply h x

@[simp] theorem toStageChain_stage : R.toStageChain.stage = R.stage := rfl

/-- The carrier is nonempty, since a stage is. -/
theorem nonempty_carrier (R : StageRun M Ω) : Nonempty Ω :=
  Nonempty.map (fun x : ↥(R.stage R.baseIndex).carrier ↦ (x : Ω))
    (R.stage_nonempty R.baseIndex)

/-- Every stage is an elementary submodel of `Ω`, read with the stage's own membership
structure. -/
noncomputable def stageEmbedding (α : OmegaOne) :
    @ElementaryMap _ _ (stageSetStructure (R.stage α)) (inferInstance : SetStructure Ω) :=
  @ElementaryMap.mk _ _ (stageSetStructure (R.stage α)) _ (fun x ↦ (x : Ω)) (by
    have h : stageSetStructure (R.stage α) = submodel ((R.stage α).carrier) :=
      R.toStageChain.stageSetStructure_eq α
    rw [h]
    intro ξ n φ b f
    exact (R.toStageChain.toSubmodelChain.embedding α).elementary φ b f)

@[simp] theorem stageEmbedding_apply (α : OmegaOne) (x : ↥(R.stage α).carrier) :
    ElementaryMap.fn _ _ (R.stageEmbedding α) x = (x : Ω) := rfl

/-- The starting model, elementarily inside `Ω`. -/
noncomputable def embedding : ElementaryMap M Ω :=
  @ElementaryMap.comp _ _ _ _ (stageSetStructure (R.stage R.baseIndex)) _
    (R.stageEmbedding R.baseIndex) R.baseMap

/-- `Ω` models `ZF`, because the stage carrying `M` does and is an elementary submodel. -/
theorem models_zf (R : StageRun M Ω) [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Nonempty Ω] :
    Ω↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  haveI hne : Nonempty ↥(R.toStageChain.stage R.baseIndex).carrier :=
    R.stage_nonempty R.baseIndex
  refine R.toStageChain.models_zf R.baseIndex ?_
  refine ⟨?_⟩
  intro φ hφ
  have hs := Theory.models M 𝗭𝗙 hφ
  change φ.Eval ![] Empty.elim at hs
  have he := (R.baseMap.elementary φ ![] Empty.elim).mp hs
  have hf : (R.baseMap.toFun ∘ (Empty.elim : Empty → M)) = Empty.elim :=
    funext fun x ↦ Empty.elim x
  have hb : (R.baseMap.toFun ∘ (![] : Fin 0 → M)) = ![] := funext fun l ↦ Fin.elim0 l
  rw [hf, hb] at he
  exact he

end StageRun

end ZFVP
