import ZFVP.ModelTheory.RubinChainCriterion
import ZFVP.ModelTheory.StageSuccessor
import ZFVP.ModelTheory.SubmodelChain
import ZFVP.SetTheory.DiamondOmegaOne

/-! # The union of an increasing ω₁-chain of stages

Stage 1 of the Appendix of Enayat's paper builds an ω₁-chain of countable models, all placed on
subsets of one fixed carrier `Ω` of size `ℵ₁`; `ZFVP.exists_stage_successor` is its successor step.
This file turns such a chain into a single structure on `Ω` in which every stage is an elementary
submodel, which is the shape the Rubinness criterion reads.

* `unionMem S x y` says that `x` is an element of `y` inside some stage, and `unionSetStructure S`
  is the membership structure on `Ω` it defines.
* `unionMem_iff_stage` is the coherence lemma: on a fixed stage, the union relation is that stage's
  own relation. Two stages are compared by moving both into their maximum.
* `StageChain Ω` bundles the family with the four hypotheses it has to satisfy (increasing,
  agreeing, covering, computing the membership relation of `Ω`) and the elementary inclusions
  between stages.
* `StageChain.stageMem_iff_coe_mem` and `StageChain.stageSetStructure_eq` are the bridge between
  the two membership structures a stage carries; see the warning below.
* `StageChain.toSubmodelChain` packages the family as a `SubmodelChain Ω OmegaOne`, so
  `SubmodelChain.embedding` gives an `ElementaryMap ↥((S α).carrier) Ω` for every `α`, and
  `StageChain.models_zf` carries ZF from one stage to `Ω`.
* `stageChain`, `stageUnionChain` and `stageUnion_embedding_apply` are the same three things with
  the hypotheses passed one at a time instead of bundled.
* `StageChain.toRubinChain` builds a `ZFVP.RubinChain` from the chain, taking the two fields of
  `RubinChain` that mention definability, `upper` and `reflect`, as arguments.

## Two membership structures on a stage

`↥((S α).carrier)` carries two `SetStructure` instances: the stage's own relation
`ZFVP.stageSetStructure (S α)`, coming from the field `StageModel.mem`, and Foundation's
`LO.FirstOrder.SetTheory.submodel`, the restriction of the membership relation of `Ω`. They are not
definitionally equal, and `stageSetStructure` is the one typeclass search picks by default here, so
bare notation such as `x ∈ y` or `M↓[ℒₛₑₜ] ⊧* 𝗭𝗙` on a stage refers to the stage's own relation.
Statements that need Foundation's `submodel` instead, which is the one baked into `SubmodelChain`
and `RubinChain`, spell it out with `@`. `StageChain.stageSetStructure_eq` says the two instances
are equal, so a caller can rewrite with it in either direction.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

variable {Ω : Type u}

/-- The underlying function of an elementary map, with both membership structures given
explicitly. `ElementaryMap.toFun` synthesizes them instead, which picks the wrong one on a stage;
see the module docstring. -/
def ElementaryMap.fn {A B : Type*} (iA : SetStructure A) (iB : SetStructure B)
    (j : @ElementaryMap A B iA iB) : A → B :=
  @ElementaryMap.toFun A B iA iB j

/-! ## The membership relation of the union -/

/-- Membership in the union of a chain of stages: `x` is an element of `y` if some stage contains
both and thinks so. -/
def unionMem (S : OmegaOne → StageModel Ω) (x y : Ω) : Prop :=
  ∃ (α : OmegaOne) (hx : x ∈ (S α).carrier) (hy : y ∈ (S α).carrier), (S α).mem ⟨x, hx⟩ ⟨y, hy⟩

/-- The membership structure on the carrier given by `unionMem`. `Membership.mem` takes the
container first, so the arguments are flipped here. -/
@[instance_reducible] def unionSetStructure (S : OmegaOne → StageModel Ω) : SetStructure Ω :=
  ⟨fun y x ↦ unionMem S x y⟩

/-- Membership for `unionSetStructure` is `unionMem`, so this instance satisfies the hypothesis
`StageChain.union` by definition. -/
theorem unionSetStructure_mem_iff (S : OmegaOne → StageModel Ω) (x y : Ω) :
    @Membership.mem Ω Ω (unionSetStructure S) y x ↔ unionMem S x y := Iff.rfl

/-- The carriers of the stages increase along the index order. -/
def IsIncreasingStages (S : OmegaOne → StageModel Ω) : Prop :=
  ∀ ⦃α β : OmegaOne⦄, α ≤ β → (S α).carrier ⊆ (S β).carrier

/-- A later stage restricts to the membership relation of an earlier one. -/
def StagesAgree (S : OmegaOne → StageModel Ω) : Prop :=
  ∀ ⦃α β : OmegaOne⦄, α ≤ β → ∀ (x y : ↥(S α).carrier)
    (hx : (x : Ω) ∈ (S β).carrier) (hy : (y : Ω) ∈ (S β).carrier),
    (S α).mem x y ↔ (S β).mem ⟨x, hx⟩ ⟨y, hy⟩

/-- The stages cover the carrier. -/
def StagesCover (S : OmegaOne → StageModel Ω) : Prop := ∀ x : Ω, ∃ α, x ∈ (S α).carrier

/-- Coherence: on a fixed stage, membership in the union is membership in that stage. Two stages
are compared by pushing both of them into their maximum. -/
theorem unionMem_iff_stage {S : OmegaOne → StageModel Ω} (hinc : IsIncreasingStages S)
    (hagr : StagesAgree S) (α : OmegaOne) {x y : Ω} (hx : x ∈ (S α).carrier)
    (hy : y ∈ (S α).carrier) : unionMem S x y ↔ (S α).mem ⟨x, hx⟩ ⟨y, hy⟩ := by
  constructor
  · rintro ⟨β, hx', hy', h⟩
    have hα : α ≤ max α β := le_max_left α β
    have hβ : β ≤ max α β := le_max_right α β
    rw [hagr hα ⟨x, hx⟩ ⟨y, hy⟩ (hinc hα hx) (hinc hα hy)]
    rw [hagr hβ ⟨x, hx'⟩ ⟨y, hy'⟩ (hinc hβ hx') (hinc hβ hy')] at h
    exact h
  · exact fun h ↦ ⟨α, hx, hy, h⟩

/-! ## Chains of stages inside a fixed structure -/

variable (Ω) in
/-- An ω₁-chain of stages inside a structure `Ω` whose membership relation is the union of the
stage relations, together with the elementary inclusion of each stage into each later one.

`union` holds by `Iff.rfl` when the instance on `Ω` is `unionSetStructure stage`; the field is
stated as an equivalence so that a caller who already has a membership structure on `Ω` can use
this file. `step` and `step_apply` are elementarity of the inclusions, with the stage's own
membership structures. -/
structure StageChain [SetStructure Ω] where
  /-- The stage of index `α`, a subset of `Ω` with a membership relation on it. -/
  stage : OmegaOne → StageModel Ω
  /-- The carriers increase. -/
  inc : IsIncreasingStages stage
  /-- Later stages restrict to earlier ones. -/
  agree : StagesAgree stage
  /-- The stages cover `Ω`. -/
  cover : StagesCover stage
  /-- The membership relation of `Ω` is the union of the stage relations. -/
  union : ∀ x y : Ω, x ∈ y ↔ unionMem stage x y
  /-- The inclusion of a stage into a later one is elementary. -/
  step : ∀ {α β : OmegaOne}, α ≤ β →
    @ElementaryMap _ _ (stageSetStructure (stage α)) (stageSetStructure (stage β))
  /-- The elementary map `step` is the inclusion. -/
  step_apply : ∀ {α β : OmegaOne} (h : α ≤ β) (x : ↥(stage α).carrier),
    (step h : ↥(stage α).carrier → ↥(stage β).carrier) x =
      StageModel.incl (S := stage α) (T := stage β) (inc h) x

namespace StageChain

variable [SetStructure Ω] (C : StageChain Ω)

/-- On a fixed stage, membership in `Ω` is the stage relation. -/
theorem unionMem_iff (α : OmegaOne) {x y : Ω} (hx : x ∈ (C.stage α).carrier)
    (hy : y ∈ (C.stage α).carrier) : x ∈ y ↔ (C.stage α).mem ⟨x, hx⟩ ⟨y, hy⟩ := by
  rw [C.union, unionMem_iff_stage C.inc C.agree α hx hy]

/-- The bridge between the two membership structures on a stage: the stage relation is the
restriction of the membership relation of `Ω`. -/
theorem stageMem_iff_coe_mem (α : OmegaOne) (x y : ↥(C.stage α).carrier) :
    (C.stage α).mem x y ↔ (x : Ω) ∈ (y : Ω) := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  exact (C.unionMem_iff α hx hy).symm

/-- The two membership structures on a stage are equal: the stage's own relation
(`stageSetStructure`) and the one restricted from `Ω` (Foundation's `submodel`). -/
theorem stageSetStructure_eq (α : OmegaOne) :
    stageSetStructure (C.stage α) = submodel ((C.stage α).carrier) := by
  have h : (fun (y x : ↥(C.stage α).carrier) ↦ (C.stage α).mem x y) =
      fun (y x : ↥(C.stage α).carrier) ↦ (x : Ω) ∈ (y : Ω) := by
    funext y x
    exact propext (C.stageMem_iff_coe_mem α x y)
  show (⟨fun y x ↦ (C.stage α).mem x y⟩ : SetStructure ↥(C.stage α).carrier) =
    ⟨fun y x ↦ (x : Ω) ∈ (y : Ω)⟩
  rw [h]

/-- The elementary inclusion of one stage into a later one, read with the membership structures
restricted from `Ω`. -/
def submodelStep {α β : OmegaOne} (h : α ≤ β) :
    @ElementaryMap _ _ (submodel ((C.stage α).carrier)) (submodel ((C.stage β).carrier)) :=
  @ElementaryMap.mk _ _ (submodel ((C.stage α).carrier)) (submodel ((C.stage β).carrier))
    (StageModel.incl (S := C.stage α) (T := C.stage β) (C.inc h)) (by
      rw [← C.stageSetStructure_eq α, ← C.stageSetStructure_eq β,
        ← funext (C.step_apply h)]
      exact fun φ b f ↦ (C.step h).elementary φ b f)

@[simp] theorem submodelStep_apply {α β : OmegaOne} (h : α ≤ β) (x : ↥(C.stage α).carrier) :
    ElementaryMap.fn _ _ (C.submodelStep h) x =
      StageModel.incl (S := C.stage α) (T := C.stage β) (C.inc h) x := rfl

theorem coe_submodelStep {α β : OmegaOne} (h : α ≤ β) (x : ↥(C.stage α).carrier) :
    ((ElementaryMap.fn _ _ (C.submodelStep h) x : ↥(C.stage β).carrier) : Ω) = (x : Ω) := rfl

/-! ## The chain of subsets of `Ω` -/

/-- The chain of stages read as a chain of subsets of `Ω`. Its `embedding` is the elementary
inclusion of a stage into the whole union. -/
noncomputable def toSubmodelChain : SubmodelChain Ω OmegaOne where
  carrier α := (C.stage α).carrier
  mono _ _ h := C.inc h
  cover := C.cover
  step h := C.submodelStep h
  step_apply h x := C.coe_submodelStep h x

@[simp] theorem toSubmodelChain_carrier (α : OmegaOne) :
    C.toSubmodelChain.carrier α = (C.stage α).carrier := rfl

/-- Every stage is an elementary submodel of the union, by the inclusion. -/
theorem toSubmodelChain_embedding_apply (α : OmegaOne) (x : ↥(C.stage α).carrier) :
    C.toSubmodelChain.embedding α x = (x : Ω) := rfl

/-- If one stage models ZF, so does the union. The hypothesis uses the stage's own membership
structure, which is the one the construction produces. -/
theorem models_zf [Nonempty Ω] (α : OmegaOne) [Nonempty ↥(C.stage α).carrier]
    (hzf : (↥(C.stage α).carrier)↓[ℒₛₑₜ] ⊧* 𝗭𝗙) : Ω↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  rw [C.stageSetStructure_eq α] at hzf
  have : Nonempty ↥(C.toSubmodelChain.carrier α) :=
    inferInstanceAs (Nonempty ↥(C.stage α).carrier)
  exact C.toSubmodelChain.models_zf α hzf

end StageChain

/-! ## The same, with the hypotheses spelled out -/

section Unbundled

variable [SetStructure Ω] (S : OmegaOne → StageModel Ω) (hinc : IsIncreasingStages S)
  (hagr : StagesAgree S) (hcov : StagesCover S)
  (hunion : ∀ x y : Ω, x ∈ y ↔ unionMem S x y)
  (j : ∀ {α β : OmegaOne}, α ≤ β →
    @ElementaryMap _ _ (stageSetStructure (S α)) (stageSetStructure (S β)))
  (hj : ∀ {α β : OmegaOne} (h : α ≤ β) (x : ↥(S α).carrier),
    (j h : ↥(S α).carrier → ↥(S β).carrier) x =
      StageModel.incl (S := S α) (T := S β) (hinc h) x)

/-- The chain of stages as a `StageChain`, from the hypotheses one at a time. -/
def stageChain : StageChain Ω :=
  ⟨S, hinc, hagr, hcov, hunion, fun {_ _} h ↦ j h, fun {_ _} h x ↦ hj h x⟩

@[simp] theorem stageChain_stage : (stageChain S hinc hagr hcov hunion j hj).stage = S := rfl

/-- The union of the chain, as a chain of subsets of `Ω` along which the inclusions are
elementary. -/
noncomputable def stageUnionChain : SubmodelChain Ω OmegaOne :=
  (stageChain S hinc hagr hcov hunion j hj).toSubmodelChain

@[simp] theorem stageUnionChain_carrier (α : OmegaOne) :
    (stageUnionChain S hinc hagr hcov hunion j hj).carrier α = (S α).carrier := rfl

/-- Each stage is an elementary submodel of the union, by the inclusion. -/
theorem stageUnion_embedding_apply (α : OmegaOne) (x : ↥(S α).carrier) :
    (stageUnionChain S hinc hagr hcov hunion j hj).embedding α x = (x : Ω) := rfl

end Unbundled

/-! ## The chain as a Rubin chain -/

/-- The chain of stages as a `ZFVP.RubinChain`. The six fields that do not mention definability
come from the chain; the two that do, `upper` and `reflect`, are properties of the construction
and are passed in. -/
noncomputable def StageChain.toRubinChain [SetStructure Ω] [Nonempty Ω] [Ω↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (C : StageChain Ω) (hcount : ∀ α, ((C.stage α).carrier).Countable)
    (hupper : ∀ (α γ : OmegaOne), α ≤ γ → ∀ (P : Ω → Prop) (le : Ω → Ω → Prop),
      DefinableOver ((C.stage α).carrier) P → DefinableOverRel ((C.stage α).carrier) le →
      IsPartialOrderOn P le → IsDirectedNoMaxOn P le →
      ∃ d, P d ∧ (∀ x, x ∈ (C.stage γ).carrier → P x → le x d ∧ x ≠ d) ∧
        ∀ γ', γ < γ' → d ∈ (C.stage γ').carrier)
    (hreflect : ∀ (P : Ω → Prop) (le : Ω → Ω → Prop), (ℒₛₑₜ-predicate[Ω] P) →
      (ℒₛₑₜ-relation[Ω] le) → IsPartialOrderOn P le → ∀ F : Ω → Prop,
      IsMaximallyCompatibleOn P le F → HasCofinalOmegaOneChainOn le F → ¬ (ℒₛₑₜ-predicate[Ω] F) →
      ∃ α : OmegaOne,
        (∀ q, q ∈ (C.stage α).carrier → P q → ¬ F q →
           ∃ p, p ∈ (C.stage α).carrier ∧ F p ∧ ¬ ∃ z, P z ∧ le p z ∧ le q z) ∧
        Inseparable Ω (fun x ↦ x ∈ (C.stage α).carrier ∧ F x)
          (fun x ↦ x ∈ (C.stage α).carrier ∧ ¬ F x)) : RubinChain Ω where
  stage α := (C.stage α).carrier
  mono _ _ h := C.inc h
  cover := C.cover
  countable := hcount
  emb α := C.toSubmodelChain.embedding α
  emb_apply _ _ := rfl
  upper := hupper
  reflect := hreflect

@[simp] theorem StageChain.toRubinChain_stage [SetStructure Ω] [Nonempty Ω]
    [Ω↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (C : StageChain Ω)
    (hcount : ∀ α, ((C.stage α).carrier).Countable) {hupper hreflect} (α : OmegaOne) :
    (C.toRubinChain hcount hupper hreflect).stage α = (C.stage α).carrier := rfl

theorem StageChain.toRubinChain_emb_apply [SetStructure Ω] [Nonempty Ω]
    [Ω↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (C : StageChain Ω)
    (hcount : ∀ α, ((C.stage α).carrier).Countable) {hupper hreflect} (α : OmegaOne)
    (x : ↥(C.stage α).carrier) :
    (C.toRubinChain hcount hupper hreflect).emb α x = (x : Ω) := rfl

end ZFVP
