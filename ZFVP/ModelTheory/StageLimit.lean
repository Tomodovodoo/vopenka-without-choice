import ZFVP.ModelTheory.StageSuccessor
import ZFVP.ModelTheory.SubmodelChain

/-! # The limit step of Enayat's ω₁-length construction

At a limit ordinal `α`, Stage 1 of the Appendix of Enayat's paper sets `M_α = ⋃_{β<α} M_β`. This
file proves what that step needs: the union of an increasing family of stages, each one an
elementary substructure of the later ones, is again a stage, and every member of the family is an
elementary substructure of it.

The index type here is any linear order `J`. For the limit step take `J := ↥(Set.Iio α)` inside
`OmegaOne`; nothing below uses more than the order.

* `limitMem S x y` says that `x` is an element of `y` inside some stage of the family, and
  `limitStage S` is the stage whose carrier is `⋃ i, (S i).carrier` and whose membership relation
  is `limitMem S`.
* `limitMem_iff_stage` and `limitStage_mem_iff` are coherence: on a fixed stage the union relation
  is that stage's own relation. Two stages are compared by moving both into their maximum.
* `StageFamily Ω J` bundles a family with the three hypotheses it has to satisfy (increasing,
  agreeing, and elementary inclusions of one stage into the next).
* `StageFamily.embedding` is the elementary inclusion of a stage into the limit, obtained from
  `SubmodelChain.embedding`, and `StageFamily.embedding_apply` says its underlying function is
  `StageModel.incl`.
* `limitStage_carrier_countable`, `limitStage_nonempty` and `StageFamily.models_zf` carry
  countability, nonemptiness and ZF up to the limit.
* `stageFamily`, `stageLimitEmbedding` and `stageLimitEmbedding_apply` are the same with the
  hypotheses passed one at a time instead of bundled.

## Which membership structure

`↥(S i).carrier` carries the stage's own relation `ZFVP.stageSetStructure (S i)`, coming from the
field `StageModel.mem`; that is the instance typeclass search picks, and every statement below
about a stage or about `limitStage S` is read with it. `Ω` itself is given no membership structure
in this file, so Foundation's `submodel` never applies to `(S i).carrier`.

The ambient structure of the `SubmodelChain` built here is `↥(limitStage S).carrier` with
`stageSetStructure (limitStage S)`. Its stages are the subsets `limitPre S i` of that type, on
which Foundation's `submodel` is the instance in force; `limitEquiv` is the bijection between
`↥(S i).carrier` and `↥(limitPre S i)`, and it is a membership isomorphism exactly by the
coherence lemma. `limitFn` reads the underlying function of an elementary map with both structures
given explicitly, for statements where search would pick the wrong one.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

variable {Ω : Type u} {J : Type} [LinearOrder J]

/-- The underlying function of an elementary map, with both membership structures given
explicitly. -/
def limitFn {A B : Type*} (iA : SetStructure A) (iB : SetStructure B)
    (e : @ElementaryMap A B iA iB) : A → B :=
  @ElementaryMap.toFun A B iA iB e

/-! ## The union stage -/

/-- Membership in the union of a family of stages: `x` is an element of `y` if some stage of the
family contains both and thinks so. -/
def limitMem (S : J → StageModel Ω) (x y : Ω) : Prop :=
  ∃ (i : J) (hx : x ∈ (S i).carrier) (hy : y ∈ (S i).carrier), (S i).mem ⟨x, hx⟩ ⟨y, hy⟩

/-- The union of a family of stages: the union of the carriers, with the union of the membership
relations. -/
def limitStage (S : J → StageModel Ω) : StageModel Ω where
  carrier := ⋃ i, (S i).carrier
  mem x y := limitMem S (x : Ω) (y : Ω)

omit [LinearOrder J] in
@[simp] theorem limitStage_carrier (S : J → StageModel Ω) :
    (limitStage S).carrier = ⋃ i, (S i).carrier := rfl

omit [LinearOrder J] in
@[simp] theorem limitStage_mem (S : J → StageModel Ω) (x y : ↥(limitStage S).carrier) :
    (limitStage S).mem x y ↔ limitMem S (x : Ω) (y : Ω) := Iff.rfl

omit [LinearOrder J] in
/-- Every stage of the family includes in the union. -/
theorem subset_limitStage (S : J → StageModel Ω) (i : J) :
    (S i).carrier ⊆ (limitStage S).carrier :=
  Set.subset_iUnion (fun i ↦ (S i).carrier) i

/-- The carriers of the family increase along the index order. -/
def IsIncreasingFamily (S : J → StageModel Ω) : Prop :=
  ∀ ⦃i k : J⦄, i ≤ k → (S i).carrier ⊆ (S k).carrier

/-- A later stage restricts to the membership relation of an earlier one. -/
def FamilyAgrees (S : J → StageModel Ω) : Prop :=
  ∀ ⦃i k : J⦄, i ≤ k → ∀ (x y : ↥(S i).carrier)
    (hx : (x : Ω) ∈ (S k).carrier) (hy : (y : Ω) ∈ (S k).carrier),
    (S i).mem x y ↔ (S k).mem ⟨x, hx⟩ ⟨y, hy⟩

/-! ## Coherence -/

/-- On a fixed stage, membership in the union is membership in that stage. Two stages are compared
by pushing both of them into their maximum. -/
theorem limitMem_iff_stage {S : J → StageModel Ω} (hinc : IsIncreasingFamily S)
    (hagr : FamilyAgrees S) (i : J) {x y : Ω} (hx : x ∈ (S i).carrier)
    (hy : y ∈ (S i).carrier) : limitMem S x y ↔ (S i).mem ⟨x, hx⟩ ⟨y, hy⟩ := by
  constructor
  · rintro ⟨k, hx', hy', h⟩
    have hik : i ≤ max i k := le_max_left i k
    have hkk : k ≤ max i k := le_max_right i k
    rw [hagr hik ⟨x, hx⟩ ⟨y, hy⟩ (hinc hik hx) (hinc hik hy)]
    rw [hagr hkk ⟨x, hx'⟩ ⟨y, hy'⟩ (hinc hkk hx') (hinc hkk hy')] at h
    exact h
  · exact fun h ↦ ⟨i, hx, hy, h⟩

/-- The inclusion of a stage into the union preserves and reflects the membership relation. -/
theorem limitStage_mem_iff {S : J → StageModel Ω} (hinc : IsIncreasingFamily S)
    (hagr : FamilyAgrees S) (i : J) (x y : ↥(S i).carrier) :
    (S i).mem x y ↔ (limitStage S).mem (StageModel.incl (subset_limitStage S i) x)
      (StageModel.incl (subset_limitStage S i) y) := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  exact (limitMem_iff_stage hinc hagr i hx hy).symm

/-! ## The stage seen inside the union -/

/-- The points of the union that come from stage `i`. This is `(S i).carrier` read as a subset of
`↥(limitStage S).carrier`, which is the shape `SubmodelChain` wants. -/
def limitPre (S : J → StageModel Ω) (i : J) : Set ↥(limitStage S).carrier :=
  {z | (z : Ω) ∈ (S i).carrier}

/-- The bijection between a stage and its copy inside the union. -/
def limitEquiv (S : J → StageModel Ω) (i : J) : ↥(S i).carrier ≃ ↥(limitPre S i) where
  toFun x := ⟨⟨(x : Ω), subset_limitStage S i x.2⟩, x.2⟩
  invFun z := ⟨(z.1 : Ω), z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [LinearOrder J] in
@[simp] theorem coe_limitEquiv (S : J → StageModel Ω) (i : J) (x : ↥(S i).carrier) :
    (((limitEquiv S i x : ↥(limitPre S i)) : ↥(limitStage S).carrier) : Ω) = (x : Ω) := rfl

omit [LinearOrder J] in
@[simp] theorem coe_limitEquiv_symm (S : J → StageModel Ω) (i : J) (z : ↥(limitPre S i)) :
    (((limitEquiv S i).symm z : ↥(S i).carrier) : Ω) = ((z : ↥(limitStage S).carrier) : Ω) := rfl

/-- `limitEquiv` is a membership isomorphism from the stage's own relation to the relation the
union induces on the copy of the stage. -/
theorem limitEquiv_mem_iff {S : J → StageModel Ω} (hinc : IsIncreasingFamily S)
    (hagr : FamilyAgrees S) (i : J) (x y : ↥(S i).carrier) :
    limitEquiv S i x ∈ limitEquiv S i y ↔ x ∈ y := by
  show limitMem S (x : Ω) (y : Ω) ↔ (S i).mem x y
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  exact limitMem_iff_stage hinc hagr i hx hy

theorem limitEquiv_symm_mem_iff {S : J → StageModel Ω} (hinc : IsIncreasingFamily S)
    (hagr : FamilyAgrees S) (i : J) (z w : ↥(limitPre S i)) :
    (limitEquiv S i).symm z ∈ (limitEquiv S i).symm w ↔ z ∈ w := by
  rw [← limitEquiv_mem_iff hinc hagr i, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The stage, as an elementary submodel of its copy inside the union. -/
def limitEquivMap {S : J → StageModel Ω} (hinc : IsIncreasingFamily S) (hagr : FamilyAgrees S)
    (i : J) : ElementaryMap ↥(S i).carrier ↥(limitPre S i) :=
  ElementaryMap.ofMembershipIso (limitEquiv S i) (limitEquiv_mem_iff hinc hagr i)

@[simp] theorem limitEquivMap_apply {S : J → StageModel Ω} (hinc : IsIncreasingFamily S)
    (hagr : FamilyAgrees S) (i : J) (x : ↥(S i).carrier) :
    limitEquivMap hinc hagr i x = limitEquiv S i x := rfl

/-- The inverse bijection, as an elementary map. -/
def limitEquivSymmMap {S : J → StageModel Ω} (hinc : IsIncreasingFamily S)
    (hagr : FamilyAgrees S) (i : J) : ElementaryMap ↥(limitPre S i) ↥(S i).carrier :=
  ElementaryMap.ofMembershipIso (limitEquiv S i).symm (limitEquiv_symm_mem_iff hinc hagr i)

@[simp] theorem limitEquivSymmMap_apply {S : J → StageModel Ω} (hinc : IsIncreasingFamily S)
    (hagr : FamilyAgrees S) (i : J) (z : ↥(limitPre S i)) :
    limitEquivSymmMap hinc hagr i z = (limitEquiv S i).symm z := rfl

/-! ## Families with elementary inclusions -/

variable (Ω J) in
/-- An increasing family of stages, indexed by a linear order, whose membership relations agree
and whose inclusions of one stage into a later one are elementary.

`step` and `step_apply` are elementarity of the inclusions, read with the stages' own membership
structures. No coherence between the `step` maps is asked for, because they are inclusions. -/
structure StageFamily where
  /-- The stage of index `i`, a subset of `Ω` with a membership relation on it. -/
  stage : J → StageModel Ω
  /-- The carriers increase. -/
  inc : IsIncreasingFamily stage
  /-- Later stages restrict to earlier ones. -/
  agree : FamilyAgrees stage
  /-- The inclusion of a stage into a later one is elementary. -/
  step : ∀ {i k : J}, i ≤ k →
    @ElementaryMap _ _ (stageSetStructure (stage i)) (stageSetStructure (stage k))
  /-- The elementary map `step` is the inclusion. -/
  step_apply : ∀ {i k : J} (h : i ≤ k) (x : ↥(stage i).carrier),
    (step h : ↥(stage i).carrier → ↥(stage k).carrier) x =
      StageModel.incl (S := stage i) (T := stage k) (inc h) x

namespace StageFamily

variable (F : StageFamily Ω J)

/-- The limit of the family: the union of its stages. -/
def limit : StageModel Ω := limitStage F.stage

@[simp] theorem limit_carrier : F.limit.carrier = ⋃ i, (F.stage i).carrier := rfl

/-- The elementary inclusion of one stage into a later one, read on the copies of the stages
inside the union. -/
def limitStep {i k : J} (h : i ≤ k) :
    ElementaryMap ↥(limitPre F.stage i) ↥(limitPre F.stage k) :=
  (limitEquivMap F.inc F.agree k).comp ((F.step h).comp (limitEquivSymmMap F.inc F.agree i))

/-- `limitStep` does not move the underlying point of `Ω`. -/
theorem coe_limitStep {i k : J} (h : i ≤ k) (z : ↥(limitPre F.stage i)) :
    (((F.limitStep h z : ↥(limitPre F.stage k))
        : ↥(limitStage F.stage).carrier) : Ω) = ((z : ↥(limitStage F.stage).carrier) : Ω) := by
  show (((F.step h ((limitEquiv F.stage i).symm z) : ↥(F.stage k).carrier)) : Ω) = _
  rw [F.step_apply h]
  rfl

/-- The family, read as a chain of subsets of the union along which the inclusions are
elementary. -/
noncomputable def toSubmodelChain : SubmodelChain ↥(limitStage F.stage).carrier J where
  carrier := limitPre F.stage
  mono _ _ h _ hz := F.inc h hz
  cover z := by
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp z.2
    exact ⟨t, ht⟩
  step h := F.limitStep h
  step_apply h z := Subtype.ext (F.coe_limitStep h z)

@[simp] theorem toSubmodelChain_carrier (i : J) :
    F.toSubmodelChain.carrier i = limitPre F.stage i := rfl

/-- Every stage of the family is an elementary submodel of the union, by the inclusion. This is
the elementary chain theorem for the limit step. -/
noncomputable def embedding (i : J) :
    @ElementaryMap _ _ (stageSetStructure (F.stage i)) (stageSetStructure (limitStage F.stage)) :=
  (F.toSubmodelChain.embedding i).comp (limitEquivMap F.inc F.agree i)

/-- The underlying function of `StageFamily.embedding` is the inclusion of the carriers. -/
@[simp] theorem embedding_apply (i : J) (x : ↥(F.stage i).carrier) :
    limitFn _ _ (F.embedding i) x = StageModel.incl (subset_limitStage F.stage i) x := rfl

theorem coe_embedding (i : J) (x : ↥(F.stage i).carrier) :
    ((limitFn _ _ (F.embedding i) x : ↥(limitStage F.stage).carrier) : Ω) = (x : Ω) := rfl

/-- The inclusion of a stage into the union preserves and reflects membership. -/
theorem embedding_mem_iff (i : J) (x y : ↥(F.stage i).carrier) :
    (F.stage i).mem x y ↔
      (limitStage F.stage).mem (limitFn _ _ (F.embedding i) x) (limitFn _ _ (F.embedding i) y) :=
  limitStage_mem_iff F.inc F.agree i x y

/-- If a stage models ZF, so does the union. Both sides are read with the stage's own membership
structure. -/
theorem models_zf [Nonempty ↥(limitStage F.stage).carrier] (i : J)
    [hne : Nonempty ↥(F.stage i).carrier] (hzf : (↥(F.stage i).carrier)↓[ℒₛₑₜ] ⊧* 𝗭𝗙) :
    (↥(limitStage F.stage).carrier)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  have hpre : Nonempty ↥(limitPre F.stage i) := hne.map (limitEquiv F.stage i)
  have : Nonempty ↥(F.toSubmodelChain.carrier i) := hpre
  refine F.toSubmodelChain.models_zf i ?_
  refine ⟨?_⟩
  intro φ hφ
  have hs := Theory.models (↥(F.stage i).carrier) 𝗭𝗙 hφ
  change φ.Eval ![] Empty.elim at hs
  have he := ((limitEquivMap F.inc F.agree i).elementary φ ![] Empty.elim).mp hs
  have hf : ((limitEquivMap F.inc F.agree i) ∘ (Empty.elim : Empty → ↥(F.stage i).carrier)) =
      Empty.elim := funext fun x ↦ Empty.elim x
  have hb : ((limitEquivMap F.inc F.agree i) ∘ (![] : Fin 0 → ↥(F.stage i).carrier)) = ![] :=
    funext fun l ↦ Fin.elim0 l
  rw [hf, hb] at he
  exact he

end StageFamily

/-! ## The same, with the hypotheses spelled out -/

section Unbundled

variable (S : J → StageModel Ω) (hinc : IsIncreasingFamily S) (hagr : FamilyAgrees S)
  (step : ∀ {i k : J}, i ≤ k →
    @ElementaryMap _ _ (stageSetStructure (S i)) (stageSetStructure (S k)))
  (step_apply : ∀ {i k : J} (h : i ≤ k) (x : ↥(S i).carrier),
    (step h : ↥(S i).carrier → ↥(S k).carrier) x =
      StageModel.incl (S := S i) (T := S k) (hinc h) x)

/-- The family as a `StageFamily`, from the hypotheses one at a time. -/
def stageFamily : StageFamily Ω J :=
  ⟨S, hinc, hagr, fun {_ _} h ↦ step h, fun {_ _} h x ↦ step_apply h x⟩

@[simp] theorem stageFamily_stage :
    (stageFamily S hinc hagr step step_apply).stage = S := rfl

/-- The elementary inclusion of a stage into the limit. -/
noncomputable def stageLimitEmbedding (i : J) :
    @ElementaryMap _ _ (stageSetStructure (S i)) (stageSetStructure (limitStage S)) :=
  (stageFamily S hinc hagr step step_apply).embedding i

@[simp] theorem stageLimitEmbedding_apply (i : J) (x : ↥(S i).carrier) :
    limitFn _ _ (stageLimitEmbedding S hinc hagr step step_apply i) x =
      StageModel.incl (subset_limitStage S i) x := rfl

end Unbundled

/-! ## Countability and nonemptiness -/

omit [LinearOrder J] in
/-- The union of countably many countable stages is countable. -/
theorem limitStage_carrier_countable (S : J → StageModel Ω) [Countable J]
    (hcount : ∀ i, ((S i).carrier).Countable) : ((limitStage S).carrier).Countable :=
  Set.countable_iUnion hcount

omit [LinearOrder J] in
/-- The union is nonempty as soon as one stage is. -/
theorem limitStage_nonempty (S : J → StageModel Ω) (i : J) (h : Nonempty ↥(S i).carrier) :
    Nonempty ↥(limitStage S).carrier :=
  h.map (StageModel.incl (subset_limitStage S i))

end ZFVP
