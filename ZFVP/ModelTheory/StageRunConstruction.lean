import ZFVP.ModelTheory.StageClubs
import ZFVP.ModelTheory.StageDefinability
import ZFVP.ModelTheory.FiniteStageSuccessorPoint

/-! # The ω₁-length recursion of Stage 1 of Enayat's Appendix

`ZFVP.StageRun M Ω` records everything Stage 1 of the Appendix of Enayat's paper produces. This
file runs the recursion that produces it: `ZFVP.exists_stageRun`.

The stages are built by recursion on `α : OmegaOne` with access to the whole family below `α`.

* If nothing lies below `α`, the stage is the base stage, the countable model `M` placed on a
  countable subset of `Ω` by `ZFVP.exists_carrier_embedding`.
* If `α` has an immediate predecessor `p`, the stage is the one `ZFVP.exists_stage_successor_point`
  builds over the stage at `p`, with the point `code p` of the carrier put in and with the
  obligation set `{((stage β).carrier ∩ guess β, (stage β).carrier \ guess β) | β < α}`.
* Otherwise `α` is a limit index and the stage is `ZFVP.limitStage` of the family below `α`.

The successor step is made total by `ZFVP.succStage`, a choice over `ZFVP.SuccSpec` together with `ZFVP.StagePreservesFinite`, the conclusion
of `exists_stage_successor_point` read as a property of the new stage, with the old stage as the
fallback value. `ZFVP.succSpec_succStage` says the property holds whenever the hypotheses of that
theorem do, and along the recursion they always do.

Four invariants are carried by transfinite induction (`ZFVP.stageRunRec_inv`): each stage is countable,
nonempty and models ZF; `ZFVP.StageLe` holds between any earlier stage and the stage at `α`, which
is the inclusion of carriers together with agreement of the two membership relations and
elementarity of the inclusion; and a pair guessed at `β ≤ α` and inseparable there stays inseparable
at `α`. Continuity at limit indices holds by the definition of `limitStage`.

`StageLe` is a `Prop`, so the induction hypothesis is a proposition; the elementary map it asserts
is recovered by choice as `ZFVP.StageLe.map` where the fields `elem` and `succ_bound` of `StageRun`
need it.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

/-! ## Index arithmetic in `ω₁` -/

/-- `p` is the immediate predecessor of `α`: it lies below `α` and bounds everything below `α`. -/
def IsPredIndex (p α : OmegaOne) : Prop := p < α ∧ ∀ β, β < α → β ≤ p

theorem IsPredIndex.unique {p q α : OmegaOne} (hp : IsPredIndex p α) (hq : IsPredIndex q α) :
    p = q := le_antisymm (hq.2 p hp.1) (hp.2 q hq.1)

theorem not_isPredIndex_of_isLimitIndex {α : OmegaOne} (h : IsLimitIndex α) (p : OmegaOne) :
    ¬ IsPredIndex p α := by
  rintro ⟨hp, hmax⟩
  obtain ⟨γ, hpγ, hγα⟩ := h.2 p hp
  exact absurd (hmax γ hγα) (not_le.mpr hpγ)

theorem not_isPredIndex_of_not_exists_lt {α : OmegaOne} (h : ¬ ∃ β, β < α) (p : OmegaOne) :
    ¬ IsPredIndex p α := fun hp ↦ h ⟨p, hp.1⟩

/-- The index immediately above `α`. A successor of a countable ordinal is countable, so this
stays inside `ω₁`. -/
noncomputable def succIndex (α : OmegaOne) : OmegaOne :=
  Ordinal.enum (α := OmegaOne) (· < ·)
    ⟨Order.succ (Ordinal.typein (α := OmegaOne) (· < ·) α), by
      rw [type_omegaOne]
      exact (Cardinal.isSuccLimit_omega 1).succ_lt (typein_lt_omegaOne α)⟩

theorem typein_succIndex (α : OmegaOne) :
    Ordinal.typein (α := OmegaOne) (· < ·) (succIndex α) =
      Order.succ (Ordinal.typein (α := OmegaOne) (· < ·) α) :=
  Ordinal.typein_enum _ _

/-- `succIndex α` is the immediate successor of `α`. -/
theorem isPredIndex_succIndex (α : OmegaOne) : IsPredIndex α (succIndex α) := by
  constructor
  · refine (Ordinal.typein_lt_typein (α := OmegaOne) (· < ·)).mp ?_
    rw [typein_succIndex]
    exact Order.lt_succ _
  · intro β hβ
    have h : Ordinal.typein (α := OmegaOne) (· < ·) β <
        Order.succ (Ordinal.typein (α := OmegaOne) (· < ·) α) := by
      rw [← typein_succIndex]
      exact (Ordinal.typein_lt_typein (α := OmegaOne) (· < ·)).mpr hβ
    exact (Ordinal.typein_le_typein' _).mp (Order.lt_succ_iff.mp h)

/-- `ω₁` has a least index, since it is well founded and nonempty. -/
theorem exists_leastIndex : ∃ α : OmegaOne, ¬ ∃ β, β < α := by
  obtain ⟨α, -, hα⟩ := (IsWellFounded.wf (α := OmegaOne) (r := (· < ·))).has_min Set.univ
    ⟨Classical.arbitrary OmegaOne, Set.mem_univ _⟩
  exact ⟨α, fun h ↦ hα h.choose (Set.mem_univ _) h.choose_spec⟩

/-- The least index of `ω₁`. -/
noncomputable def leastIndex : OmegaOne := exists_leastIndex.choose

theorem not_exists_lt_leastIndex : ¬ ∃ β : OmegaOne, β < leastIndex :=
  exists_leastIndex.choose_spec

/-! ## One step of the construction -/

section Construction

variable {Ω : Type u}

/-- What `ZFVP.exists_stage_successor_point` promises about the stage it builds over `S`, read as
a property of the new stage `T`. -/
def SuccSpec (S T : StageModel Ω) (O : Set (Set Ω × Set Ω)) (x₀ : Ω) : Prop :=
  ∃ hsub : S.carrier ⊆ T.carrier,
    T.carrier.Countable ∧ x₀ ∈ T.carrier ∧
    (∀ x y : ↥S.carrier, x ∈ y ↔ StageModel.incl hsub x ∈ StageModel.incl hsub y) ∧
    (∃ j : ElementaryMap ↥S.carrier ↥T.carrier, ∀ x, j x = StageModel.incl hsub x) ∧
    (∀ p ∈ O, Inseparable ↥S.carrier (fun x ↦ (x : Ω) ∈ p.1) (fun x ↦ (x : Ω) ∈ p.2) →
      Inseparable ↥T.carrier (fun y ↦ (y : Ω) ∈ p.1) (fun y ↦ (y : Ω) ∈ p.2)) ∧
    (∀ (dφ : SetTheorySemiformula ↥S.carrier 1) (rφ : SetTheorySemiformula ↥S.carrier 2),
      DirectedNoLast (fun x ↦ dφ.Eval ![x] id) (fun x y ↦ rφ.Eval ![x, y] id) →
      ∃ t : ↥T.carrier,
        dφ.Eval ![t] (fun m ↦ StageModel.incl hsub m) ∧
        ∀ m : ↥S.carrier, dφ.Eval ![m] id →
          rφ.Eval ![StageModel.incl hsub m, t] (fun m ↦ StageModel.incl hsub m))

/-- Every member of an old internally finite set was already in the old stage. -/
def StagePreservesFinite (S T : StageModel Ω) : Prop :=
  ∀ [Nonempty ↥S.carrier] [(↥S.carrier)↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
    ∀ hsub : S.carrier ⊆ T.carrier, ∀ a : ↥S.carrier, IsInternallyFinite a →
      ∀ b : ↥T.carrier, b ∈ StageModel.incl hsub a →
        ∃ m ∈ a, StageModel.incl hsub m = b

open Classical in
/-- The successor step as a total operation: a stage satisfying `SuccSpec` and preserving old
internally finite sets if there is one, and
the old stage otherwise. -/
noncomputable def succStage (S : StageModel Ω) (O : Set (Set Ω × Set Ω)) (x₀ : Ω) :
    StageModel Ω :=
  if h : ∃ T, SuccSpec S T O x₀ ∧ StagePreservesFinite S T then h.choose else S

/-- `succStage` does what the successor step promises, whenever the hypotheses of
`ZFVP.exists_stage_successor_point` hold. -/
theorem succSpec_succStage (hΩ : Cardinal.mk Ω = Cardinal.aleph 1) (S : StageModel Ω)
    (hcount : S.carrier.Countable) [Nonempty ↥S.carrier] [(↥S.carrier)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (O : Set (Set Ω × Set Ω)) (hO : O.Countable)
    (hOsub : ∀ p ∈ O, p.1 ⊆ S.carrier ∧ p.2 ⊆ S.carrier) (x₀ : Ω) :
    SuccSpec S (succStage S O x₀) O x₀ := by
  have h : ∃ T, SuccSpec S T O x₀ ∧ StagePreservesFinite S T := by
    obtain ⟨T, hsub, hc, hx, hf, hm, hj, hi, hb⟩ :=
      exists_finite_stage_successor_point hΩ S hcount O hO hOsub x₀
    exact ⟨T, ⟨hsub, hc, hx, hm, hj, hi, hb⟩, by intro _ _ h; exact hf⟩
  rw [succStage, dif_pos h]
  exact h.choose_spec.1

/-- The chosen successor never adds a member to an old internally finite set. -/
theorem stagePreservesFinite_succStage (S : StageModel Ω)
    (O : Set (Set Ω × Set Ω)) (x₀ : Ω) :
    StagePreservesFinite S (succStage S O x₀) := by
  classical
  by_cases h : ∃ T, SuccSpec S T O x₀ ∧ StagePreservesFinite S T
  · rw [succStage, dif_pos h]
    exact h.choose_spec.2
  · rw [succStage, dif_neg h]
    intro hsub a ha b hb
    exact ⟨b, hb, rfl⟩

/-- The obligation set at `α`, read off a family of stages indexed by the indices below `α`: the
pair the guess at `β` cuts out of the stage at `β`, for every `β < α`. -/
def obligSetOn {α : OmegaOne} (f : ↥(Set.Iio α) → StageModel Ω) (guess : OmegaOne → Set Ω) :
    Set (Set Ω × Set Ω) :=
  Set.range fun β : ↥(Set.Iio α) ↦ ((f β).carrier ∩ guess (β : OmegaOne),
    (f β).carrier \ guess (β : OmegaOne))

theorem obligSetOn_countable {α : OmegaOne} (f : ↥(Set.Iio α) → StageModel Ω)
    (guess : OmegaOne → Set Ω) : (obligSetOn f guess).Countable := by
  have : Countable ↥(Set.Iio α) := (countable_Iio_omegaOne α).to_subtype
  exact Set.countable_range _

theorem mem_obligSetOn {α : OmegaOne} (f : ↥(Set.Iio α) → StageModel Ω)
    (guess : OmegaOne → Set Ω) (β : ↥(Set.Iio α)) :
    ((f β).carrier ∩ guess (β : OmegaOne), (f β).carrier \ guess (β : OmegaOne)) ∈
      obligSetOn f guess := ⟨β, rfl⟩

open Classical in
/-- One step of the recursion, reading the whole family below `α`. -/
noncomputable def stepAt (base : StageModel Ω) (code : OmegaOne ≃ Ω) (guess : OmegaOne → Set Ω)
    (α : OmegaOne) (f : ↥(Set.Iio α) → StageModel Ω) : StageModel Ω :=
  if hp : ∃ p, IsPredIndex p α then
    succStage (f ⟨hp.choose, hp.choose_spec.1⟩) (obligSetOn f guess) (code hp.choose)
  else if ∃ β : OmegaOne, β < α then limitStage f else base

/-- The stages of Enayat's ω₁-length construction. -/
noncomputable def stageRunRec (base : StageModel Ω) (code : OmegaOne ≃ Ω)
    (guess : OmegaOne → Set Ω) (α : OmegaOne) : StageModel Ω :=
  stepAt base code guess α fun β : ↥(Set.Iio α) ↦ stageRunRec base code guess (β : OmegaOne)
termination_by α
decreasing_by exact β.2

theorem stageRunRec_eq (base : StageModel Ω) (code : OmegaOne ≃ Ω) (guess : OmegaOne → Set Ω)
    (α : OmegaOne) :
    stageRunRec base code guess α =
      stepAt base code guess α fun β : ↥(Set.Iio α) ↦ stageRunRec base code guess (β : OmegaOne) := by
  rw [stageRunRec]

theorem stageRunRec_base (base : StageModel Ω) (code : OmegaOne ≃ Ω) (guess : OmegaOne → Set Ω)
    {α : OmegaOne} (h : ¬ ∃ β : OmegaOne, β < α) : stageRunRec base code guess α = base := by
  rw [stageRunRec_eq, stepAt, dif_neg (fun hp ↦ not_isPredIndex_of_not_exists_lt h _ hp.choose_spec),
    if_neg h]

theorem stageRunRec_succ (base : StageModel Ω) (code : OmegaOne ≃ Ω) (guess : OmegaOne → Set Ω)
    {p α : OmegaOne} (h : IsPredIndex p α) :
    stageRunRec base code guess α =
      succStage (stageRunRec base code guess p)
        (obligSetOn (fun β : ↥(Set.Iio α) ↦ stageRunRec base code guess (β : OmegaOne)) guess)
        (code p) := by
  have hp : ∃ q, IsPredIndex q α := ⟨p, h⟩
  have hchoose : hp.choose = p := (hp.choose_spec.unique h)
  rw [stageRunRec_eq, stepAt, dif_pos hp]
  simp only [hchoose]

theorem stageRunRec_limit (base : StageModel Ω) (code : OmegaOne ≃ Ω) (guess : OmegaOne → Set Ω)
    {α : OmegaOne} (h : IsLimitIndex α) :
    stageRunRec base code guess α =
      limitStage fun β : ↥(Set.Iio α) ↦ stageRunRec base code guess (β : OmegaOne) := by
  rw [stageRunRec_eq, stepAt,
    dif_neg (fun hp ↦ not_isPredIndex_of_isLimitIndex h _ hp.choose_spec), if_pos h.1]

/-! ## The order between stages -/

/-- One stage sits inside another: the carriers include, the two membership relations agree on the
smaller carrier, and the inclusion is elementary. This is a `Prop`, so it can be carried by
transfinite induction; the elementary map is recovered by choice as `StageLe.map`. -/
def StageLe (S T : StageModel Ω) : Prop :=
  ∃ h : S.carrier ⊆ T.carrier,
    (∀ x y : ↥S.carrier, x ∈ y ↔ StageModel.incl h x ∈ StageModel.incl h y) ∧
    ∃ j : ElementaryMap ↥S.carrier ↥T.carrier, ∀ x, j x = StageModel.incl h x

namespace StageLe

variable {S T U : StageModel Ω}

theorem subset (h : StageLe S T) : S.carrier ⊆ T.carrier := h.choose

theorem mem_iff (h : StageLe S T) (x y : ↥S.carrier) :
    x ∈ y ↔ StageModel.incl h.subset x ∈ StageModel.incl h.subset y := h.choose_spec.1 x y

/-- The elementary inclusion of one stage into a larger one, read off `StageLe` by choice. -/
noncomputable def map (h : StageLe S T) : ElementaryMap ↥S.carrier ↥T.carrier :=
  h.choose_spec.2.choose

theorem map_apply (h : StageLe S T) (x : ↥S.carrier) :
    h.map x = StageModel.incl h.subset x := h.choose_spec.2.choose_spec x

theorem refl (S : StageModel Ω) : StageLe S S :=
  ⟨subset_rfl, fun _ _ ↦ Iff.rfl, ElementaryMap.identity _, fun _ ↦ rfl⟩

theorem trans (h₁ : StageLe S T) (h₂ : StageLe T U) : StageLe S U :=
  ⟨h₁.subset.trans h₂.subset, fun x y ↦ (h₁.mem_iff x y).trans (h₂.mem_iff _ _),
    h₂.map.comp h₁.map, fun x ↦ by
      show h₂.map (h₁.map x) = _
      rw [h₁.map_apply, h₂.map_apply]
      rfl⟩

end StageLe

/-- A stage models ZF. The nonemptiness the notation needs is taken as an instance argument, so
that this is a predicate on the stage alone and can be carried by the induction. -/
def StageZF (S : StageModel Ω) : Prop :=
  ∀ [Nonempty ↥S.carrier], (↥S.carrier)↓[ℒₛₑₜ] ⊧* 𝗭𝗙

/-- An elementary map carries `ZF` from its source to its target. -/
theorem models_zf_of_map {A B : Type*} [SetStructure A] [SetStructure B] [Nonempty A]
    [Nonempty B] [A↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (j : ElementaryMap A B) : B↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  refine ⟨?_⟩
  intro φ hφ
  have hs := Theory.models A 𝗭𝗙 hφ
  change φ.Eval ![] Empty.elim at hs
  have he := (j.elementary φ ![] Empty.elim).mp hs
  have hf : (j.toFun ∘ (Empty.elim : Empty → A)) = Empty.elim := funext fun x ↦ Empty.elim x
  have hb : (j.toFun ∘ (![] : Fin 0 → A)) = ![] := funext fun l ↦ Fin.elim0 l
  rw [hf, hb] at he
  exact he

/-- The pair a guess cuts out of a stage is inseparable there as soon as the guess itself is
inseparable from its complement: the two descriptions agree on the points of the stage. -/
theorem inseparable_self {S : StageModel Ω} {G : Set Ω}
    (h : Inseparable ↥S.carrier (fun x ↦ (x : Ω) ∈ G) (fun x ↦ (x : Ω) ∉ G)) :
    Inseparable ↥S.carrier (fun x ↦ (x : Ω) ∈ S.carrier ∩ G)
      (fun x ↦ (x : Ω) ∈ S.carrier \ G) :=
  h.congr (fun x ↦ ⟨fun hx ↦ hx.2, fun hx ↦ ⟨x.2, hx⟩⟩)
    (fun x ↦ ⟨fun hx ↦ hx.2, fun hx ↦ ⟨x.2, hx⟩⟩)

/-! ## The invariants of the recursion -/

section Invariants

variable (base : StageModel Ω) (code : OmegaOne ≃ Ω) (guess : OmegaOne → Set Ω)

/-- The family of stages below `α`, as a `StageFamily` indexed by `↥(Set.Iio α)`. The hypothesis
is the part of the induction hypothesis saying that the stages below `α` increase elementarily. -/
noncomputable def belowFamily (α : OmegaOne)
    (h : ∀ i k : ↥(Set.Iio α), i ≤ k →
      StageLe (stageRunRec base code guess (i : OmegaOne)) (stageRunRec base code guess (k : OmegaOne))) :
    StageFamily Ω ↥(Set.Iio α) where
  stage := fun β ↦ stageRunRec base code guess (β : OmegaOne)
  inc := fun i k hik ↦ (h i k hik).subset
  agree := fun i k hik x y _ _ ↦ (h i k hik).mem_iff x y
  step := fun {i k} hik ↦ (h i k hik).map
  step_apply := fun {_ _} hik x ↦ (h _ _ hik).map_apply x

theorem belowFamily_stage (α : OmegaOne) (h) (i : ↥(Set.Iio α)) :
    (belowFamily base code guess α h).stage i = stageRunRec base code guess (i : OmegaOne) := rfl

/-- What the induction proves at every index: the stage is countable, nonempty and models ZF; the
earlier stages sit inside it elementarily; and a pair guessed at an earlier index and inseparable
there is inseparable in it. -/
def StageInv (α : OmegaOne) : Prop :=
  ((stageRunRec base code guess α).carrier).Countable ∧
  Nonempty ↥(stageRunRec base code guess α).carrier ∧
  StageZF (stageRunRec base code guess α) ∧
  (∀ β, β ≤ α → StageLe (stageRunRec base code guess β) (stageRunRec base code guess α)) ∧
  (∀ β, β ≤ α →
    Inseparable ↥(stageRunRec base code guess β).carrier
      (fun x ↦ (x : Ω) ∈ guess β) (fun x ↦ (x : Ω) ∉ guess β) →
    Inseparable ↥(stageRunRec base code guess α).carrier
      (fun x ↦ (x : Ω) ∈ (stageRunRec base code guess β).carrier ∩ guess β)
      (fun x ↦ (x : Ω) ∈ (stageRunRec base code guess β).carrier \ guess β))

/-- At an index with an immediate predecessor, the stage is the one the successor step promises,
as soon as the invariants hold below. -/
theorem succSpec_of_inv (hΩ : Cardinal.mk Ω = Cardinal.aleph 1) {p α : OmegaOne}
    (hpa : IsPredIndex p α) (hbelow : ∀ β, β < α → StageInv base code guess β) :
    SuccSpec (stageRunRec base code guess p) (stageRunRec base code guess α)
      (obligSetOn (fun β : ↥(Set.Iio α) ↦ stageRunRec base code guess (β : OmegaOne)) guess)
      (code p) := by
  obtain ⟨hc, hne, hzf, hle, -⟩ := hbelow p hpa.1
  haveI := hne
  haveI : (↥(stageRunRec base code guess p).carrier)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := hzf
  have hOsub : ∀ q ∈ obligSetOn
      (fun β : ↥(Set.Iio α) ↦ stageRunRec base code guess (β : OmegaOne)) guess,
      q.1 ⊆ (stageRunRec base code guess p).carrier ∧
        q.2 ⊆ (stageRunRec base code guess p).carrier := by
    rintro q ⟨β, rfl⟩
    have hs := (hle (β : OmegaOne) (hpa.2 (β : OmegaOne) β.2)).subset
    exact ⟨fun x hx ↦ hs hx.1, fun x hx ↦ hs hx.1⟩
  rw [stageRunRec_succ base code guess hpa]
  exact succSpec_succStage hΩ _ hc _ (obligSetOn_countable _ _) hOsub _

/-- The invariants hold at every index. -/
theorem stageRunRec_inv (hΩ : Cardinal.mk Ω = Cardinal.aleph 1) (hbc : base.carrier.Countable)
    (hbne : Nonempty ↥base.carrier) (hbzf : StageZF base) (α : OmegaOne) :
    StageInv base code guess α := by
  induction α using WellFoundedLT.induction with
  | ind α ih =>
  by_cases hlt : ∃ β : OmegaOne, β < α
  · by_cases hp : ∃ p, IsPredIndex p α
    · -- successor index
      obtain ⟨p, hpa⟩ := hp
      obtain ⟨hsub, hTc, -, hmem, ⟨jmap, hjmap⟩, hins, -⟩ :=
        succSpec_of_inv base code guess hΩ hpa (fun β hβ ↦ ih β hβ)
      obtain ⟨-, hnep, hzfp, hlep, hkeepp⟩ := ih p hpa.1
      have hstep : StageLe (stageRunRec base code guess p) (stageRunRec base code guess α) :=
        ⟨hsub, hmem, jmap, hjmap⟩
      have hneα : Nonempty ↥(stageRunRec base code guess α).carrier :=
        hnep.map (StageModel.incl hsub)
      refine ⟨hTc, hneα, ?_, ?_, ?_⟩
      · haveI := hnep
        haveI : (↥(stageRunRec base code guess p).carrier)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := hzfp
        intro _
        exact models_zf_of_map jmap
      · intro β hβ
        rcases lt_or_eq_of_le hβ with h | h
        · exact (hlep β (hpa.2 β h)).trans hstep
        · subst h
          exact StageLe.refl _
      · intro β hβ hinsβ
        rcases lt_or_eq_of_le hβ with h | h
        · exact hins _ (mem_obligSetOn
            (fun β : ↥(Set.Iio α) ↦ stageRunRec base code guess (β : OmegaOne)) guess ⟨β, h⟩)
            (hkeepp β (hpa.2 β h) hinsβ)
        · subst h
          exact inseparable_self hinsβ
    · -- limit index
      have hlim : IsLimitIndex α := by
        refine ⟨hlt, fun β hβ ↦ ?_⟩
        by_contra hcon
        push_neg at hcon
        exact hp ⟨β, hβ, fun γ hγ ↦ not_lt.mp fun hlt' ↦ absurd hγ (not_lt.mpr (hcon γ hlt'))⟩
      obtain ⟨β₀, hβ₀⟩ := hlt
      haveI : Nonempty ↥(Set.Iio α) := ⟨⟨β₀, hβ₀⟩⟩
      haveI : Countable ↥(Set.Iio α) := (countable_Iio_omegaOne α).to_subtype
      have hfle : ∀ i k : ↥(Set.Iio α), i ≤ k →
          StageLe (stageRunRec base code guess (i : OmegaOne))
            (stageRunRec base code guess (k : OmegaOne)) :=
        fun i k hik ↦ (ih (k : OmegaOne) k.2).2.2.2.1 (i : OmegaOne) hik
      have heq : stageRunRec base code guess α =
          limitStage (belowFamily base code guess α hfle).stage :=
        stageRunRec_limit base code guess hlim
      have hne0 : Nonempty ↥(limitStage (belowFamily base code guess α hfle).stage).carrier :=
        limitStage_nonempty _ ⟨β₀, hβ₀⟩ (ih β₀ hβ₀).2.1
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [heq]
        exact limitStage_carrier_countable _ (fun i ↦ (ih (i : OmegaOne) i.2).1)
      · rw [heq]; exact hne0
      · rw [heq]
        intro _
        haveI hnb : Nonempty ↥(stageRunRec base code guess β₀).carrier := (ih β₀ hβ₀).2.1
        haveI : Nonempty ↥((belowFamily base code guess α hfle).stage ⟨β₀, hβ₀⟩).carrier := hnb
        exact (belowFamily base code guess α hfle).models_zf ⟨β₀, hβ₀⟩ (ih β₀ hβ₀).2.2.1
      · intro β hβ
        rcases lt_or_eq_of_le hβ with h | h
        · rw [heq]
          refine ⟨subset_limitStage (belowFamily base code guess α hfle).stage ⟨β, h⟩, ?_,
            (belowFamily base code guess α hfle).embedding ⟨β, h⟩, fun x ↦ rfl⟩
          exact limitStage_mem_iff (belowFamily base code guess α hfle).inc
            (belowFamily base code guess α hfle).agree ⟨β, h⟩
        · subst h
          exact StageLe.refl _
      · intro β hβ hinsβ
        rcases lt_or_eq_of_le hβ with h | h
        · rw [heq]
          refine StageFamily.inseparable_limit (belowFamily base code guess α hfle)
            ((stageRunRec base code guess β).carrier ∩ guess β)
            ((stageRunRec base code guess β).carrier \ guess β) ⟨β, h⟩
            (fun x hx ↦ hx.1) (fun x hx ↦ hx.1) ?_
          intro i hi
          exact (ih (i : OmegaOne) i.2).2.2.2.2 β hi hinsβ
        · subst h
          exact inseparable_self hinsβ
  · -- least index
    have heq := stageRunRec_base base code guess hlt
    have hself : ∀ β : OmegaOne, β ≤ α → β = α := by
      intro β hβ
      rcases lt_or_eq_of_le hβ with h | h
      · exact absurd ⟨β, h⟩ hlt
      · exact h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [heq]; exact hbc
    · rw [heq]; exact hbne
    · rw [heq]; exact hbzf
    · intro β hβ
      obtain rfl := hself β hβ
      exact StageLe.refl _
    · intro β hβ hinsβ
      obtain rfl := hself β hβ
      exact inseparable_self hinsβ

end Invariants

/-! ## The run -/

/-- Everything `ZFVP.StageRun` asks for, over a base stage the starting model is placed on. -/
theorem exists_stageRun_of_base_with_stages {M : Type u} [SetStructure M] (base : StageModel Ω)
    (code : OmegaOne ≃ Ω) (guess : OmegaOne → Set Ω)
    (hΩ : Cardinal.mk Ω = Cardinal.aleph 1) (hbc : base.carrier.Countable)
    (hbne : Nonempty ↥base.carrier) (hbzf : StageZF base)
    (bmap : ElementaryMap M ↥base.carrier) :
    ∃ (inst : SetStructure Ω) (R : @StageRun M _ Ω inst), R.code = code ∧ R.guess = guess ∧ R.stage = stageRunRec base code guess := by
  have hinv := stageRunRec_inv base code guess hΩ hbc hbne hbzf
  -- the stages cover the carrier: `code p` is put into the stage at the index just above `p`
  have hcover : StagesCover (stageRunRec base code guess) := by
    intro x
    refine ⟨succIndex (code.symm x), ?_⟩
    obtain ⟨-, -, hx₀, -⟩ := succSpec_of_inv base code guess hΩ
      (isPredIndex_succIndex (code.symm x)) (fun β _ ↦ hinv β)
    rwa [Equiv.apply_symm_apply] at hx₀
  -- continuity at limit indices
  have hlimc : ∀ α : OmegaOne, IsLimitIndex α →
      (stageRunRec base code guess α).carrier =
        {x : Ω | ∃ β, β < α ∧ x ∈ (stageRunRec base code guess β).carrier} := by
    intro α hα
    rw [stageRunRec_limit base code guess hα]
    ext x
    simp only [limitStage_carrier, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨β, hβ⟩, hx⟩
      exact ⟨β, hβ, hx⟩
    · rintro ⟨β, hβ, hx⟩
      exact ⟨⟨β, hβ⟩, hx⟩
  -- the starting model sits in the stage at the least index
  have hbase : stageRunRec base code guess leastIndex = base :=
    stageRunRec_base base code guess not_exists_lt_leastIndex
  have hbmap : ElementaryMap M ↥(stageRunRec base code guess leastIndex).carrier := by
    rw [hbase]; exact bmap
  -- the successor step, at the index just above `γ`
  have hsucc : ∀ (γ : OmegaOne) (dφ : SetTheorySemiformula ↥(stageRunRec base code guess γ).carrier 1)
      (rφ : SetTheorySemiformula ↥(stageRunRec base code guess γ).carrier 2),
      DirectedNoLast (fun x ↦ dφ.Eval ![x] id) (fun x y ↦ rφ.Eval ![x, y] id) →
      ∃ (β : OmegaOne) (hβ : γ < β) (t : ↥(stageRunRec base code guess β).carrier),
        (∀ γ' : OmegaOne, γ < γ' → (t : Ω) ∈ (stageRunRec base code guess γ').carrier) ∧
        dφ.Eval ![t] (fun m ↦ ((hinv β).2.2.2.1 γ hβ.le).map m) ∧
        ∀ m : ↥(stageRunRec base code guess γ).carrier, dφ.Eval ![m] id →
          rφ.Eval ![((hinv β).2.2.2.1 γ hβ.le).map m, t]
            (fun m ↦ ((hinv β).2.2.2.1 γ hβ.le).map m) := by
    intro γ dφ rφ hdir
    have hpa := isPredIndex_succIndex γ
    obtain ⟨hsub, -, -, -, -, -, hbnd⟩ :=
      succSpec_of_inv base code guess hΩ hpa (fun β _ ↦ hinv β)
    obtain ⟨t, ht, htb⟩ := hbnd dφ rφ hdir
    have hfe : (fun m : ↥(stageRunRec base code guess γ).carrier ↦
        ((hinv (succIndex γ)).2.2.2.1 γ hpa.1.le).map m) =
          fun m ↦ StageModel.incl hsub m := funext fun m ↦ StageLe.map_apply _ m
    refine ⟨succIndex γ, hpa.1, t, ?_, ?_, ?_⟩
    · intro γ' hγγ'
      have hle : succIndex γ ≤ γ' := by
        by_contra hc
        exact absurd (hpa.2 γ' (not_le.mp hc)) (not_le.mpr hγγ')
      exact ((hinv γ').2.2.2.1 (succIndex γ) hle).subset t.2
    · rw [hfe]; exact ht
    · intro m hm
      have h1 : ((hinv (succIndex γ)).2.2.2.1 γ hpa.1.le).map m = StageModel.incl hsub m :=
        StageLe.map_apply _ m
      rw [h1, hfe]
      exact htb m hm
  letI inst : SetStructure Ω := unionSetStructure (stageRunRec base code guess)
  exact ⟨inst,
    { stage := stageRunRec base code guess
      code := code
      guess := guess
      countable := fun α ↦ (hinv α).1
      stage_nonempty := fun α ↦ (hinv α).2.1
      inc := fun α β h ↦ ((hinv β).2.2.2.1 α h).subset
      agree := fun α β h x y _ _ ↦ ((hinv β).2.2.2.1 α h).mem_iff x y
      cover := hcover
      union := fun _ _ ↦ Iff.rfl
      elem := fun {α β} h ↦ ((hinv β).2.2.2.1 α h).map
      elem_apply := fun h x ↦ StageLe.map_apply _ x
      limit_carrier := hlimc
      baseIndex := leastIndex
      baseMap := hbmap
      succ_bound := hsucc
      keep := fun α β h hins ↦ (hinv β).2.2.2.2 α h hins }, rfl, rfl, rfl⟩

/-- The stage run with its original interface. -/
theorem exists_stageRun_of_base {M : Type u} [SetStructure M] (base : StageModel Ω)
    (code : OmegaOne ≃ Ω) (guess : OmegaOne → Set Ω)
    (hΩ : Cardinal.mk Ω = Cardinal.aleph 1) (hbc : base.carrier.Countable)
    (hbne : Nonempty ↥base.carrier) (hbzf : StageZF base)
    (bmap : ElementaryMap M ↥base.carrier) :
    ∃ (inst : SetStructure Ω) (R : @StageRun M _ Ω inst), R.code = code ∧ R.guess = guess := by
  obtain ⟨inst, R, hc, hg, _⟩ :=
    exists_stageRun_of_base_with_stages base code guess hΩ hbc hbne hbzf bmap
  exact ⟨inst, R, hc, hg⟩

end Construction

/-- Stage 1 of the Appendix of Enayat's paper: over a countable model `M` of ZF and a carrier `Ω`
of size `ℵ₁`, with a bijection `code` of `ω₁` with `Ω` and a guess at every index, the ω₁-length
recursion produces a `ZFVP.StageRun` with that bookkeeping. -/
theorem exists_stageRun {M : Type u} [SetStructure M] [Nonempty M] [Countable M]
    [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {Ω : Type u} (hΩ : Cardinal.mk Ω = Cardinal.aleph 1) (code : OmegaOne ≃ Ω)
    (guess : OmegaOne → Set Ω) :
    ∃ (inst : SetStructure Ω) (R : @StageRun M _ Ω inst), R.code = code ∧ R.guess = guess := by
  obtain ⟨B, e, hBc⟩ := exists_carrier_embedding (Ω := Ω) hΩ M
  have hbne : Nonempty ↥(StageModel.ofEquiv B e).carrier :=
    Nonempty.map (e.symm : M → ↥B) inferInstance
  refine exists_stageRun_of_base (StageModel.ofEquiv B e) code guess hΩ hBc hbne ?_
    (StageModel.ofEquivSymmMap B e)
  intro _
  exact models_zf_of_map (StageModel.ofEquivSymmMap B e)

end ZFVP

