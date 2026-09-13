import ZFVP.ModelTheory.ElementaryStageCaseOne
import ZFVP.ModelTheory.WeaklyRubinDeadEnd
import ZFVP.SetTheory.WitnessClosure

/-! Case II of Enayat's Theorem 4.4 in "Models of set theory: extensions and dead ends", and
with it his Theorem 5.1: no model of ZF has a conservative proper end extension satisfying ZF.

Let `j : V → W` be a conservative proper end extension of models of ZF, `δ` a new ordinal of `W`
and `θ` the stage produced by `exists_reflectsCaseOne`, so that Enayat's class `O'` of the new
ordinals `ξ ≤ δ` definable in `(V_θ, ∈)` from `δ` and one old parameter has no least element
(`exists_stage_without_least`). Enayat rules that out by naming those ordinals inside the smaller
model, reflecting, and contradicting foundation in the larger one. This file carries that out.

A *name* is a pair `⟨m, φ⟩ₖ` of the smaller model: `m` a parameter, `φ` a three-variable formula
code. It names the element of `V_θ` that `j φ` defines there from `δ` and `j m`. Two facts make
the argument work.

* Every three-variable formula code of `W` is old. The set of codes of arity `3` is the image of
  the corresponding set of `V`, because the arity `3` is old and `j` transports `formulaSet`; and
  an end extension has no new members of an old set. So the names capture the whole of `O'`, not
  just its old-code part.
* Conservativity turns "the name `p` names an ordinal `≤ δ`", "the name `p` names `j α`" and "the
  ordinal named by `p` is below the one named by `q`" into predicates definable in the smaller
  model, since each is the pullback along `j` of a predicate definable in the larger one from the
  parameters `δ` and `θ`.

Writing `T` for the names of new ordinals `≤ δ`, Case II says that `T` is not empty and that every
name in `T` has a name in `T` below it. Witness closure inside `V` then bounds the choice of the
smaller name: there is a stage `V_η` such that `w = {p ∈ V_η ; T p}` is not empty and every name
in `w` has a name in `w` below it. Then `j w` is a set of `W`, so the ordinals it names form a set
of `W` by Separation, and that set is a nonempty set of ordinals with no least element. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Names and the three relations they carry -/

/-- The pair `u = ⟨m, φ⟩ₖ` names an ordinal `≤ δ` over the stage `V_θ`: `φ` is a three-variable
formula code and it defines an ordinal `≤ δ` in `(V_θ, ∈)` from the parameters `δ` and `m`. -/
def StageNamesOrdinal (δ θ u : V) : Prop :=
  IsMembershipFormulaCode ((3 : ℕ) : V) (kpair.π₂ u) ∧
    ∃ x : V, DefinesInStage θ δ (kpair.π₁ u) (kpair.π₂ u) x ∧ IsOrdinal x ∧ x ∈ succ δ

/-- For `w = ⟨u, x⟩ₖ`: the name `u` names `x` over the stage `V_θ`. -/
def StageNameValue (δ θ w : V) : Prop :=
  DefinesInStage θ δ (kpair.π₁ (kpair.π₁ w)) (kpair.π₂ (kpair.π₁ w)) (kpair.π₂ w)

/-- For `w = ⟨u, u'⟩ₖ`: the element named by `u` is a member of the one named by `u'`. -/
def StageNameLt (δ θ w : V) : Prop :=
  ∃ x y : V, DefinesInStage θ δ (kpair.π₁ (kpair.π₁ w)) (kpair.π₂ (kpair.π₁ w)) x ∧
    DefinesInStage θ δ (kpair.π₁ (kpair.π₂ w)) (kpair.π₂ (kpair.π₂ w)) y ∧ x ∈ y

instance stageNamesOrdinal_definable : ℒₛₑₜ-relation₃[V] StageNamesOrdinal := by
  unfold StageNamesOrdinal
  definability

instance stageNameValue_definable : ℒₛₑₜ-relation₃[V] StageNameValue := by
  unfold StageNameValue
  definability

instance stageNameLt_definable : ℒₛₑₜ-relation₃[V] StageNameLt := by
  unfold StageNameLt
  definability

theorem stageNamesOrdinal_kpair (δ θ m φ : V) :
    StageNamesOrdinal δ θ ⟨m, φ⟩ₖ ↔ IsMembershipFormulaCode ((3 : ℕ) : V) φ ∧
      ∃ x : V, DefinesInStage θ δ m φ x ∧ IsOrdinal x ∧ x ∈ succ δ := by
  simp only [StageNamesOrdinal, kpair.π₁_kpair, kpair.π₂_kpair]

theorem stageNameValue_kpair (δ θ m φ x : V) :
    StageNameValue δ θ ⟨⟨m, φ⟩ₖ, x⟩ₖ ↔ DefinesInStage θ δ m φ x := by
  simp only [StageNameValue, kpair.π₁_kpair, kpair.π₂_kpair]

theorem stageNameLt_kpair (δ θ m φ m' φ' : V) :
    StageNameLt δ θ ⟨⟨m, φ⟩ₖ, ⟨m', φ'⟩ₖ⟩ₖ ↔
      ∃ x y : V, DefinesInStage θ δ m φ x ∧ DefinesInStage θ δ m' φ' y ∧ x ∈ y := by
  simp only [StageNameLt, kpair.π₁_kpair, kpair.π₂_kpair]

/-- The names of elements that are not in the image of the smaller model, as a definable
predicate. `T₀` is "names an ordinal `≤ δ`" and `E` is "the name in the first component names the
second component", both pulled back along the extension. -/
theorem definable_newName {T₀ E : V → Prop} (h₀ : ℒₛₑₜ-predicate[V] T₀)
    (h₁ : ℒₛₑₜ-predicate[V] E) :
    ℒₛₑₜ-predicate[V]
      (fun p ↦ p = ⟨kpair.π₁ p, kpair.π₂ p⟩ₖ ∧ T₀ p ∧ ∀ α : V, ¬ E ⟨p, α⟩ₖ) := by
  have := h₀
  have := h₁
  definability

/-- The step relation of the witness-closure argument: `q` is a name in `T` whose value is below
the value of `p`. -/
theorem definable_nameStep {T L : V → Prop} (h₀ : ℒₛₑₜ-predicate[V] T)
    (h₁ : ℒₛₑₜ-predicate[V] L) : ℒₛₑₜ-relation[V] (fun p q ↦ T q ∧ L ⟨q, p⟩ₖ) := by
  have := h₀
  have := h₁
  definability

/-- Membership in a fixed set is a definable predicate. -/
theorem definable_mem_set (A : V) : ℒₛₑₜ-predicate[V] (fun z ↦ z ∈ A) := by definability

/-- The elements of the stage `V_θ` named by a member of a fixed set of names. -/
theorem definable_namedBy (δ θ c : V) :
    ℒₛₑₜ-predicate[V] (fun x ↦ IsOrdinal x ∧
      ∃ u : V, u ∈ c ∧ DefinesInStage θ δ (kpair.π₁ u) (kpair.π₂ u) x) := by
  definability

namespace MembershipEndExtension

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-! ### Every formula code of an old arity is old -/

/-- The formula codes of an old arity are exactly the images of the old ones: `formulaSet` is
transported by `j`, and an end extension adds no members to an old set. -/
theorem exists_old_formula_code (j : MembershipEndExtension V W) (n : ℕ) {φ : W}
    (h : IsMembershipFormulaCode ((n : ℕ) : W) φ) : ∃ c : V, j c = φ := by
  have hmem : φ ∈ formulaSet (membershipLanguageCode : W) ∅ (j ((n : ℕ) : V)) := by
    rw [j.map_numeral n]
    exact (mem_formulaSet_iff _ _ _ _).mpr h
  rw [← j.map_membershipLanguageCode', ← j.map_empty,
    ← j.map_formulaSet membershipLanguageCode_valid ∅ ((n : ℕ) : V)] at hmem
  obtain ⟨c, -, hc⟩ := j.endExtension _ φ hmem
  exact ⟨c, hc.symm⟩

/-! ### Case II -/

/-- Case II of Enayat's Theorem 4.4 for a conservative end extension: Enayat's class `O'` cannot
be nonempty without a least element. The hypotheses are that `δ` is a new ordinal below `θ` and
that no ordinal is least in `O'`. -/
theorem false_of_stage_without_least {j : MembershipEndExtension V W} (hc : j.IsConservative)
    {δ θ : W} [IsOrdinal δ] [IsOrdinal θ] (hδθ : δ ∈ θ) (hnew : ∀ α : V, j α ≠ δ)
    (hno : ∀ δ₀ : W, ¬ IsLeastStageDefinableParamNew j δ θ δ₀) : False := by
  -- the image of the smaller model lies in the stage
  have hmemδ : ∀ m : V, j m ∈ hierarchy δ := fun m ↦ map_mem_hierarchy_of_new hc hnew m
  have hδsubθ : δ ⊆ θ := IsOrdinal.toIsTransitive.transitive δ hδθ
  have hmemθ : ∀ m : V, j m ∈ hierarchy θ := fun m ↦ hierarchy_mono hδsubθ _ (hmemδ m)
  have hδmem : δ ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr hδθ
  -- the three pullbacks, definable in the smaller model by conservativity
  obtain ⟨T₀, hT₀d, hT₀s⟩ : ∃ P : V → Prop, (ℒₛₑₜ-predicate[V] P) ∧
      ∀ p : V, P p ↔ StageNamesOrdinal δ θ (j p) :=
    ⟨fun p ↦ StageNamesOrdinal δ θ (j p),
      hc (fun u ↦ StageNamesOrdinal δ θ u) (by definability), fun _ ↦ Iff.rfl⟩
  obtain ⟨E, hEd, hEs⟩ : ∃ P : V → Prop, (ℒₛₑₜ-predicate[V] P) ∧
      ∀ r : V, P r ↔ StageNameValue δ θ (j r) :=
    ⟨fun r ↦ StageNameValue δ θ (j r),
      hc (fun u ↦ StageNameValue δ θ u) (by definability), fun _ ↦ Iff.rfl⟩
  obtain ⟨L, hLd, hLs⟩ : ∃ P : V → Prop, (ℒₛₑₜ-predicate[V] P) ∧
      ∀ r : V, P r ↔ StageNameLt δ θ (j r) :=
    ⟨fun r ↦ StageNameLt δ θ (j r),
      hc (fun u ↦ StageNameLt δ θ u) (by definability), fun _ ↦ Iff.rfl⟩
  -- the names of new ordinals `≤ δ`
  obtain ⟨T, hTd, hTs⟩ : ∃ P : V → Prop, (ℒₛₑₜ-predicate[V] P) ∧
      ∀ p : V, P p ↔ (p = ⟨kpair.π₁ p, kpair.π₂ p⟩ₖ ∧ T₀ p ∧ ∀ α : V, ¬ E ⟨p, α⟩ₖ) :=
    ⟨_, definable_newName hT₀d hEd, fun _ ↦ Iff.rfl⟩
  -- reading a name off its two components
  have hnames : ∀ m φ : V, T₀ ⟨m, φ⟩ₖ ↔ (IsMembershipFormulaCode ((3 : ℕ) : W) (j φ) ∧
      ∃ x : W, DefinesInStage θ δ (j m) (j φ) x ∧ IsOrdinal x ∧ x ∈ succ δ) := by
    intro m φ
    rw [hT₀s, j.map_kpair, stageNamesOrdinal_kpair]
  have hvalues : ∀ m φ α : V, E ⟨⟨m, φ⟩ₖ, α⟩ₖ ↔ DefinesInStage θ δ (j m) (j φ) (j α) := by
    intro m φ α
    rw [hEs, j.map_kpair, j.map_kpair, stageNameValue_kpair]
  have hlts : ∀ m φ m' φ' : V, L ⟨⟨m, φ⟩ₖ, ⟨m', φ'⟩ₖ⟩ₖ ↔ ∃ x y : W,
      DefinesInStage θ δ (j m) (j φ) x ∧ DefinesInStage θ δ (j m') (j φ') y ∧ x ∈ y := by
    intro m φ m' φ'
    rw [hLs, j.map_kpair, j.map_kpair, j.map_kpair, stageNameLt_kpair]
  -- a name of `δ` itself: the formula "the first variable equals the second"
  obtain ⟨c₀, hc₀⟩ : ∃ c : V, j c = (encodeMembershipFormula firstEqualsSecond : W) :=
    j.exists_old_formula_code 3 ((mem_formulaSet_iff _ _ _ _).mp (encodeMembershipFormula_mem _))
  have hdef₀ : DefinesInStage θ δ (j (∅ : V)) (j c₀) δ := by
    rw [hc₀]
    exact definesInStage_firstEqualsSecond hδmem (hmemθ ∅)
  have hcode₀ : IsMembershipFormulaCode ((3 : ℕ) : W) (j c₀) := by
    rw [hc₀]
    exact (mem_formulaSet_iff _ _ _ _).mp (encodeMembershipFormula_mem _)
  obtain ⟨p₀, hp₀def⟩ : ∃ p : V, p = ⟨(∅ : V), c₀⟩ₖ := ⟨_, rfl⟩
  have hTp₀ : T p₀ := by
    refine (hTs p₀).mpr ⟨?_, ?_, fun α hα ↦ ?_⟩
    · rw [hp₀def]
      simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    · rw [hp₀def]
      exact (hnames _ _).mpr ⟨hcode₀, δ, hdef₀, inferInstance, mem_succ_self δ⟩
    · rw [hp₀def] at hα
      exact hnew α (hdef₀.unique ((hvalues (∅ : V) c₀ α).mp hα)).symm
  -- every name of a new ordinal has a name of a smaller new ordinal
  have hserial : ∀ p : V, T p → ∃ q : V, T q ∧ L ⟨q, p⟩ₖ := by
    intro p hp
    obtain ⟨hpair, hT₀p, holdp⟩ := (hTs p).mp hp
    rw [hpair] at hT₀p
    obtain ⟨hcode, x, hx, hxord, hxδ⟩ := (hnames _ _).mp hT₀p
    -- the ordinal named by `p` lies in Enayat's `O'`
    have hxnew : ∀ α : V, j α ≠ x := by
      intro α hα
      refine holdp α ?_
      rw [hpair]
      exact (hvalues _ _ α).mpr (hα ▸ hx)
    have hxO : stageDefinableParamNew j δ θ x :=
      ⟨⟨hxδ, kpair.π₁ p, j (kpair.π₂ p), hcode, hx⟩, hxnew⟩
    -- so it is not least in `O'`
    obtain ⟨ξ, hξx, hξO⟩ : ∃ ξ ∈ x, stageDefinableParamNew j δ θ ξ := by
      by_contra hcon
      exact hno x ⟨hxord, hxO, fun ξ hξ hO ↦ hcon ⟨ξ, hξ, hO⟩⟩
    obtain ⟨⟨hξδ, m', ψ, hψcode, hψ⟩, hξnew⟩ := hξO
    -- its code is old, so the smaller ordinal has a name
    obtain ⟨φ', hφ'⟩ := j.exists_old_formula_code 3 hψcode
    rw [← hφ'] at hψ hψcode
    refine ⟨⟨m', φ'⟩ₖ, (hTs _).mpr ⟨?_, ?_, fun α hα ↦ ?_⟩, ?_⟩
    · simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    · exact (hnames m' φ').mpr ⟨hψcode, ξ, hψ, IsOrdinal.of_mem hξx, hξδ⟩
    · exact hξnew α (hψ.unique ((hvalues m' φ' α).mp hα)).symm
    · rw [hpair]
      exact (hlts m' φ' _ _).mpr ⟨ξ, x, hψ, hx, hξx⟩
  -- bound the choice of the smaller name by witness closure inside the smaller model
  obtain ⟨η, hη, hrank, -, hclosed⟩ :=
    witnessClosed_above (V := V) (fun p q ↦ T q ∧ L ⟨q, p⟩ₖ) (definable_nameStep hTd hLd) (rank p₀)
  have : IsOrdinal η := hη
  have hp₀η : p₀ ∈ hierarchy η := (mem_hierarchy_iff_rank_mem _ _).mpr hrank
  obtain ⟨w, hwdef⟩ : ∃ s : V, s = sep (hierarchy η) T hTd := ⟨_, rfl⟩
  have hw : ∀ p : V, p ∈ w ↔ p ∈ hierarchy η ∧ T p := by
    intro p
    rw [hwdef]
    exact mem_sep_iff
  have hp₀w : p₀ ∈ w := (hw p₀).mpr ⟨hp₀η, hTp₀⟩
  have hwserial : ∀ p ∈ w, ∃ q ∈ w, L ⟨q, p⟩ₖ := by
    intro p hp
    obtain ⟨hpη, hTp⟩ := (hw p).mp hp
    obtain ⟨q, hq⟩ := hserial p hTp
    obtain ⟨q', hq'η, hq'⟩ := hclosed p hpη ⟨q, hq⟩
    exact ⟨q', (hw q').mpr ⟨hq'η, hq'.1⟩, hq'.2⟩
  -- the ordinals named by `j w` form a set of the larger model
  obtain ⟨A, hAdef⟩ : ∃ S : W, S = sep (succ δ) (fun x ↦ IsOrdinal x ∧ ∃ u : W, u ∈ j w ∧
      DefinesInStage θ δ (kpair.π₁ u) (kpair.π₂ u) x) (definable_namedBy δ θ (j w)) := ⟨_, rfl⟩
  have hA : ∀ x : W, x ∈ A ↔ x ∈ succ δ ∧ (IsOrdinal x ∧ ∃ u : W, u ∈ j w ∧
      DefinesInStage θ δ (kpair.π₁ u) (kpair.π₂ u) x) := by
    intro x
    rw [hAdef]
    exact mem_sep_iff
  have hδA : δ ∈ A := by
    refine (hA δ).mpr ⟨mem_succ_self δ, inferInstance, j p₀, (j.mem_iff p₀ w).mpr hp₀w, ?_⟩
    rw [hp₀def, j.map_kpair]
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact hdef₀
  -- it is nonempty and has no least element, which foundation forbids
  obtain ⟨ζ, hζ, -⟩ := leastOrdinal_existsUnique (fun z : W ↦ z ∈ A) (definable_mem_set A)
    ⟨δ, inferInstance, hδA⟩
  obtain ⟨hζδ, hζord, u, huw, huζ⟩ := (hA ζ).mp hζ.2.1
  obtain ⟨p, hpw, rfl⟩ := (j.mem_map_iff w u).mp huw
  obtain ⟨hpη, hTp⟩ := (hw p).mp hpw
  obtain ⟨hpair, -, -⟩ := (hTs p).mp hTp
  obtain ⟨q, hqw, hqp⟩ := hwserial p hpw
  obtain ⟨hqpair, -, -⟩ := (hTs q).mp ((hw q).mp hqw).2
  rw [hqpair, hpair] at hqp
  obtain ⟨x, y, hxq, hyp, hxy⟩ := (hlts _ _ _ _).mp hqp
  have hyζ : y = ζ := by
    refine DefinesInStage.unique ?_ huζ
    rw [hpair, j.map_kpair]
    simp only [kpair.π₁_kpair, kpair.π₂_kpair]
    exact hyp
  rw [hyζ] at hxy
  have hxA : x ∈ A := by
    refine (hA x).mpr ⟨?_, IsOrdinal.of_mem hxy, j q, (j.mem_iff q w).mpr hqw, ?_⟩
    · refine mem_succ_iff.mpr (Or.inr ?_)
      rcases mem_succ_iff.mp hζδ with heq | hlt
      · exact heq ▸ hxy
      · exact IsOrdinal.toIsTransitive.mem_trans hxy hlt
    · rw [hqpair, j.map_kpair]
      simp only [kpair.π₁_kpair, kpair.π₂_kpair]
      exact hxq
  exact mem_irrefl x (hζ.2.2 x (IsOrdinal.of_mem hxy) hxA x hxy)

/-- Enayat's Theorem 4.4 for a conservative end extension, in the form his Theorem 5.1 uses:
a conservative end extension of a model of ZF to a model of ZF has no new ordinal. -/
theorem false_of_new_ordinal {j : MembershipEndExtension V W} (hc : j.IsConservative) (δ : W)
    [IsOrdinal δ] (hnew : ∀ α : V, j α ≠ δ) : False := by
  obtain ⟨θ, hθ, hδθ, hno⟩ := exists_stage_without_least hc δ
  have : IsOrdinal θ := hθ
  exact false_of_stage_without_least hc hδθ hnew hno

end MembershipEndExtension

/-- Enayat's Theorem 5.1: no model of ZF has a conservative proper end extension satisfying ZF. -/
theorem no_conservative_proper_end_extension : NoConservativeProperEndExtension.{u} := by
  intro M _ _ _ N _ _ _ j hc hp
  obtain ⟨δ, hδ, hnew⟩ := hc.exists_new_ordinal hp
  have : IsOrdinal δ := hδ
  exact MembershipEndExtension.false_of_new_ordinal hc δ hnew

/-- Enayat's Theorem 5.18, unconditionally: a weakly Rubin model is a ZF dead end. -/
theorem IsWeaklyRubin.isZFDeadEnd' {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (h : IsWeaklyRubin V) : IsZFDeadEnd V :=
  h.isZFDeadEnd no_conservative_proper_end_extension

end ZFVP
