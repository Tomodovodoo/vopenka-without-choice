import ZFVP.ModelTheory.NoConservativeEndExtension
import ZFVP.ModelTheory.FaithfulStageCaseOne
import ZFVP.SetTheory.AmenableWitnessClosure

/-! Case II for a faithful end extension, using full amenability of a single predicate. -/
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V W : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace MembershipEndExtension
theorem relative_nameStep (X : V → Prop) {T L : V → Prop}
    (hT : PredicateExpansion.Pred X T) (hL : PredicateExpansion.Pred X L) :
    PredicateExpansion.Rel X (fun p q ↦ T q ∧ L ⟨q, p⟩ₖ) := by
  let : Structure predicateLanguage V := predicateExpansion X
  change Language.DefinableRel predicateLanguage (fun p q ↦ T q ∧ L ⟨q, p⟩ₖ)
  apply Language.Definable.and
  · exact Language.Definable.retraction hT ![1]
  · apply Language.DefinablePred.comp (hP := hL)
    refine @PredicateExpansion.base _ _ X _ _ ?_
    definability
theorem false_of_stage_without_least_of_amenable_names {j : MembershipEndExtension V W} (hp : j.IsPowersetPreserving)
    {δ θ : W} [IsOrdinal δ] [IsOrdinal θ] (hδθ : δ ∈ θ) (hnew : ∀ α : V, j α ≠ δ)
    (X : V → Prop) (hX : IsAmenablePredicate X)
    (T₀ E L : V → Prop)
    (hT₀d : PredicateExpansion.Pred X T₀)
    (hEd : PredicateExpansion.Pred X E)
    (hLd : PredicateExpansion.Pred X L)
    (hT₀s : ∀ p : V, T₀ p ↔ StageNamesOrdinal δ θ (j p))
    (hEs : ∀ p : V, E p ↔ StageNameValue δ θ (j p))
    (hLs : ∀ p : V, L p ↔ StageNameLt δ θ (j p))
    (hno : ∀ δ₀ : W, ¬ IsLeastStageDefinableParamNew j δ θ δ₀) : False := by
  -- the image of the smaller model lies in the stage
  have hmemδ : ∀ m : V, j m ∈ hierarchy δ := fun m ↦ hp.map_mem_hierarchy_of_new hnew m
  have hδsubθ : δ ⊆ θ := IsOrdinal.toIsTransitive.transitive δ hδθ
  have hmemθ : ∀ m : V, j m ∈ hierarchy θ := fun m ↦ hierarchy_mono hδsubθ _ (hmemδ m)
  have hδmem : δ ∈ hierarchy θ := ordinal_mem_hierarchy_iff.mpr hδθ
  let : Structure predicateLanguage V := predicateExpansion X
  have : Language.DefinablePred predicateLanguage T₀ := hT₀d
  have : Language.DefinablePred predicateLanguage E := hEd
  have : Language.DefinablePred predicateLanguage L := hLd
  let T (p : V) := p = ⟨kpair.π₁ p, kpair.π₂ p⟩ₖ ∧ T₀ p ∧ ∀ α : V, ¬ E ⟨p, α⟩ₖ
  have hTd : PredicateExpansion.Pred X T := by
    change Language.DefinablePred predicateLanguage T
    unfold T
    relative_definability X
  have hTs (p : V) : T p ↔ (p = ⟨kpair.π₁ p, kpair.π₂ p⟩ₖ ∧ T₀ p ∧ ∀ α : V, ¬ E ⟨p, α⟩ₖ) := Iff.rfl
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
  have hstep := relative_nameStep X hTd hLd
  obtain ⟨η, hη, hrank, hclosed⟩ :=
    hX.witnessClosedAbove (fun p q ↦ T q ∧ L ⟨q, p⟩ₖ) hstep (rank p₀)
  have : IsOrdinal η := hη
  have hp₀η : p₀ ∈ hierarchy η := (mem_hierarchy_iff_rank_mem _ _).mpr hrank
  obtain ⟨w, hw⟩ := hX.separation T hTd (hierarchy η)
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


def stageNamePredicate (δ θ u : W) : Prop :=
  (kpair.π₁ u = 0 ∧ StageNamesOrdinal δ θ (kpair.π₂ u)) ∨
  (kpair.π₁ u = 1 ∧ StageNameValue δ θ (kpair.π₂ u)) ∨
  (kpair.π₁ u = 2 ∧ StageNameLt δ θ (kpair.π₂ u))

instance stageNamePredicate_definable : ℒₛₑₜ-relation₃[W] stageNamePredicate := by
  unfold stageNamePredicate
  definability

theorem relative_tag (X : V → Prop) (k : V) :
    PredicateExpansion.Pred X (fun p ↦ X ⟨k, p⟩ₖ) := by
  let : Structure predicateLanguage V := predicateExpansion X
  change Language.DefinablePred predicateLanguage (fun p ↦ X ⟨k, p⟩ₖ)
  apply Language.DefinablePred.comp (hP := PredicateExpansion.predicate X)
  refine @PredicateExpansion.base _ _ X _ _ ?_
  definability

theorem false_of_faithful_stage_without_least {j : MembershipEndExtension V W}
    (hf : j.IsFaithful) {δ θ : W} [IsOrdinal δ] [IsOrdinal θ]
    (hδθ : δ ∈ θ) (hnew : ∀ α : V, j α ≠ δ)
    (hno : ∀ δ₀ : W, ¬ IsLeastStageDefinableParamNew j δ θ δ₀) : False := by
  let X (p : V) := stageNamePredicate δ θ (j p)
  have hX : IsAmenablePredicate X := hf (stageNamePredicate δ θ) (by definability)
  apply false_of_stage_without_least_of_amenable_names hf.isPowersetPreserving hδθ hnew X hX
    (fun p ↦ X ⟨0, p⟩ₖ) (fun p ↦ X ⟨1, p⟩ₖ) (fun p ↦ X ⟨2, p⟩ₖ)
    (relative_tag X 0) (relative_tag X 1) (relative_tag X 2) ?_ ?_ ?_ hno
  all_goals
    intro p
    simp only [X, stageNamePredicate, j.map_kpair, kpair.π₁_kpair, kpair.π₂_kpair]
    simp only [show j (0 : V) = (0 : W) from j.map_numeral 0,
      show j (1 : V) = (1 : W) from j.map_numeral 1,
      show j (2 : V) = (2 : W) from j.map_numeral 2]
    simp only [show ((0 : W) = 1 ↔ False) by exact (natCast_eq_iff 0 1).trans (by decide),
      show ((0 : W) = 2 ↔ False) by exact (natCast_eq_iff 0 2).trans (by decide),
      show ((1 : W) = 0 ↔ False) by exact (natCast_eq_iff 1 0).trans (by decide),
      show ((1 : W) = 2 ↔ False) by exact (natCast_eq_iff 1 2).trans (by decide),
      show ((2 : W) = 0 ↔ False) by exact (natCast_eq_iff 2 0).trans (by decide),
      show ((2 : W) = 1 ↔ False) by exact (natCast_eq_iff 2 1).trans (by decide),
      true_and, false_and, false_or, or_false, eq_self]
end MembershipEndExtension
end ZFVP
