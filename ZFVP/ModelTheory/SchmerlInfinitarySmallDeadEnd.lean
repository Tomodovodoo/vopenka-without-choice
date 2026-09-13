import ZFVP.ModelTheory.SchmerlInfinitaryDeadEndSentence
import ZFVP.ModelTheory.SchmerlInfinitaryDownwardLS
import ZFVP.ModelTheory.SchmerlInfinitaryFiniteSmall

/-! A standard model of the fixed Schmerl sentence has a ZF dead-end
submodel of size exactly `ℵ₁`. A countable conjunction retains any specified
first-order set theory. Membership in the smaller model is the restriction
of membership in the given model. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary (Formula)

universe u

/-- Enumerate all original-language sentences, using truth at unused codes. -/
noncomputable def enumerateSetSentences (n : ℕ) : SetTheorySentence :=
  (Encodable.decode (α := SetTheorySentence) n).getD ⊤

theorem enumerateSetSentences_surjective : Function.Surjective enumerateSetSentences := by
  intro φ
  exact ⟨Encodable.encode φ, by simp [enumerateSetSentences]⟩

/-- A countable conjunction of precisely the requested theory's axioms. -/
noncomputable def originalTheorySentence (T : Theory ℒₛₑₜ) : Formula deadEndLanguage 0 := by
  classical
  exact .conj fun n ↦ if enumerateSetSentences n ∈ T then
    .fo ((enumerateSetSentences n).lMap deadEndSetEmbedding) else .fo ⊤

theorem eval_originalTheorySentence {V : Type u} [SetStructure V] [Nonempty V]
    (S : Structure deadEndLanguage V)
    (hS : S.lMap deadEndSetEmbedding = (inferInstance : Structure ℒₛₑₜ V))
    (T : Theory ℒₛₑₜ) :
    @Formula.Eval deadEndLanguage V S 0 (originalTheorySentence T) ![] ↔ V↓[ℒₛₑₜ] ⊧* T := by
  classical
  have he (φ : SetTheorySentence) :
      @Formula.Eval deadEndLanguage V S 0 (.fo (φ.lMap deadEndSetEmbedding)) ![] ↔
        V↓[ℒₛₑₜ] ⊧ φ := by
    change (φ.lMap deadEndSetEmbedding).Evalb (s := S) ![] ↔ _
    rw [Semiformula.eval_lMap, hS]
    rfl
  rw [originalTheorySentence, Formula.eval_conj, models_theory_iff]
  constructor
  · intro h φ hφ
    obtain ⟨n, rfl⟩ := enumerateSetSentences_surjective φ
    exact (he _).mp (by simpa only [ite_eq_left hφ] using h n)
  · intro h n
    split_ifs with hn
    · exact (he _).mpr (h _ hn)
    · trivial

/-- The fixed dead-end sentence together with all axioms to be preserved. -/
noncomputable def deadEndTheorySentence (T : Theory ℒₛₑₜ) : Formula deadEndLanguage 0 :=
  .and deadEndSentence (originalTheorySentence (𝗭𝗙 ∪ T))

/-- The class-rank `Q` clause forces every standard model to be uncountable. -/
theorem aleph_one_le_of_deadEndSentence {V : Type u}
    (S : Structure deadEndLanguage V)
    (h : @Formula.Eval deadEndLanguage V S 0 deadEndSentence ![]) :
    Cardinal.aleph 1 ≤ Cardinal.mk V := by
  let : Structure deadEndLanguage V := S
  have hc := (Formula.eval_and _ _ _).mp h |>.1
  have he := (eval_mapLanguage deadEndClassEmbedding S classTreeSentence ![]).mp hc
  let : Structure classLanguage V := S.lMap deadEndClassEmbedding
  have htree := (Formula.eval_and _ _ _).mp he |>.2
  have hcof := (Formula.eval_and _ _ _).mp htree |>.1
  have hunc := (eval_cofinalityWitnessClause _ _ _).mp hcof |>.1
  rw [Cardinal.aleph_one_le_iff, ← not_le, Cardinal.mk_le_aleph0_iff]
  intro hcount
  let : Countable V := hcount
  exact hunc (Set.to_countable _)

/-- Membership on a closed subset is inherited from its ambient set model. -/
@[instance_reducible] def closedSubsetSetStructure {V : Type u} [SetStructure V]
    {S : Structure deadEndLanguage V} (A : @Structure.ClosedSubset deadEndLanguage V S) :
    SetStructure A := submodel (A : Set V)

/-- The induced expanded structure has the actual restricted membership
structure as its set-language reduct, including ordinary equality. -/
theorem closedSubset_set_reduct {V : Type u} [SetStructure V]
    (S : Structure deadEndLanguage V)
    (hS : S.lMap deadEndSetEmbedding = (inferInstance : Structure ℒₛₑₜ V))
    (A : @Structure.ClosedSubset deadEndLanguage V S) :
    letI := closedSubsetSetStructure A
    A.toStructure.lMap deadEndSetEmbedding = (inferInstance : Structure ℒₛₑₜ A) := by
  let := closedSubsetSetStructure A
  apply Structure.ext
  · funext n F
    exact Empty.elim F
  · funext n R b
    change @Structure.rel ℒₛₑₜ V (S.lMap deadEndSetEmbedding) n R (fun i ↦ (b i : V)) = _
    rw [hS]
    cases R with
    | eq => exact propext Subtype.val_inj
    | mem => rfl

/-- Downward transfer retaining an additional infinitary sentence. Its truth
in the source is an explicit premise, and its truth in the resulting expansion
is part of the conclusion. This applies, in particular, to `FinSmall`. -/
theorem exists_small_deadEnd_expansion_submodel {V : Type} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (T : Theory ℒₛₑₜ) [V↓[ℒₛₑₜ] ⊧* T]
    (χ : Formula deadEndLanguage 0)
    (S : Structure deadEndLanguage V)
    (hS : S.lMap deadEndSetEmbedding = (inferInstance : Structure ℒₛₑₜ V))
    (h : @Formula.Eval deadEndLanguage V S 0 deadEndSentence ![])
    (hχ : @Formula.Eval deadEndLanguage V S 0 χ ![]) :
    ∃ A : Set V, ∃ _ : Nonempty A, ∃ _ : A↓[ℒₛₑₜ] ⊧* 𝗭𝗙,
      A↓[ℒₛₑₜ] ⊧* T ∧ Cardinal.mk A = Cardinal.aleph 1 ∧ IsZFDeadEnd A ∧
      ∃ SA : Structure deadEndLanguage A,
        SA.lMap deadEndSetEmbedding = (inferInstance : Structure ℒₛₑₜ A) ∧
        @Formula.Eval deadEndLanguage A SA 0 deadEndSentence ![] ∧
        @Formula.Eval deadEndLanguage A SA 0 χ ![] := by
  let : Structure deadEndLanguage V := S
  have hVT : V↓[ℒₛₑₜ] ⊧* (𝗭𝗙 ∪ T) := by
    apply models_theory_iff.mpr
    intro φ hφ
    rcases hφ with hφ | hφ
    · exact models_of_mem hφ
    · exact models_of_mem hφ
  let φ := (deadEndTheorySentence T).and χ
  have hφ : φ.Eval (M := V) ![] := (Formula.eval_and _ _ _).mpr
    ⟨(Formula.eval_and _ _ _).mpr ⟨h, (eval_originalTheorySentence S hS _).mpr hVT⟩, hχ⟩
  let A := Infinitary.DownwardLS.hull φ (∅ : Set V)
  let : SetStructure A := closedSubsetSetStructure A
  let : Nonempty (A : Set V) := Infinitary.DownwardLS.hullNonempty _ ∅
  have hA : φ.Eval (M := A) ![] :=
    (Infinitary.DownwardLS.sentence_eval _ ∅).mpr hφ
  have hAS := closedSubset_set_reduct S hS A
  obtain ⟨hbase, hχA⟩ := (Formula.eval_and _ _ _).mp hA
  obtain ⟨hdead, htheory⟩ := (Formula.eval_and _ _ _).mp hbase
  have hAT := (eval_originalTheorySentence A.toStructure hAS _).mp htheory
  have hAZF : A↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := models_theory_iff.mpr fun φ hφ ↦
    models_theory_iff.mp hAT φ (Or.inl hφ)
  let : A↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := hAZF
  refine ⟨(A : Set V), inferInstance, hAZF, ?_, ?_, ?_, A.toStructure, hAS, hdead, hχA⟩
  · exact models_theory_iff.mpr fun φ hφ ↦ models_theory_iff.mp hAT φ (Or.inr hφ)
  · exact le_antisymm (Infinitary.DownwardLS.hull_card_le _ ∅ (by simp))
      (aleph_one_le_of_deadEndSentence A.toStructure hdead)
  · exact isZFDeadEnd_of_deadEndSentence A.toStructure hAS hdead

/-- Downward transfer inside an actual model. No separate satisfiability or
forcing-absoluteness premise is introduced. -/
theorem exists_small_deadEnd_submodel {V : Type} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (T : Theory ℒₛₑₜ) [V↓[ℒₛₑₜ] ⊧* T]
    (S : Structure deadEndLanguage V)
    (hS : S.lMap deadEndSetEmbedding = (inferInstance : Structure ℒₛₑₜ V))
    (h : @Formula.Eval deadEndLanguage V S 0 deadEndSentence ![]) :
    ∃ A : Set V, ∃ _ : Nonempty A, ∃ _ : A↓[ℒₛₑₜ] ⊧* 𝗭𝗙,
      A↓[ℒₛₑₜ] ⊧* T ∧ Cardinal.mk A = Cardinal.aleph 1 ∧ IsZFDeadEnd A := by
  obtain ⟨A, hne, hZF, hT, hcard, hdead, _⟩ :=
    exists_small_deadEnd_expansion_submodel T (.fo ⊤) S hS h trivial
  exact ⟨A, hne, hZF, hT, hcard, hdead⟩

/-- A model-form corollary of the actual-submodel construction. The theory
`T` can include additional principles or their negations. -/
theorem exists_small_deadEnd_model {V : Type} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (T : Theory ℒₛₑₜ) [V↓[ℒₛₑₜ] ⊧* T]
    (S : Structure deadEndLanguage V)
    (hS : S.lMap deadEndSetEmbedding = (inferInstance : Structure ℒₛₑₜ V))
    (h : @Formula.Eval deadEndLanguage V S 0 deadEndSentence ![]) :
    ∃ N : Type, ∃ _ : SetStructure N, ∃ _ : Nonempty N, ∃ _ : N↓[ℒₛₑₜ] ⊧* 𝗭𝗙,
      N↓[ℒₛₑₜ] ⊧* T ∧ Cardinal.mk N = Cardinal.aleph 1 ∧ IsZFDeadEnd N := by
  obtain ⟨A, hne, hZF, hT, hcard, hdead⟩ := exists_small_deadEnd_submodel T S hS h
  exact ⟨A, inferInstance, hne, hZF, hT, hcard, hdead⟩

/-- The strengthened sentence survives size reduction, including its literal
`FinSmall` clause. Its source satisfaction is required explicitly. -/
theorem exists_small_weaklyRubinSentence_submodel {V : Type} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (T : Theory ℒₛₑₜ) [V↓[ℒₛₑₜ] ⊧* T]
    (S : Structure deadEndLanguage V)
    (hS : S.lMap deadEndSetEmbedding = (inferInstance : Structure ℒₛₑₜ V))
    (h : @Formula.Eval deadEndLanguage V S 0 weaklyRubinSentence ![]) :
    ∃ A : Set V, ∃ _ : Nonempty A, ∃ _ : A↓[ℒₛₑₜ] ⊧* 𝗭𝗙,
      A↓[ℒₛₑₜ] ⊧* T ∧ Cardinal.mk A = Cardinal.aleph 1 ∧ IsZFDeadEnd A ∧ FinSmall A ∧
      ∃ SA : Structure deadEndLanguage A,
        SA.lMap deadEndSetEmbedding = (inferInstance : Structure ℒₛₑₜ A) ∧
        @Formula.Eval deadEndLanguage A SA 0 weaklyRubinSentence ![] := by
  obtain ⟨hdead, hfin⟩ := (Formula.eval_and _ _ _).mp h
  obtain ⟨A, hne, hZF, hT, hcard, hdeadA, SA, hSA, hsentA, hfinA⟩ :=
    exists_small_deadEnd_expansion_submodel T finiteSmallSentence S hS hdead hfin
  let : Nonempty A := hne
  let : A↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := hZF
  exact ⟨A, hne, hZF, hT, hcard, hdeadA, (eval_finiteSmallSentence SA hSA).mp hfinA,
    SA, hSA, (Formula.eval_and _ _ _).mpr ⟨hsentA, hfinA⟩⟩

/-- The model-form transfer of Φ⁺ preserves the supplied first-order theory,
the exact cardinality, restricted membership, and the complete expanded sentence. -/
theorem exists_small_weaklyRubinSentence_model {V : Type} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (T : Theory ℒₛₑₜ) [V↓[ℒₛₑₜ] ⊧* T]
    (S : Structure deadEndLanguage V)
    (hS : S.lMap deadEndSetEmbedding = (inferInstance : Structure ℒₛₑₜ V))
    (h : @Formula.Eval deadEndLanguage V S 0 weaklyRubinSentence ![]) :
    ∃ N : Type, ∃ _ : SetStructure N, ∃ _ : Nonempty N, ∃ _ : N↓[ℒₛₑₜ] ⊧* 𝗭𝗙,
      N↓[ℒₛₑₜ] ⊧* T ∧ Cardinal.mk N = Cardinal.aleph 1 ∧ IsZFDeadEnd N ∧ FinSmall N ∧
      ∃ SN : Structure deadEndLanguage N,
        SN.lMap deadEndSetEmbedding = (inferInstance : Structure ℒₛₑₜ N) ∧
        @Formula.Eval deadEndLanguage N SN 0 weaklyRubinSentence ![] := by
  obtain ⟨A, hne, hZF, hT, hcard, hdead, hfin, hS⟩ :=
    exists_small_weaklyRubinSentence_submodel T S hS h
  exact ⟨A, inferInstance, hne, hZF, hT, hcard, hdead, hfin, hS⟩

end ZFVP.Schmerl
