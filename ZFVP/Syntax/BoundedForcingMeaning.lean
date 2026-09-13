import ZFVP.Syntax.BoundedForcingTranslation
import ZFVP.Syntax.BoundedForcingStepSemantics

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem bounded_pair_forall_congr {T x : V} [IsTransitive T] (hx : x ∈ T)
    {F G : V → V → Prop} (h : ∀ u s, ⟨u, s⟩ₖ ∈ x → (F u s ↔ G u s)) :
    (∀ u ∈ T, ∀ s ∈ T, ⟨u, s⟩ₖ ∈ x → F u s) ↔ ∀ u s, ⟨u, s⟩ₖ ∈ x → G u s := by
  constructor
  · intro hf u s hus
    obtain ⟨hu, hs⟩ := subname_pair_components_mem_transitive hx hus
    exact (h u s hus).mp (hf u hu s hs hus)
  · intro hg u _ s _ hus
    exact (h u s hus).mpr (hg u s hus)

theorem bounded_pair_exists_congr {T x : V} [IsTransitive T] (hx : x ∈ T)
    {F G : V → V → Prop} (h : ∀ u s, ⟨u, s⟩ₖ ∈ x → (F u s ↔ G u s)) :
    (∃ u ∈ T, ∃ s ∈ T, ⟨u, s⟩ₖ ∈ x ∧ F u s) ↔ ∃ u s, ⟨u, s⟩ₖ ∈ x ∧ G u s := by
  constructor
  · rintro ⟨u, _, s, _, hus, hf⟩
    exact ⟨u, s, hus, (h u s hus).mp hf⟩
  · rintro ⟨u, s, hus, hg⟩
    obtain ⟨hu, hs⟩ := subname_pair_components_mem_transitive hx hus
    exact ⟨u, hu, s, hs, hus, (h u s hus).mpr hg⟩

theorem forcingTermValue_standard_property {n : ℕ} (t : SetTheorySemiterm Empty n)
    (v : Fin n → V) (Q : V → Prop) (hv : ∀ i, Q (v i)) :
    Q (forcingTermValue t (standardTuple v)) := by
  rw [forcingTermValue_standard]
  cases t with
  | bvar i => exact hv i
  | fvar x => exact Empty.elim x
  | func f _ => exact Empty.elim f

theorem BoundedFormulaTree.forcingSigma_meaning {P R T : V} [IsTransitive T]
    (hR : IsForcingPreorder P R) (N : V → Prop) (hN : ℒₛₑₜ-predicate N)
    (hnames : ∀ x, N x → IsForcingName P x)
    (hclosed : ∀ x, N x → ∀ u s, ⟨u, s⟩ₖ ∈ x → N u)
    {n : ℕ} (φ : BoundedFormulaTree n) (v : Fin n → V)
    (hv : ∀ i, N (v i)) (hvT : ∀ i, v i ∈ T) (answer : Bool) (p : V) :
    (φ.forcingSigma answer).Evalb (T :> P :> R :> p :> v) ↔
      TruthAnswer answer (p ∈ classForcingFormula P R N hN φ.formula (standardTuple v)) := by
  classical
  induction φ generalizing answer p with
  | verum => cases answer <;> rfl
  | falsum =>
    cases answer
    · change True ↔ p ∉ (∅ : V)
      simp
    · change False ↔ p ∈ (∅ : V)
      simp
  | rel r ts => exact eval_forcingAtomicSigmaStep r ts answer T P R p v
  | nrel r ts =>
    simp only [forcingSigma, eval_forcingNegationSigmaStep, eval_forcingAtomicSigmaStep,
      formula, classForcingFormula_nrel, mem_forcingNegation_iff]
    cases answer <;> simp [TruthAnswer, ← imp_iff_not_or]
  | and φ ψ ihφ ihψ =>
    simp only [forcingSigma, eval_forcingAndSigmaStep, ihφ v hv hvT, ihψ v hv hvT, formula, classForcingFormula_and,
      mem_inter_iff]
    cases answer <;> simp [TruthAnswer, ← imp_iff_not_or]
  | or φ ψ ihφ ihψ =>
    have hφP := (classForcingFormula_regular N hN hR φ.formula (standardTuple v)).1
    have hψP := (classForcingFormula_regular N hN hR ψ.formula (standardTuple v)).1
    have he (q : V) :
        (∃ r ∈ classForcingFormula P R N hN φ.formula (standardTuple v) ∪
          classForcingFormula P R N hN ψ.formula (standardTuple v), ⟨r, q⟩ₖ ∈ R) ↔
        ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ (r ∈ classForcingFormula P R N hN φ.formula (standardTuple v) ∨
          r ∈ classForcingFormula P R N hN ψ.formula (standardTuple v)) := by
      simp only [mem_union_iff]
      constructor
      · rintro ⟨r, hr, hrq⟩
        exact ⟨r, hr.elim (hφP r) (hψP r), hrq, hr⟩
      · rintro ⟨r, _, hrq, hr⟩
        exact ⟨r, hr, hrq⟩
    simp only [forcingSigma, eval_forcingOrSigmaStep, ihφ v hv hvT, ihψ v hv hvT, formula, classForcingFormula_or,
      mem_forcingClosure_iff, he]
    cases answer <;> simp [TruthAnswer, ← imp_iff_not_or]
  | all t φ ih =>
    have htN := forcingTermValue_standard_property t v N hv
    have htT := forcingTermValue_standard_property t v (fun x ↦ x ∈ T) hvT
    have hs := hclosed _ htN
    have hi (u s : V) (hus : ⟨u, s⟩ₖ ∈ forcingTermValue t (standardTuple v)) (a : Bool) (q : V) :=
      ih (u :> v) (by intro i; exact Fin.cases (hs u s hus) (fun j ↦ hv j) i)
        (by intro i; exact Fin.cases (subname_pair_components_mem_transitive htT hus).1 (fun j ↦ hvT j) i) a q
    simp only [forcingSigma, eval_forcingAllSigmaStep, formula]
    rw [classForcingFormula_boundedAll_iff hR N hN t φ.formula v (hnames _ htN) hs]
    cases answer <;> simp only [TruthAnswer, Bool.false_eq_true, reduceIte]
    all_goals simp only [← forcingTermValue_standard]
    · rw [not_and_or]
      simp only [not_forall, exists_prop]
      apply or_congr Iff.rfl
      apply bounded_pair_exists_congr htT
      intro u s hus
      simp only [hi u s hus, TruthAnswer, Bool.false_eq_true, reduceIte]
    · apply and_congr Iff.rfl
      apply bounded_pair_forall_congr htT
      intro u s hus
      simp only [hi u s hus, TruthAnswer, reduceIte]
  | exs t φ ih =>
    have htN := forcingTermValue_standard_property t v N hv
    have htT := forcingTermValue_standard_property t v (fun x ↦ x ∈ T) hvT
    have hs := hclosed _ htN
    have hi (u s : V) (hus : ⟨u, s⟩ₖ ∈ forcingTermValue t (standardTuple v)) (a : Bool) (q : V) :=
      ih (u :> v) (by intro i; exact Fin.cases (hs u s hus) (fun j ↦ hv j) i)
        (by intro i; exact Fin.cases (subname_pair_components_mem_transitive htT hus).1 (fun j ↦ hvT j) i) a q
    simp only [forcingSigma, eval_forcingExsSigmaStep, formula]
    rw [classForcingFormula_boundedExs_iff hR N hN t φ.formula v (hnames _ htN) hs]
    cases answer <;> simp only [TruthAnswer, Bool.false_eq_true, reduceIte]
    all_goals simp only [← forcingTermValue_standard]
    · rw [not_and_or]
      simp only [not_forall, not_exists, not_and, exists_prop]
      apply or_congr Iff.rfl
      apply exists_congr
      intro q
      apply and_congr Iff.rfl
      apply and_congr Iff.rfl
      apply forall_congr'
      intro r
      apply imp_congr_right
      intro _
      apply imp_congr_right
      intro _
      apply bounded_pair_forall_congr htT
      intro u s hus
      simp only [hi u s hus, TruthAnswer, Bool.false_eq_true, reduceIte]
    · apply and_congr Iff.rfl
      apply forall_congr'
      intro q
      apply imp_congr_right
      intro _
      apply imp_congr_right
      intro _
      apply exists_congr
      intro r
      apply and_congr Iff.rfl
      apply and_congr Iff.rfl
      apply bounded_pair_exists_congr htT
      intro u s hus
      simp only [hi u s hus, TruthAnswer, reduceIte]

end ZFVP
