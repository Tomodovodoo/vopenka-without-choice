import ZFVP.Syntax.BoundedForcingMeaning
import ZFVP.Syntax.BoundedStandardTuples

/-! External bounded formulas admit both Sigma_1 answers, uniformly in the preorder.
The name class may be any definable class of names closed under subnames. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingParametersInFormula (n : ℕ) : SetTheorySemisentence (n + 4) :=
  finiteConjunction (fun i : Fin n ↦ .rel Language.Set.Rel.mem ![forcingParameterTerms 4 rfl i, .bvar 0])

theorem forcingParametersInFormula_bounded (n : ℕ) : IsBoundedSetFormula (forcingParametersInFormula n) :=
  finiteConjunction_bounded _ (fun _ ↦ .rel _ _)

def BoundedFormulaTree.forcingCertificate {n : ℕ} (φ : BoundedFormulaTree n) (answer : Bool) :
    SetTheorySemisentence (n + 3) :=
  .exs ((IsTransitive.dfn.subst ![.bvar 0]).and
    ((forcingParametersInFormula n).and (φ.forcingSigma answer)))

def BoundedFormulaTree.forcingPi {n : ℕ} (φ : BoundedFormulaTree n) : SetTheorySemisentence (n + 3) :=
  ∼φ.forcingCertificate false

theorem BoundedFormulaTree.forcingCertificate_sigmaOne {n : ℕ} (φ : BoundedFormulaTree n) (answer : Bool) :
    IsSigmaFormula 1 (φ.forcingCertificate answer) :=
  .exs (.and (.bounded (isTransitiveFormula_bounded.subst _))
    (.and (.bounded (forcingParametersInFormula_bounded n)) (φ.forcingSigma_sigmaOne answer)))

theorem BoundedFormulaTree.forcingPi_piOne {n : ℕ} (φ : BoundedFormulaTree n) :
    IsPiFormula 1 φ.forcingPi := (φ.forcingCertificate_sigmaOne false).neg

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_forcingParametersInFormula {n : ℕ} (T P R p : V) (v : Fin n → V) :
    (forcingParametersInFormula n).Evalb (T :> P :> R :> p :> v) ↔ ∀ i, v i ∈ T := by
  rw [forcingParametersInFormula, eval_finiteConjunction]
  apply forall_congr'
  intro i
  simp [forcingParameterTerms, Semiformula.Evalb, Structure.rel]

theorem exists_transitive_parameters {n : ℕ} (v : Fin n → V) :
    ∃ T : V, IsTransitive T ∧ ∀ i, v i ∈ T := by
  refine ⟨transitiveClosure (range (standardTuple v)), transitiveClosure_transitive _, ?_⟩
  intro i
  apply subset_transitiveClosure
  exact mem_range_iff.mpr ⟨(i.val : V), (mem_standardTuple_iff v _).mpr ⟨i, rfl⟩⟩

theorem BoundedFormulaTree.forcingCertificate_meaning {P R : V} (hR : IsForcingPreorder P R)
    (N : V → Prop) (hN : ℒₛₑₜ-predicate N) (hnames : ∀ x, N x → IsForcingName P x)
    (hclosed : ∀ x, N x → ∀ u s, ⟨u, s⟩ₖ ∈ x → N u)
    {n : ℕ} (φ : BoundedFormulaTree n) (v : Fin n → V) (hv : ∀ i, N (v i))
    (answer : Bool) (p : V) :
    (φ.forcingCertificate answer).Evalb (P :> R :> p :> v) ↔
      TruthAnswer answer (p ∈ classForcingFormula P R N hN φ.formula (standardTuple v)) := by
  have he : (φ.forcingCertificate answer).Evalb (P :> R :> p :> v) ↔
      ∃ T : V, IsTransitive T ∧ (∀ i, v i ∈ T) ∧
        (φ.forcingSigma answer).Evalb (T :> P :> R :> p :> v) := by
    change (∃ T : V, (IsTransitive.dfn.subst ![.bvar 0]).Evalb (T :> P :> R :> p :> v) ∧
      (forcingParametersInFormula n).Evalb (T :> P :> R :> p :> v) ∧
        (φ.forcingSigma answer).Evalb (T :> P :> R :> p :> v)) ↔ _
    simp [Semiformula.eval_substs, eval_forcingParametersInFormula]
  rw [he]
  constructor
  · rintro ⟨T, hT, hvT, hφ⟩
    let := hT
    exact (φ.forcingSigma_meaning hR N hN hnames hclosed v hv hvT answer p).mp hφ
  · intro hφ
    obtain ⟨T, hT, hvT⟩ := exists_transitive_parameters v
    let := hT
    exact ⟨T, hT, hvT, (φ.forcingSigma_meaning hR N hN hnames hclosed v hv hvT answer p).mpr hφ⟩

theorem BoundedFormulaTree.forcingPi_meaning {P R : V} (hR : IsForcingPreorder P R)
    (N : V → Prop) (hN : ℒₛₑₜ-predicate N) (hnames : ∀ x, N x → IsForcingName P x)
    (hclosed : ∀ x, N x → ∀ u s, ⟨u, s⟩ₖ ∈ x → N u)
    {n : ℕ} (φ : BoundedFormulaTree n) (v : Fin n → V) (hv : ∀ i, N (v i)) (p : V) :
    φ.forcingPi.Evalb (P :> R :> p :> v) ↔
      p ∈ classForcingFormula P R N hN φ.formula (standardTuple v) := by
  simp [forcingPi, φ.forcingCertificate_meaning hR N hN hnames hclosed v hv, TruthAnswer]

theorem bounded_forcing_deltaOne_formulas {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsBoundedSetFormula φ) :
    ∃ σ π : SetTheorySemisentence (n + 3), IsSigmaFormula 1 σ ∧ IsPiFormula 1 π ∧
      ∀ (P R : V), IsForcingPreorder P R → ∀ (N : V → Prop) (hN : ℒₛₑₜ-predicate N),
        (∀ x, N x → IsForcingName P x) → (∀ x, N x → ∀ u s, ⟨u, s⟩ₖ ∈ x → N u) →
        ∀ (v : Fin n → V), (∀ i, N (v i)) → ∀ p,
          (σ.Evalb (P :> R :> p :> v) ↔ p ∈ classForcingFormula P R N hN φ (standardTuple v)) ∧
          (π.Evalb (P :> R :> p :> v) ↔ p ∈ classForcingFormula P R N hN φ (standardTuple v)) := by
  obtain ⟨t, rfl⟩ := boundedFormulaTree_exists hφ
  refine ⟨t.forcingCertificate true, t.forcingPi, t.forcingCertificate_sigmaOne true, t.forcingPi_piOne, ?_⟩
  intro P R hR N hN hnames hclosed v hv p
  exact ⟨t.forcingCertificate_meaning hR N hN hnames hclosed v hv true p,
    t.forcingPi_meaning hR N hN hnames hclosed v hv p⟩

end ZFVP
