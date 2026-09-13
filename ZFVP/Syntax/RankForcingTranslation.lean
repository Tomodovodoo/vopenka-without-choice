import ZFVP.Syntax.LevyForcingStepSemantics
import ZFVP.SetTheory.CnAbsoluteness

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- The atomic clauses use Sigma-one certificates. Quantifiers range over names
in the structure in which this formula is evaluated. -/
def rankForcingTranslation : {n : ℕ} → SetTheorySemisentence n → SetTheorySemisentence (n + 5)
  | _, .verum => .rel Language.Set.Rel.mem ![.bvar 4, .bvar 0]
  | _, .falsum => .falsum
  | _, .rel r ts => (BoundedFormulaTree.rel r ts).levyForcingBase .sigma
  | _, .nrel r ts => (BoundedFormulaTree.nrel r ts).levyForcingBase .sigma
  | _, .and φ ψ => (rankForcingTranslation φ).and (rankForcingTranslation ψ)
  | _, .or φ ψ => levyForcingOrStep (rankForcingTranslation φ) (rankForcingTranslation ψ)
  | _, .all φ => levyForcingAllStep false (rankForcingTranslation φ)
  | _, .exs φ => levyForcingExsStep false (rankForcingTranslation φ)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {δ : V} (hδ : Cn 1 δ)

include hδ in
private theorem rank_pair_eval (R a b : SetDomain (hierarchy δ)) :
    boundedPairMemberFormula.Evalb ![R, a, b] ↔ ⟨a.val, b.val⟩ₖ ∈ R.val := by
  let := hδ.ordinal
  let := hierarchy_transitive δ
  have he := bounded_formula_absolute (hierarchy δ) boundedPairMemberFormula_bounded ![R, a, b]
  simpa [Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton] using he

include hδ in
private theorem rank_name_eval (P Γ F a : SetDomain (hierarchy δ)) :
    (sigmaOneForcingNameClassFormula false).Evalb ![P, Γ, F, a] ↔ IsForcingName P.val a.val := by
  have he := hδ.sigma_correct (sigmaOneForcingNameClassFormula_sigmaOne false) ![P, Γ, F, a]
  simpa [sigmaOneForcingNameClassFormula, Matrix.comp_vecCons', Function.comp_def,
    Matrix.constant_eq_singleton] using he

private theorem rank_mem_eval (x y : SetDomain (hierarchy δ)) : x ∈ y ↔ x.val ∈ y.val := Iff.rfl

private theorem eval_and {W : Type*} [SetStructure W] {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → W) :
    (φ.and ψ).Evalb v ↔ φ.Evalb v ∧ ψ.Evalb v := Iff.rfl
private theorem eval_or {W : Type*} [SetStructure W] {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → W) :
    (φ.or ψ).Evalb v ↔ φ.Evalb v ∨ ψ.Evalb v := Iff.rfl
private theorem eval_all {W : Type*} [SetStructure W] {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (v : Fin n → W) :
    φ.all.Evalb v ↔ ∀ x : W, φ.Evalb (x :> v) := Iff.rfl
private theorem eval_exs {W : Type*} [SetStructure W] {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (v : Fin n → W) :
    φ.exs.Evalb v ↔ ∃ x : W, φ.Evalb (x :> v) := Iff.rfl

include hδ in
theorem eval_rankForcingOrStep {n : ℕ} (φ ψ : SetTheorySemisentence (n + 5))
    (P R Γ F p : SetDomain (hierarchy δ)) (v : Fin n → SetDomain (hierarchy δ)) :
    (levyForcingOrStep φ ψ).Evalb (P :> R :> Γ :> F :> p :> v) ↔
      p.val ∈ P.val ∧ ∀ q : SetDomain (hierarchy δ), q.val ∈ P.val → ⟨q.val, p.val⟩ₖ ∈ R.val →
        ∃ r : SetDomain (hierarchy δ), r.val ∈ P.val ∧ ⟨r.val, q.val⟩ₖ ∈ R.val ∧
          (φ.Evalb (P :> R :> Γ :> F :> r :> v) ∨ ψ.Evalb (P :> R :> Γ :> F :> r :> v)) := by
  simp [levyForcingOrStep, eval_and, eval_or, eval_boundedSetAll, eval_boundedSetExs,
    forcingSystemSubst, Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
    Function.comp_def, forcingParameterTerms, Structure.rel, rank_mem_eval, rank_pair_eval hδ, ← imp_iff_not_or]

include hδ in
theorem eval_rankForcingAllStep {n : ℕ} (φ : SetTheorySemisentence (n + 1 + 5))
    (P R Γ F p : SetDomain (hierarchy δ)) (v : Fin n → SetDomain (hierarchy δ)) :
    (levyForcingAllStep false φ).Evalb (P :> R :> Γ :> F :> p :> v) ↔
      p.val ∈ P.val ∧ ∀ u : SetDomain (hierarchy δ), IsForcingName P.val u.val →
        φ.Evalb (P :> R :> Γ :> F :> p :> u :> v) := by
  simp [levyForcingAllStep, eval_and, eval_or, eval_all, forcingSystemSubst, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def, forcingParameterTerms,
    Structure.rel, rank_mem_eval, rank_name_eval hδ, ← imp_iff_not_or]

include hδ in
theorem eval_rankForcingExsStep {n : ℕ} (φ : SetTheorySemisentence (n + 1 + 5))
    (P R Γ F p : SetDomain (hierarchy δ)) (v : Fin n → SetDomain (hierarchy δ)) :
    (levyForcingExsStep false φ).Evalb (P :> R :> Γ :> F :> p :> v) ↔
      p.val ∈ P.val ∧ ∀ q : SetDomain (hierarchy δ), q.val ∈ P.val → ⟨q.val, p.val⟩ₖ ∈ R.val →
        ∃ r : SetDomain (hierarchy δ), r.val ∈ P.val ∧ ⟨r.val, q.val⟩ₖ ∈ R.val ∧
          ∃ u : SetDomain (hierarchy δ), IsForcingName P.val u.val ∧
            φ.Evalb (P :> R :> Γ :> F :> r :> u :> v) := by
  simp [levyForcingExsStep, eval_and, eval_or, eval_exs, eval_boundedSetAll, eval_boundedSetExs,
    forcingSystemSubst, Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
    Function.comp_def, forcingParameterTerms, Structure.rel, rank_mem_eval, rank_pair_eval hδ, rank_name_eval hδ,
    ← imp_iff_not_or]

end ZFVP
