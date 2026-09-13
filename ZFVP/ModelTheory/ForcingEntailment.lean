import ZFVP.ModelTheory.ForcingSemanticConsequence
import ZFVP.ModelTheory.CountableZFTransfer
import ZFVP.SetTheory.BoundedFunctionDomain
import ZFVP.Syntax.ForcingTranslationSemantics

/-! Semantic consequence in every ZF model gives inclusion of forcing truth
sets over an arbitrary ZF ground model. The consequence hypothesis concerns
the formulas themselves, not a forcing or iteration theorem. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

def forcingEntailmentFormula {n : ℕ} (φ ψ : SetTheorySemisentence n) : SetTheorySemisentence 5 :=
  f“P R o p b. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧ p ∈ P ∧
    !boundedFunctionDomainFormula b (!(numeralFormula n)) ∧
    (∀ i ∈ (!(numeralFormula n)), !forcingNameFormula P (!value.dfn b i)) ∧
    !(ordinaryForcingTranslation φ) P R P P p b →
    !(ordinaryForcingTranslation ψ) P R P P p b”

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_forcingEntailmentFormula {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin 5 → V) :
    (forcingEntailmentFormula φ ψ).Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) → v 3 ∈ v 0 →
        IsFunction (v 4) → domain (v 4) = (n : V) →
        (∀ i ∈ (n : V), IsForcingName (v 0) ((v 4) ‘ i)) →
        v 3 ∈ forcingFormula (v 0) (v 1) φ (v 4) →
        v 3 ∈ forcingFormula (v 0) (v 1) ψ (v 4)) := by
  simp [forcingEntailmentFormula, Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Fin.forall_fin_succ]
  constructor
  · intro h hR ht hp hf hd hn hφ
    exact h hR (by rintro a b c rfl rfl rfl; exact ht) hp hf hd hn
      (by rintro a b c d e f rfl rfl rfl rfl rfl rfl; exact hφ)
      _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
  · intro h hR ht hp hf hd hn hφ a b c d e f ha hb hc hd' he hf'
    subst a b c d e f
    exact h hR (ht _ _ _ rfl rfl rfl) hp hf hd hn
      (hφ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl)

theorem standardTuple_values_eq {n : ℕ} {b : V} [IsFunction b] (hb : domain b = (n : V)) :
    standardTuple (fun i : Fin n ↦ b ‘ (i.val : V)) = b := by
  have hbf : b ∈ range b ^ (n : V) := hb ▸ IsFunction.mem_function b
  apply function_eq_of_values (standardTuple_mem_function _ (fun i ↦
    function_value_mem hbf (natCast_mem_of_lt i.isLt))) hbf
  intro x hx
  obtain ⟨i, rfl⟩ := (mem_natCast_iff _ _).mp hx
  exact value_standardTuple _ i

theorem forcingFormula_entailment {n : ℕ} (φ ψ : SetTheorySemisentence n)
    (hvalid : ∀ (W : Type u) [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
      ∀ v : Fin n → W, φ.Evalb v → ψ.Evalb v)
    {P R one p : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hp : p ∈ P) (v : Fin n → ForcingName P)
    (hφ : p ∈ forcingFormula P R φ (standardTuple (fun i ↦ (v i).val))) :
    p ∈ forcingFormula P R ψ (standardTuple (fun i ↦ (v i).val)) := by
  have ht := eval_of_countable_zf (forcingEntailmentFormula φ ψ) (by
    intro W _ _ _ _ b
    apply (eval_forcingEntailmentFormula φ ψ b).mpr
    intro hR ht hp hb hdom hnames hφ
    let := hb
    let v : Fin n → ForcingName (b 0) := fun i ↦
      ⟨(b 4) ‘ (i.val : W), hnames _ (natCast_mem_of_lt i.isLt)⟩
    have hv : standardTuple (fun i ↦ (v i).val) = b 4 := standardTuple_values_eq hdom
    rw [← hv] at hφ ⊢
    apply forcingFormula_of_all_generics hR ht hp ψ v
    intro G hG hpG
    let S : ForcingContext W := ⟨b 0, b 1, b 2, G, hR, ht, hG⟩
    exact hvalid S.Model _ ((S.formula_truth φ v).mpr ⟨b 3, hpG, hφ⟩))
    ![P, R, one, p, standardTuple (fun i ↦ (v i).val)]
  apply (eval_forcingEntailmentFormula φ ψ _).mp ht hR htop hp (standardTuple_isFunction _)
    (domain_standardTuple _) ?_ hφ
  intro i hi
  obtain ⟨j, rfl⟩ := (mem_natCast_iff _ _).mp hi
  simpa using (v j).property

end ZFVP
