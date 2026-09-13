import ZFVP.SetTheory.UniformFormulaName
import ZFVP.ModelTheory.ForcingEntailment

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def formulaNameForcingFormula {n : ℕ} (φ : SetTheorySemisentence (n + 1)) : SetTheorySemisentence 6 :=
  f“P R o p b U. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧ p ∈ P ∧
    !boundedFunctionDomainFormula b (!(numeralFormula n)) ∧
    (∀ i ∈ (!(numeralFormula n)), !forcingNameFormula P (!value.dfn b i)) ∧
    !(formulaUniqueNameFormula φ) U P R b → !(formulaOutputTruthFormula φ) P R b U p”

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_formulaNameForcingFormula {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (v : Fin 6 → V) :
    (formulaNameForcingFormula φ).Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) → v 3 ∈ v 0 →
        IsFunction (v 4) → domain (v 4) = (n : V) →
        (∀ i ∈ (n : V), IsForcingName (v 0) ((v 4) ‘ i)) →
        v 5 = formulaUniqueName (v 0) (v 1) φ (v 4) →
        v 3 ∈ forcingFormula (v 0) (v 1) φ (assignmentPrepend (n : V) (v 4) (v 5))) := by
  simp [formulaNameForcingFormula, Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Fin.forall_fin_succ]
  constructor
  · intro h hR ht hp hf hd hn hu
    exact h hR (by rintro a b c rfl rfl rfl; exact ht) hp hf hd hn
      (by rintro a b c d rfl rfl rfl rfl; exact hu)
      _ _ _ _ _ rfl rfl rfl rfl rfl
  · intro h hR ht hp hf hd hn hu a b c d e ha hb hc hd' he
    subst a b c d e
    exact h hR (ht _ _ _ rfl rfl rfl) hp hf hd hn (hu _ _ _ _ rfl rfl rfl rfl)

/-- Every condition forces the specification of a uniformly named total
unique function. Countability is used only inside the ZF transfer argument. -/
theorem formulaUniqueName_forces {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (hvalid : ∀ (W : Type u) [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
      ∀ v : Fin n → W, ∃! x : W, φ.Evalb (x :> v))
    {P R one p : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hp : p ∈ P) (v : Fin n → ForcingName P) :
    p ∈ forcingFormula P R φ (assignmentPrepend (n : V) (standardTuple (fun i ↦ (v i).val))
      (formulaUniqueName P R φ (standardTuple (fun i ↦ (v i).val)))) := by
  have hall := eval_of_countable_zf (formulaNameForcingFormula φ) (by
    intro W _ _ _ _ b
    apply (eval_formulaNameForcingFormula φ b).mpr
    intro hR ht hp hb hdom hnames hu
    let := hb
    let v : Fin n → ForcingName (b 0) := fun i ↦
      ⟨(b 4) ‘ (i.val : W), hnames _ (natCast_mem_of_lt i.isLt)⟩
    have hv : standardTuple (fun i ↦ (v i).val) = b 4 := standardTuple_values_eq hdom
    rw [hu, ← hv]
    let τ : ForcingName (b 0) := ⟨formulaUniqueName (b 0) (b 1) φ
      (standardTuple (fun i ↦ (v i).val)), formulaUniqueName_isName _ _ _ _⟩
    change b 3 ∈ forcingFormula (b 0) (b 1) φ (standardTuple (fun i ↦ ((τ :> v) i).val))
    apply forcingFormula_of_all_generics hR ht hp φ (τ :> v)
    intro G hG _hpG
    let A : ForcingContext W := ⟨b 0, b 1, b 2, G, hR, ht, hG⟩
    have hs := A.formulaName_spec φ v (hvalid A.Model (fun i ↦ A.ofName (v i)))
    have hv' : (fun i ↦ A.ofName ((τ :> v) i)) = A.ofName (A.formulaName φ v) :> (fun i ↦ A.ofName (v i)) := by
      funext i
      exact Fin.cases rfl (fun _ ↦ rfl) i
    rw [hv']
    exact hs)
    ![P, R, one, p, standardTuple (fun i ↦ (v i).val),
      formulaUniqueName P R φ (standardTuple (fun i ↦ (v i).val))]
  apply (eval_formulaNameForcingFormula φ _).mp hall hR htop hp (standardTuple_isFunction _)
    (domain_standardTuple _) ?_ rfl
  intro i hi
  obtain ⟨j, rfl⟩ := (mem_natCast_iff _ _).mp hi
  simpa using (v j).property

end ZFVP
