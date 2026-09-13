import ZFVP.SetTheory.UniformNameEvaluation
import ZFVP.SetTheory.UniformFormulaName
import ZFVP.ModelTheory.ForcingModelEvaluation
import ZFVP.SetTheory.FunctionComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def evaluatedUnionFormula : SetTheorySemisentence 3 :=
  f“U E f. ∀ x, x ∈ U ↔ ∃ y ∈ !range.dfn f, x ∈ !value.dfn E y”

def forcingEvaluatedUnionFormula : SetTheorySemisentence 6 :=
  f“U P R o C f. !(formulaUniqueNameFormula evaluatedUnionFormula) U P R
    (!assignmentPrependFormula (!(numeralFormula 1))
      (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) f)
      (!nameEvaluationGraphFormula o C))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def evaluatedUnion (E f : V) : V :=
  ⋃ˢ (repl (fun y ↦ E ‘ y) (by definability) (range f))

theorem mem_evaluatedUnion_iff (E f x : V) :
    x ∈ evaluatedUnion E f ↔ ∃ y ∈ range f, x ∈ E ‘ y := by
  simp only [evaluatedUnion, mem_sUnion_iff, repl_spec]
  constructor
  · rintro ⟨z, ⟨y, hy, rfl⟩, hx⟩
    exact ⟨y, hy, hx⟩
  · rintro ⟨y, hy, hx⟩
    exact ⟨_, ⟨y, hy, rfl⟩, hx⟩

instance evaluatedUnionFormula_defined :
    ℒₛₑₜ-function₂[V] evaluatedUnion via evaluatedUnionFormula :=
  ⟨fun v ↦ by
    simp [evaluatedUnionFormula]
    rw [mem_ext_iff]
    simp only [mem_evaluatedUnion_iff]⟩

instance evaluatedUnion_definable : ℒₛₑₜ-function₂[V] evaluatedUnion :=
  evaluatedUnionFormula_defined.to_definable

theorem evaluatedUnion_eq_union_compose {E f X Y Z : V}
    (hf : f ∈ Y ^ X) (hE : E ∈ Z ^ Y) :
    evaluatedUnion E f = ⋃ˢ range (compose f E) := by
  let := IsFunction.of_mem hf
  let := IsFunction.of_mem hE
  apply mem_ext
  intro x
  rw [mem_evaluatedUnion_iff, mem_sUnion_iff]
  constructor
  · rintro ⟨y, hy, hx⟩
    obtain ⟨i, hiy⟩ := mem_range_iff.mp hy
    have hi : i ∈ X := by
      simpa only [domain_eq_of_mem_function hf] using mem_domain_of_kpair_mem hiy
    have he : f ‘ i = y := value_eq_of_kpair_mem hiy
    refine ⟨E ‘ y, ?_, hx⟩
    have hv := value_mem_range (compose_function hf hE) hi
    simpa only [value_compose_of_mem_function hf hE hi, he] using hv
  · rintro ⟨z, hz, hx⟩
    obtain ⟨i, hiz⟩ := mem_range_iff.mp hz
    obtain ⟨a, b, c, hab, hbc, he⟩ := mem_compose_iff.mp hiz
    obtain ⟨rfl, rfl⟩ := kpair_iff.mp he
    exact ⟨b, mem_range_of_kpair_mem hab, (value_eq_of_kpair_mem hbc).symm ▸ hx⟩

theorem evaluatedUnion_subset {E f B : V}
    (h : ∀ y ∈ range f, E ‘ y ⊆ B) : evaluatedUnion E f ⊆ B := by
  intro x hx
  obtain ⟨y, hy, hx⟩ := (mem_evaluatedUnion_iff _ _ _).mp hx
  exact h y hy x hx

theorem evaluatedUnion_empty {E f : V}
    (h : ∀ y ∈ range f, E ‘ y = ∅) : evaluatedUnion E f = ∅ := by
  apply subset_empty_iff_eq_empty.mp
  apply evaluatedUnion_subset
  intro y hy
  rw [h y hy]

noncomputable def forcingEvaluatedUnion (P R one C f : V) : V :=
  formulaUniqueName P R evaluatedUnionFormula
    (standardTuple ![nameEvaluationGraph one C, f])

instance forcingEvaluatedUnionFormula_defined :
    ℒₛₑₜ-function₅[V] forcingEvaluatedUnion via forcingEvaluatedUnionFormula :=
  ⟨fun v ↦ by simp [forcingEvaluatedUnionFormula, forcingEvaluatedUnion, standardTuple]⟩

instance forcingEvaluatedUnion_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (forcingEvaluatedUnion (V := V)) :=
  forcingEvaluatedUnionFormula_defined.to_definable

theorem forcingEvaluatedUnion_isName (P R one C f : V) :
    IsForcingName P (forcingEvaluatedUnion P R one C f) :=
  formulaUniqueName_isName _ _ _ _

namespace ForcingContext
variable (A : ForcingContext V)

theorem forcingEvaluatedUnion_value (C : V) (hC : ∀ σ ∈ C, IsForcingName A.P σ)
    (f : ForcingName A.P) :
    A.ofName ⟨forcingEvaluatedUnion A.P A.R A.one C f.val,
      forcingEvaluatedUnion_isName _ _ _ _ _⟩ =
        evaluatedUnion (A.evaluationGraph C hC) (A.ofName f) := by
  let E : ForcingName A.P := ⟨nameEvaluationGraph A.one C,
    nameEvaluationGraph_isName A.top.1 hC⟩
  change A.ofName (A.formulaName evaluatedUnionFormula ![E, f]) = _
  apply A.formulaName_value
  · intro x y hx hy
    simp at hx hy
    exact hx.trans hy.symm
  · simp [E, evaluationGraph]

theorem mem_forcingEvaluatedUnion_iff (C : V) (hC : ∀ σ ∈ C, IsForcingName A.P σ)
    (f : ForcingName A.P) {X : A.Model} (hf : A.ofName f ∈ A.check C ^ X)
    (x : A.Model) :
    x ∈ A.ofName ⟨forcingEvaluatedUnion A.P A.R A.one C f.val,
      forcingEvaluatedUnion_isName _ _ _ _ _⟩ ↔
        ∃ i ∈ X, ∃ σ, ∃ hσ : σ ∈ C,
          (A.ofName f) ‘ i = A.check σ ∧ x ∈ A.ofName ⟨σ, hC σ hσ⟩ := by
  rw [A.forcingEvaluatedUnion_value C hC f, mem_evaluatedUnion_iff]
  let := IsFunction.of_mem hf
  constructor
  · rintro ⟨y, hy, hx⟩
    obtain ⟨i, hiy⟩ := mem_range_iff.mp hy
    have hi : i ∈ X := by
      simpa only [domain_eq_of_mem_function hf] using mem_domain_of_kpair_mem hiy
    have he : (A.ofName f) ‘ i = y := value_eq_of_kpair_mem hiy
    obtain ⟨σ, hσ, rfl⟩ := (A.mem_check_iff C y).mp (he ▸ function_value_mem hf hi)
    refine ⟨i, hi, σ, hσ, he, ?_⟩
    simpa only [A.evaluationGraph_value C hC σ hσ] using hx
  · rintro ⟨i, hi, σ, hσ, he, hx⟩
    refine ⟨A.check σ, ?_, ?_⟩
    · exact he ▸ value_mem_range hf hi
    · simpa only [A.evaluationGraph_value C hC σ hσ] using hx

end ForcingContext
end ZFVP
