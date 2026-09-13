import Mathlib.Tactic.FinCases
import ZFVP.ModelTheory.ArithmeticInterpretation

/-! The interpreted omega model with arithmetic operations and an explicit value map. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic

abbrev InternalArithmetic (V : Type*) [SetStructure V] :=
  Structure.Model ℒₒᵣ (arithmeticInZF.Model V)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def internalArithmeticVal (x : InternalArithmetic V) : V := x.intro.val

theorem internalArithmeticVal_mem (x : InternalArithmetic V) : internalArithmeticVal x ∈ (ω : V) :=
  (arithmeticInZF_domain _).mp x.intro.dom

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem internalArithmeticVal_injective : Function.Injective (internalArithmeticVal (V := V)) := by
  rintro ⟨x⟩ ⟨y⟩ h
  have hxy : x = y := DirectTranslation.Model.ext h
  cases hxy
  rfl

theorem internalArithmeticVal_surjective {x : V} (hx : x ∈ (ω : V)) :
    ∃ n : InternalArithmetic V, internalArithmeticVal n = x :=
  ⟨⟨⟨x, (arithmeticInZF_domain x).mpr hx⟩⟩, rfl⟩

@[simp] theorem internalArithmeticVal_zero : internalArithmeticVal (0 : InternalArithmetic V) = 0 := by
  change (Structure.func (L := ℒₒᵣ) Language.Zero.zero (![] : Fin 0 → arithmeticInZF.Model V)).val = 0
  have h := (DirectTranslation.Model.func_iff (π := arithmeticInZF)
    (f := Language.Zero.zero) (v := (![] : Fin 0 → arithmeticInZF.Model V))).mp rfl
  simpa [arithmeticInZF, arithmeticNaturalFunction, zero_def] using h

@[simp] theorem internalArithmeticVal_one : internalArithmeticVal (1 : InternalArithmetic V) = 1 := by
  change (Structure.func (L := ℒₒᵣ) Language.One.one (![] : Fin 0 → arithmeticInZF.Model V)).val = 1
  have h := (DirectTranslation.Model.func_iff (π := arithmeticInZF)
    (f := Language.One.one) (v := (![] : Fin 0 → arithmeticInZF.Model V))).mp rfl
  simpa [arithmeticInZF, arithmeticNaturalFunction] using h

theorem arithmeticInZF_func_spec {k : ℕ} (f : Language.ORing.Func k)
    (v : Fin k → arithmeticInZF.Model V) (y : arithmeticInZF.Model V)
    (h : (arithmeticNaturalFunction f).Evalb (y.val :> fun i ↦ (v i).val)) :
    y = Structure.func (L := ℒₒᵣ) f v :=
  (DirectTranslation.Model.func_iff (π := arithmeticInZF) (f := f) (v := v) (y := y)).mpr h

theorem arithmeticInZF_add_spec (x y z : arithmeticInZF.Model V)
    (h : z.val = ordinalAdd x.val y.val) : z = Structure.func (L := ℒₒᵣ) Language.ORing.Func.add ![x, y] := by
  have hf := (ordinalAddFormula_defined.iff ![z.val, x.val, y.val]).mpr h
  have hv : (z.val :> fun i : Fin 2 ↦ (![x, y] i).val) = ![z.val, x.val, y.val] := by
    funext i; fin_cases i <;> rfl
  exact arithmeticInZF_func_spec .add ![x, y] z (hv.symm ▸ hf)

theorem arithmeticInZF_mul_spec (x y z : arithmeticInZF.Model V)
    (h : z.val = naturalMul x.val y.val) : z = Structure.func (L := ℒₒᵣ) Language.ORing.Func.mul ![x, y] := by
  have hf := (naturalMulFormula_defined.iff ![z.val, x.val, y.val]).mpr h
  have hv : (z.val :> fun i : Fin 2 ↦ (![x, y] i).val) = ![z.val, x.val, y.val] := by
    funext i; fin_cases i <;> rfl
  exact arithmeticInZF_func_spec .mul ![x, y] z (hv.symm ▸ hf)
@[simp] theorem internalArithmeticVal_add (x y : InternalArithmetic V) :
    internalArithmeticVal (x + y) = ordinalAdd (internalArithmeticVal x) (internalArithmeticVal y) := by
  let z : arithmeticInZF.Model V := ⟨ordinalAdd (internalArithmeticVal x) (internalArithmeticVal y),
    (arithmeticInZF_domain _).mpr (ordinalAdd_natural (internalArithmeticVal_mem x) (internalArithmeticVal_mem y))⟩
  change (Structure.func (L := ℒₒᵣ) Language.ORing.Func.add (fun i : Fin 2 ↦ (![x, y] i).intro)).val = _
  have hv : (fun i : Fin 2 ↦ (![x, y] i).intro) = ![x.intro, y.intro] := by funext i; fin_cases i <;> rfl
  rw [hv]
  have hz := arithmeticInZF_add_spec x.intro y.intro z rfl
  exact (congrArg DirectTranslation.Model.val hz).symm

@[simp] theorem internalArithmeticVal_mul (x y : InternalArithmetic V) :
    internalArithmeticVal (x * y) = naturalMul (internalArithmeticVal x) (internalArithmeticVal y) := by
  let z : arithmeticInZF.Model V := ⟨naturalMul (internalArithmeticVal x) (internalArithmeticVal y),
    (arithmeticInZF_domain _).mpr (naturalMul_natural (internalArithmeticVal_mem x) (internalArithmeticVal_mem y))⟩
  change (Structure.func (L := ℒₒᵣ) Language.ORing.Func.mul (fun i : Fin 2 ↦ (![x, y] i).intro)).val = _
  have hv : (fun i : Fin 2 ↦ (![x, y] i).intro) = ![x.intro, y.intro] := by funext i; fin_cases i <;> rfl
  rw [hv]
  have hz := arithmeticInZF_mul_spec x.intro y.intro z rfl
  exact (congrArg DirectTranslation.Model.val hz).symm
@[simp] theorem internalArithmetic_lt (x y : InternalArithmetic V) :
    x < y ↔ internalArithmeticVal x ∈ internalArithmeticVal y := by
  change (arithmeticNaturalRelation Language.ORing.Rel.lt).Evalb ![x.intro.val, y.intro.val] ↔ _
  simp [arithmeticNaturalRelation, internalArithmeticVal]
omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem internalArithmetic_eq (x y : InternalArithmetic V) :
    x = y ↔ internalArithmeticVal x = internalArithmeticVal y := internalArithmeticVal_injective.eq_iff.symm

theorem internalArithmetic_eval_translation {ξ : Type*} {n : ℕ} (φ : ArithmeticSemiformula ξ n)
    (b : Fin n → InternalArithmetic V) (e : ξ → InternalArithmetic V) :
    (arithmeticInZF.translate φ).Eval (internalArithmeticVal ∘ b) (internalArithmeticVal ∘ e) ↔ φ.Eval b e := by
  have h1 := DirectTranslation.Model.eval_translate_iff (π := arithmeticInZF) (M := V)
    (e := fun i ↦ (b i).intro) (ε := fun i ↦ (e i).intro) (φ := φ)
  let s : Structure ℒₒᵣ (InternalArithmetic V) := Structure.ofEquiv (Structure.Model.equiv ℒₒᵣ (arithmeticInZF.Model V))
  have hs : s = standardModel (InternalArithmetic V) := standardModel_unique _ s
  have h2 := Structure.eval_ofEquiv_iff (Θ := Structure.Model.equiv ℒₒᵣ (arithmeticInZF.Model V))
    (b := b) (f := e) (φ := φ)
  change Semiformula.Eval (s := s) b e φ ↔ _ at h2
  rw [hs] at h2
  exact h1.trans h2.symm

theorem internalArithmetic_translation (φ : ArithmeticSentence) :
    V↓[ℒₛₑₜ] ⊧ arithmeticInZF.translate φ ↔ (InternalArithmetic V)↓[ℒₒᵣ] ⊧ φ := by
  rw [DirectTranslation.Model.translate_iff]
  let s : Structure ℒₒᵣ (InternalArithmetic V) := Structure.ofEquiv (Structure.Model.equiv ℒₒᵣ (arithmeticInZF.Model V))
  have hs : s = standardModel (InternalArithmetic V) := standardModel_unique _ s
  have h := @Structure.ElementaryEquiv.models ℒₒᵣ (arithmeticInZF.Model V) (InternalArithmetic V)
    inferInstance inferInstance inferInstance s inferInstance φ
  rw [hs] at h
  exact h

end ZFVP
