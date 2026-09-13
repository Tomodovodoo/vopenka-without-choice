import ZFVP.Syntax.PrimitiveProgramSyntaxRequirements

/-! A course-of-values program deciding validity and bound-variable requirements
for natural membership-formula codes, including nonstandard internal inputs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def quantifyRequirement : PrimitiveProgram :=
  ifZero identity .zero (ifEqual identity (constant 1) (constant 1) predecessor)

def formulaRequirementStep (allowFree : Bool) : PrimitiveProgram :=
  let n := .comp .left .right
  let t := .comp listHead n
  let c := .comp listTail n
  let table := .comp .right .right
  let prev := fun i ↦ .comp listGet (.pair table (.comp subtraction (.pair n (.comp .succ i))))
  let atom := .comp (atomicRequirement allowFree) c
  let bin := .comp joinRequirements (.pair (prev (.comp .left c)) (prev (.comp .right c)))
  let quant := .comp quantifyRequirement (prev c)
  ifZero n .zero
    (ifEqual t (constant 0) atom
    (ifEqual t (constant 1) atom
    (ifEqual t (constant 2) (constant 1)
    (ifEqual t (constant 3) (constant 1)
    (ifEqual t (constant 4) bin
    (ifEqual t (constant 5) bin
    (ifEqual t (constant 6) quant
    (ifEqual t (constant 7) quant .zero))))))))

def formulaRequirement (allowFree : Bool) : PrimitiveProgram :=
  .comp (courseEval (formulaRequirementStep allowFree)) (.pair .zero identity)

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_quantifyRequirement (r : M) :
    quantifyRequirement.evalArithmetic r = if r = 0 then 0 else if r = 1 then 1 else r - 1 := by
  simp [quantifyRequirement]

noncomputable def formulaRequirementValue (allowFree : Bool) (t c : M) (F : M → M) : M :=
  if t = 0 then (atomicRequirement allowFree).evalArithmetic c
  else if t = 1 then (atomicRequirement allowFree).evalArithmetic c
  else if t = 2 then 1
  else if t = 3 then 1
  else if t = 4 then joinRequirements.evalArithmetic (Arithmetic.pair (F (Arithmetic.pi₁ c)) (F (Arithmetic.pi₂ c)))
  else if t = 5 then joinRequirements.evalArithmetic (Arithmetic.pair (F (Arithmetic.pi₁ c)) (F (Arithmetic.pi₂ c)))
  else if t = 6 then quantifyRequirement.evalArithmetic (F c)
  else if t = 7 then quantifyRequirement.evalArithmetic (F c)
  else 0

@[simp] theorem evalArithmetic_formulaRequirementStep (allowFree : Bool) (z n table : M) :
    (formulaRequirementStep allowFree).evalArithmetic (Arithmetic.pair z (Arithmetic.pair n table)) =
      if n = 0 then 0 else formulaRequirementValue allowFree (Arithmetic.pi₁ (n - 1)) (Arithmetic.pi₂ (n - 1))
        (fun i ↦ listGet.evalArithmetic (Arithmetic.pair table (n - (i + 1)))) := by
  simp [formulaRequirementStep, formulaRequirementValue]

theorem evalArithmetic_formulaRequirement (allowFree : Bool) (n : M) :
    (formulaRequirement allowFree).evalArithmetic n =
      if n = 0 then 0 else formulaRequirementValue allowFree (Arithmetic.pi₁ (n - 1)) (Arithmetic.pi₂ (n - 1))
        (fun i ↦ listGet.evalArithmetic (Arithmetic.pair
          ((courseTable (formulaRequirementStep allowFree)).evalArithmetic (Arithmetic.pair 0 n))
          (n - (i + 1)))) := by
  simp [formulaRequirement, evalArithmetic_courseEval]

theorem evalArithmetic_formulaRequirement_prev (allowFree : Bool) (n i : M) (hi : i < n) :
    listGet.evalArithmetic (Arithmetic.pair
      ((courseTable (formulaRequirementStep allowFree)).evalArithmetic (Arithmetic.pair 0 n))
      (n - (i + 1))) = (formulaRequirement allowFree).evalArithmetic i := by
  rw [evalArithmetic_courseTable_get (formulaRequirementStep allowFree) 0 n i hi]
  simp [formulaRequirement]

theorem evalArithmetic_formulaRequirement_tagged (allowFree : Bool) (t c : M) :
    (formulaRequirement allowFree).evalArithmetic (Arithmetic.pair t c + 1) =
      formulaRequirementValue allowFree t c (formulaRequirement allowFree).evalArithmetic := by
  have hc : c < Arithmetic.pair t c + 1 := lt_succ_iff_le.mpr (Arithmetic.le_pair_right t c)
  have hl : Arithmetic.pi₁ c < Arithmetic.pair t c + 1 := lt_of_le_of_lt (Arithmetic.pi₁_le_self c) hc
  have hr : Arithmetic.pi₂ c < Arithmetic.pair t c + 1 := lt_of_le_of_lt (Arithmetic.pi₂_le_self c) hc
  rw [evalArithmetic_formulaRequirement]
  simp [formulaRequirementValue, evalArithmetic_formulaRequirement_prev allowFree _ _ hc,
    evalArithmetic_formulaRequirement_prev allowFree _ _ hl, evalArithmetic_formulaRequirement_prev allowFree _ _ hr]

@[simp] theorem evalArithmetic_formulaRequirement_zero (allowFree : Bool) :
    (formulaRequirement allowFree).evalArithmetic (0 : M) = 0 := by
  simp [evalArithmetic_formulaRequirement]

@[simp] theorem evalArithmetic_formulaRequirement_rel (allowFree : Bool) (c : M) :
    (formulaRequirement allowFree).evalArithmetic (Arithmetic.pair 0 c + 1) =
      (atomicRequirement allowFree).evalArithmetic c := by
  simp [evalArithmetic_formulaRequirement_tagged, formulaRequirementValue]

@[simp] theorem evalArithmetic_formulaRequirement_nrel (allowFree : Bool) (c : M) :
    (formulaRequirement allowFree).evalArithmetic (Arithmetic.pair 1 c + 1) =
      (atomicRequirement allowFree).evalArithmetic c := by
  simp [evalArithmetic_formulaRequirement_tagged, formulaRequirementValue]

@[simp] theorem evalArithmetic_formulaRequirement_verum (allowFree : Bool) (c : M) :
    (formulaRequirement allowFree).evalArithmetic (Arithmetic.pair 2 c + 1) = 1 := by
  simp [evalArithmetic_formulaRequirement_tagged, formulaRequirementValue]

@[simp] theorem evalArithmetic_formulaRequirement_falsum (allowFree : Bool) (c : M) :
    (formulaRequirement allowFree).evalArithmetic (Arithmetic.pair 3 c + 1) = 1 := by
  simp [evalArithmetic_formulaRequirement_tagged, formulaRequirementValue]

@[simp] theorem evalArithmetic_formulaRequirement_and (allowFree : Bool) (a b : M) :
    (formulaRequirement allowFree).evalArithmetic (Arithmetic.pair 4 (Arithmetic.pair a b) + 1) =
      joinRequirements.evalArithmetic (Arithmetic.pair
        ((formulaRequirement allowFree).evalArithmetic a) ((formulaRequirement allowFree).evalArithmetic b)) := by
  simp [evalArithmetic_formulaRequirement_tagged, formulaRequirementValue]

@[simp] theorem evalArithmetic_formulaRequirement_or (allowFree : Bool) (a b : M) :
    (formulaRequirement allowFree).evalArithmetic (Arithmetic.pair 5 (Arithmetic.pair a b) + 1) =
      joinRequirements.evalArithmetic (Arithmetic.pair
        ((formulaRequirement allowFree).evalArithmetic a) ((formulaRequirement allowFree).evalArithmetic b)) := by
  simp [evalArithmetic_formulaRequirement_tagged, formulaRequirementValue]

@[simp] theorem evalArithmetic_formulaRequirement_all (allowFree : Bool) (a : M) :
    (formulaRequirement allowFree).evalArithmetic (Arithmetic.pair 6 a + 1) =
      quantifyRequirement.evalArithmetic ((formulaRequirement allowFree).evalArithmetic a) := by
  simp [evalArithmetic_formulaRequirement_tagged, formulaRequirementValue]

@[simp] theorem evalArithmetic_formulaRequirement_exs (allowFree : Bool) (a : M) :
    (formulaRequirement allowFree).evalArithmetic (Arithmetic.pair 7 a + 1) =
      quantifyRequirement.evalArithmetic ((formulaRequirement allowFree).evalArithmetic a) := by
  simp [evalArithmetic_formulaRequirement_tagged, formulaRequirementValue]
theorem joinRequirements_valid_iff (x y k : M) :
    (joinRequirements.evalArithmetic (Arithmetic.pair x y) ≠ 0 ∧
      joinRequirements.evalArithmetic (Arithmetic.pair x y) ≤ k) ↔
      (x ≠ 0 ∧ x ≤ k) ∧ (y ≠ 0 ∧ y ≤ k) := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  have hm : max x y ≠ 0 := by
    intro hm
    exact hx (le_antisymm (by simpa [hm] using le_max_left x y) (Arithmetic.zero_le x))
  simp [hx, hy, hm]

theorem quantifyRequirement_valid_iff (r n : M) :
    (quantifyRequirement.evalArithmetic r ≠ 0 ∧ quantifyRequirement.evalArithmetic r ≤ n + 1) ↔
      r ≠ 0 ∧ r ≤ (n + 1) + 1 := by
  rcases zero_or_succ r with (rfl | ⟨r, rfl⟩)
  · simp
  rcases zero_or_succ r with (rfl | ⟨r, rfl⟩)
  · simp
  · have hr : r + 1 + 1 ≠ 1 := by simp
    simp [hr]
end PrimitiveProgram
end ZFVP