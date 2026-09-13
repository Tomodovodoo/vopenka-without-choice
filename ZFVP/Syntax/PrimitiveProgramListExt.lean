import ZFVP.Syntax.PrimitiveProgramListLength

/-! Extensionality of all internal natural-number list codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem listCode_cases (xs : M) : xs = 0 ∨ ∃ x ys, xs = Arithmetic.pair x ys + 1 := by
  rcases zero_or_succ xs with h | ⟨n, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨Arithmetic.pi₁ n, Arithmetic.pi₂ n, by rw [Arithmetic.pair_unpair]⟩

@[simp] theorem evalArithmetic_listLength_eq_zero (xs : M) :
    listLength.evalArithmetic xs = 0 ↔ xs = 0 := by
  have h := evalArithmetic_listDrop_eq_zero xs (0 : M)
  simpa only [evalArithmetic_listDrop_zero, le_zero_iff] using h.symm

theorem listCode_ext_of_length (n xs ys : M)
    (hx : listLength.evalArithmetic xs = n) (hy : listLength.evalArithmetic ys = n)
    (h : ∀ i < n, listGet.evalArithmetic (Arithmetic.pair xs i) = listGet.evalArithmetic (Arithmetic.pair ys i)) :
    xs = ys := by
  induction n using ISigma1.pi1_succ_induction generalizing xs ys
  · definability
  case zero =>
    have hx0 := (evalArithmetic_listLength_eq_zero xs).mp hx
    have hy0 := (evalArithmetic_listLength_eq_zero ys).mp hy
    exact hx0.trans hy0.symm
  case succ n ih =>
    rcases listCode_cases xs with rfl | ⟨x, xt, rfl⟩
    · simp at hx
    rcases listCode_cases ys with rfl | ⟨y, yt, rfl⟩
    · simp at hy
    have hxt : listLength.evalArithmetic xt = n := by simpa using hx
    have hyt : listLength.evalArithmetic yt = n := by simpa using hy
    have hhead : x = y := by simpa only [evalArithmetic_listGet_cons_zero] using h 0 (by simp)
    have htail : xt = yt := ih xt yt hxt hyt (fun i hi ↦ by
      simpa only [evalArithmetic_listGet_cons_succ] using h (i + 1) (by simpa only [add_comm] using add_lt_add_right hi 1))
    rw [hhead, htail]

theorem listCode_ext (xs ys : M) (hlen : listLength.evalArithmetic xs = listLength.evalArithmetic ys)
    (h : ∀ i < listLength.evalArithmetic xs,
      listGet.evalArithmetic (Arithmetic.pair xs i) = listGet.evalArithmetic (Arithmetic.pair ys i)) : xs = ys :=
  listCode_ext_of_length _ xs ys rfl hlen.symm h

end PrimitiveProgram
end ZFVP
