import PalomarSolovayBridge.Vocabulary
import PalomarBridge.CodingOperations
import ZFVP.SetTheory.RealCaratheodory
import ZFVP.SetTheory.RealRegularitySentences

namespace PalomarSolovayBridge
open PalomarBridge LO LO.FirstOrder LO.FirstOrder.SetTheory
open RealCode
variable {M : Type u} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "mem" => (fun x y : M => x ∈ y)
@[simp] theorem subset_iff (A B : M) : Subset mem A B ↔ A ⊆ B := Iff.rfl
@[simp] theorem power_eq (A : M) : RealCode.power mem A = ℘ A := by
  apply setValue_eq; intro x; rw [mem_power_iff]; rfl
@[simp] theorem intersect_eq (A B : M) : intersect mem A B = A ∩ B := by
  apply setValue_eq; simp
@[simp] theorem difference_eq (A B : M) : difference mem A B = A \ B := by
  apply setValue_eq; simp
@[simp] theorem binaryUnion_eq (A B : M) : binaryUnion mem A B = A ∪ B := by
  apply setValue_eq; simp
@[simp] theorem ordinal_iff (a : M) : Ordinal mem a ↔ IsOrdinal a := by
  constructor
  · intro h
    exact { transitive := fun x hx y hy => h.1 x hx y hy, trichotomy := h.2 }
  · intro h
    exact ⟨fun x hx y hy => h.transitive x hx y hy, h.trichotomy⟩
@[simp] theorem attempt_iff (F : M → M) (a f : M) : Attempt mem F a f ↔ IsAttempt F a f := by
  simp [Attempt, IsAttempt, eq_comm]
theorem recValue_eq (F : M → M) (hF : ℒₛₑₜ-function₁ F) (a : M) :
    recValue mem F a = Replacement.transfiniteRec F hF a := by
  apply (ZFVP.transfiniteRec_eq_iff F hF a _).mpr
  have hex : ∃ y, (∃ f, Attempt mem F a f ∧ y = F f) ∨ (¬Ordinal mem a ∧ y = Coding.empty mem) := by
    refine ⟨Replacement.transfiniteRec F hF a, ?_⟩
    simpa using (ZFVP.transfiniteRec_eq_iff F hF a _).mp rfl
  simpa only [recValue, attempt_iff, ordinal_iff, coding_empty] using Classical.epsilon_spec hex
@[simp] theorem addStep_eq (a f : M) : addStep mem a f = ZFVP.ordinalAddStep a f := by
  apply setValue_eq
  simp [ZFVP.ordinalAddStep, mem_sUnion_iff, repl_spec]
@[simp] theorem natAdd_eq (a b : M) : natAdd mem a b = ZFVP.ordinalAdd a b := by
  unfold natAdd
  have he : addStep mem a = ZFVP.ordinalAddStep a := funext (addStep_eq a)
  rw [he]
  exact recValue_eq _ _ b
@[simp] theorem iterationStep_eq (F : M → M) (z g : M) :
    iterationStep mem F z g = ZFVP.naturalIterationStep F z g := by
  unfold iterationStep ZFVP.naturalIterationStep
  rw [coding_domain, coding_empty, coding_union, coding_value]
  rfl
@[simp] theorem natMul_eq (a b : M) : natMul mem a b = ZFVP.naturalMul a b := by
  unfold natMul
  have he : iterationStep mem (fun x => natAdd mem x a) (Coding.empty mem) =
      ZFVP.naturalIterationStep (fun x => ZFVP.ordinalAdd x a) 0 := by
    funext g
    simp [zero_def]
  rw [he]
  exact recValue_eq _ _ b
@[simp] theorem fractionCodes_eq : fractionCodes mem = ZFVP.rationalCodeSpace M := by
  apply setValue_eq
  simp [ZFVP.mem_rationalCodeSpace_iff, zero_def]
@[simp] theorem fractionEquiv_iff (c e : M) : FractionEquiv mem c e ↔ ZFVP.RationalCodeEquiv c e := by
  simp [FractionEquiv, balance, oppositeBalance, ZFVP.RationalCodeEquiv]
@[simp] theorem fractionClass_eq (c : M) : fractionClass mem c = ZFVP.rationalClass c := by
  apply setValue_eq
  simp [ZFVP.mem_rationalClass_iff]
@[simp] theorem rationals_eq : rationals mem = ZFVP.internalRationals M := by
  apply setValue_eq
  simp [ZFVP.internalRationals, repl_spec, eq_comm]
@[simp] theorem ratLT_iff (q r : M) : RatLT mem q r ↔ ZFVP.InternalRationalLT q r := by
  simp [RatLT, balance, oppositeBalance, ZFVP.InternalRationalLT, ZFVP.RationalCodeLT]
@[simp] theorem fractionAdd_eq (c e : M) : fractionAdd mem c e = ZFVP.rationalCodeAdd c e := by
  simp [fractionAdd, ZFVP.rationalCodeAdd]
@[simp] theorem fractionNeg_eq (c : M) : fractionNeg mem c = ZFVP.rationalCodeNeg c := by
  simp [fractionNeg, ZFVP.rationalCodeNeg]
@[simp] theorem ratAdd_eq (q r : M) : ratAdd mem q r = ZFVP.rationalAdd q r := by
  apply setValue_eq
  simp [ZFVP.rationalAdd]
@[simp] theorem ratNeg_eq (q : M) : ratNeg mem q = ZFVP.rationalNeg q := by
  apply setValue_eq
  simp [ZFVP.rationalNeg]
@[simp] theorem ratZero_eq : ratZero mem = ZFVP.rationalZero M := by
  simp [ratZero, ZFVP.rationalZero, zero_def]
@[simp] theorem ratCut_eq (q : M) : ratCut mem q = ZFVP.rationalCut q := by
  apply setValue_eq
  simp [ZFVP.rationalCut]
end PalomarSolovayBridge

