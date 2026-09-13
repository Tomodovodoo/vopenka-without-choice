import PalomarSolovayBridge.ArithmeticDictionary

namespace PalomarSolovayBridge
open PalomarBridge LO LO.FirstOrder LO.FirstOrder.SetTheory
open RealCode
variable {M : Type u} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "mem" => (fun x y : M => x ∈ y)
@[simp] theorem isReal_iff (x : M) : IsReal mem x ↔ ZFVP.IsDedekindCut x := by
  simp [IsReal, ZFVP.IsDedekindCut, isNonempty_def]
@[simp] theorem reals_eq : reals mem = ZFVP.dedekindReals M := by
  apply setValue_eq
  simp [ZFVP.mem_dedekindReals_iff]
@[simp] theorem realLT_iff (x y : M) : RealLT mem x y ↔ ZFVP.DedekindLT x y := Iff.rfl
@[simp] theorem interval_eq (a b : M) : interval mem a b = ZFVP.realInterval a b := by
  apply setValue_eq
  simp [ZFVP.mem_realInterval_iff]
@[simp] theorem basicCodes_eq : basicCodes mem = ZFVP.realBasicCodes M := by
  apply setValue_eq
  simp [ZFVP.mem_realBasicCodes_iff, mem_prod_iff]
@[simp] theorem openFrom_eq (S : M) : openFrom mem S = ZFVP.realOpenFrom S := by
  apply setValue_eq
  simp [ZFVP.mem_realOpenFrom_iff]
@[simp] theorem closedFrom_eq (S : M) : closedFrom mem S = ZFVP.realClosedFrom S := by
  simp [closedFrom, ZFVP.realClosedFrom]
@[simp] theorem open_iff (U : M) : Open mem U ↔ ZFVP.IsRealOpen U := by
  simp [Open, ZFVP.IsRealOpen]
@[simp] theorem length_eq (p : M) : RealCode.length mem p = ZFVP.realIntervalLength p := by
  simp [RealCode.length, ZFVP.realIntervalLength]
@[simp] theorem sumNext_eq (f p : M) : sumNext mem f p = ZFVP.rationalSumNext f p := by
  simp [sumNext, ZFVP.rationalSumNext]
@[simp] theorem partialSum_eq (f n : M) : partialSum mem f n = ZFVP.rationalPartialSum f n := by
  unfold partialSum
  rw [coding_second]
  have he : iterationStep mem (sumNext mem f) (Coding.pair mem (Coding.empty mem) (ratZero mem)) =
      ZFVP.naturalIterationStep (ZFVP.rationalSumNext f) ⟨0, ZFVP.rationalZero M⟩ₖ := by
    funext g
    have hf : sumNext mem f = ZFVP.rationalSumNext f := funext (sumNext_eq f)
    simp [hf, zero_def]
  rw [he, recValue_eq _ (ZFVP.naturalIterationStep_definable _ (by definability) _) n]
  rfl
@[simp] theorem lengths_eq (d : M) : lengths mem d = ZFVP.realCoverLengths d := by
  apply setValue_eq
  simp [ZFVP.realCoverLengths, ZFVP.mem_definableGraph_iff]
@[simp] theorem cost_eq (d n : M) : cost mem d n = ZFVP.realCoverCost d n := by
  simp [cost, ZFVP.realCoverCost]
@[simp] theorem intervalCover_iff (d A : M) : IntervalCover mem d A ↔ ZFVP.IsRealIntervalCover d A := by
  simp [IntervalCover, ZFVP.IsRealIntervalCover]
@[simp] theorem outerMeasure_eq (A : M) : outerMeasure mem A = ZFVP.realOuterMeasure A := by
  apply setValue_eq
  simp [ZFVP.mem_realOuterMeasure_iff]
@[simp] theorem extendedAdd_eq (u v : M) : extendedAdd mem u v = ZFVP.extendedRealAdd u v := by
  apply setValue_eq
  simp [ZFVP.mem_extendedRealAdd_iff]
@[simp] theorem lebesgueMeasurable_iff (A : M) : LebesgueMeasurable mem A ↔ ZFVP.IsRealLebesgueMeasurable A := by
  simp [LebesgueMeasurable, ZFVP.IsRealLebesgueMeasurable]
@[simp] theorem nowhereDense_iff (P : M) : NowhereDense mem P ↔ ZFVP.IsRealNowhereDense P := by
  simp [NowhereDense, ZFVP.IsRealNowhereDense]
@[simp] theorem meagre_iff (A : M) : Meagre mem A ↔ ZFVP.IsRealMeagre A := by
  simp [Meagre, ZFVP.IsRealMeagre]
@[simp] theorem baireProperty_iff (A : M) : BaireProperty mem A ↔ ZFVP.RealBaireProperty A := by
  simp [BaireProperty, ZFVP.RealBaireProperty]
@[simp] theorem perfect_iff (P : M) : Perfect mem P ↔ ZFVP.IsPerfectRealSet P := by
  simp [Perfect, ZFVP.IsPerfectRealSet, isNonempty_def]
@[simp] theorem injective_iff (f : M) : RealCode.Injective mem f ↔ SetTheory.Injective f := by
  simp [RealCode.Injective, SetTheory.Injective]
@[simp] theorem cardLE_iff (A B : M) : RealCode.CardLE mem A B ↔ SetTheory.CardLE A B := by
  simp [RealCode.CardLE, SetTheory.CardLE]
@[simp] theorem perfectSetProperty_iff (A : M) : PerfectSetProperty mem A ↔ ZFVP.RealPerfectSetProperty A := by
  simp [PerfectSetProperty, ZFVP.RealPerfectSetProperty, ZFVP.IsInternallyCountable]
end PalomarSolovayBridge
