import PalomarSolovayBridge.RegularityDictionary
import PalomarDCBridge.Dictionary
import ZFVP.ModelTheory.RealSolovayConsistency

namespace PalomarSolovayBridge
open PalomarBridge LO LO.FirstOrder LO.FirstOrder.SetTheory
open RealCode
variable {M : Type u} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "mem" => (fun x y : M => x ∈ y)
@[simp] theorem isOmegaOne_iff (k : M) : IsOmegaOne mem k ↔ ZFVP.IsHartogsNumber (ω : M) k := by
  simp [IsOmegaOne, ZFVP.IsHartogsNumber, ZFVP.IsLeastOrdinal]
@[simp] theorem omegaOne_eq : omegaOne mem = ZFVP.hartogsNumber (ω : M) := by
  symm
  apply (ZFVP.hartogsNumber_eq_iff _ _).mpr
  have he : ∃ k, IsOmegaOne mem k := ⟨ZFVP.hartogsNumber (ω : M),
    (isOmegaOne_iff _).mpr (ZFVP.hartogsNumber_spec _)⟩
  exact (isOmegaOne_iff _).mp (Classical.epsilon_spec he)
@[simp] theorem indexedIntersection_eq (K I g : M) :
    RealCode.indexedIntersection mem K I g = ZFVP.indexedIntersection K I g := by
  apply setValue_eq
  simp [ZFVP.mem_indexedIntersection_iff]
@[simp] theorem ultrafilter_iff (K U : M) : RealCode.Ultrafilter mem K U ↔ ZFVP.IsSetUltrafilter K U := by
  have he (X : M) : difference mem K X = ZFVP.relativeComplement K X := by
    apply setValue_eq
    simp
  simp [RealCode.Ultrafilter, ZFVP.IsSetUltrafilter, he]
@[simp] theorem omegaOneMeasure_iff : OmegaOneMeasure mem ↔
    ∃ U : M, ZFVP.IsNonprincipalSetUltrafilter (ZFVP.hartogsNumber (ω : M)) U ∧
      ZFVP.IsOrdinalComplete (ZFVP.hartogsNumber (ω : M)) U := by
  simp [OmegaOneMeasure, ZFVP.IsNonprincipalSetUltrafilter, ZFVP.IsOrdinalComplete, and_assoc]

theorem allLM_iff : (∀ A : M, RealCode.Subset mem A (reals mem) → LebesgueMeasurable mem A) ↔
    ZFVP.AllRealLebesgueMeasurable M := by simp [ZFVP.AllRealLebesgueMeasurable]
theorem allBP_iff : (∀ A : M, RealCode.Subset mem A (reals mem) → BaireProperty mem A) ↔
    ZFVP.AllRealBaireProperty M := by simp [ZFVP.AllRealBaireProperty]
theorem allPSP_iff : (∀ A : M, RealCode.Subset mem A (reals mem) → PerfectSetProperty mem A) ↔
    ZFVP.AllRealPerfectSetProperty M := by simp [ZFVP.AllRealPerfectSetProperty]
end PalomarSolovayBridge

