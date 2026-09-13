import ZFVP.ModelTheory.SymmetricModel
import ZFVP.ModelTheory.SVCVopenkaRestoration
import ZFVP.ModelTheory.CountableCohenVopenkaConsistency
import ZFVP.ModelTheory.RealSolovayTheory

/-!
# Statements compared against the implemented proofs

These are the main results in the development's existing internal-set-theory
encoding. The deliberate holes occur only in this statement file.

This Challenge currently imports Foundation and project definitions. It is
usable with Comparator, but does not yet meet Palomar's stricter Challenge
import policy. See docs/palomar.md for the required statement translation.
-/

namespace VopenkaWithoutChoice
open ZFVP LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment

/-- Theorem A: each instance of arbitrary-language VP holds in the symmetric
extension of a ZF model satisfying every VP instance. The symmetric context
includes the poset, normal filter, automorphism group and supplied generic. -/
theorem symmetric_preservation {V : Type*} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (S : SymmetricContext V)
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    (φ : SetTheorySemisentence 2) : VopenkaInstance (V := S.Model) φ := by
  sorry

/-- Theorem B: syntactic consistency of ZFC+VP is equivalent to that of ZF+VP.
The theories contain the arbitrary-set-language VP scheme. -/
theorem equiconsistency : Consistent zfcVPTheory ↔ Consistent zfVPTheory := by
  sorry

/-- The consistency consequence with dependent choice and failure of choice,
starting with Con(ZF+VP). -/
theorem dependent_choice (h : Consistent zfVPTheory) :
    Consistent zfVPDCNotChoiceTheory := by
  sorry

/-- The ordinary-real Solovay consistency consequence. The target theory includes
VP, DC, failure of AC, Lebesgue measurability, the Baire property and the perfect
set property for all internal sets of Dedekind reals. Its full definition also
records the ultrafilter conclusion used in the paper. -/
theorem solovay_reals (h : Consistent zfVPTheory) :
    Consistent realSolovayTheory := by
  sorry

end VopenkaWithoutChoice
