import ZFVP.ModelTheory.SymmetricVopenkaPreservation
import ZFVP.ModelTheory.WoodinSparseRestorationTheorem
import ZFVP.ModelTheory.CountableCohenVopenkaConsistency
import ZFVP.ModelTheory.RealSolovayConsistency

/-! Implementations of the exact declarations in Challenge.lean.
Challenge is deliberately not imported: both modules declare the same names
in separate environments, as required by Comparator. -/

namespace VopenkaWithoutChoice
open ZFVP LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment

theorem symmetric_preservation {V : Type*} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (S : SymmetricContext V)
    (hVP : ∀ ψ : SetTheorySemisentence 2, VopenkaInstance (V := V) ψ)
    (φ : SetTheorySemisentence 2) : VopenkaInstance (V := S.Model) φ :=
  S.vopenkaInstance hVP φ

theorem equiconsistency : Consistent zfcVPTheory ↔ Consistent zfVPTheory :=
  consistent_zfcVP_iff_consistent_zfVP_woodin

theorem dependent_choice (h : Consistent zfVPTheory) :
    Consistent zfVPDCNotChoiceTheory :=
  consistent_zfVP_DC_notChoice (consistent_zfcVP_of_consistent_zfVP_woodin h)

theorem solovay_reals (h : Consistent zfVPTheory) :
    Consistent realSolovayTheory :=
  consistent_realSolovay_of_consistent_zfVP h

end VopenkaWithoutChoice
