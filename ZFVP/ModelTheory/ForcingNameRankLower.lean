import ZFVP.ModelTheory.ForcingModelRank
import ZFVP.ModelTheory.CountableZFTransfer
import ZFVP.ModelTheory.ForcingSemanticConsequence
import ZFVP.SetTheory.EndExtensionRank
import ZFVP.SetTheory.AtomicForcingDictionary

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

private def forcingNameRankLowerFormula : SetTheorySemisentence 6 :=
  f“P R o p t x. !forcingPreorderFormula P R → !forcingTopFormula P R o → p ∈ P →
    !forcingNameFormula P t → p ∈ !atomicEqualityFormula P R t (!checkNameFormula o x) →
    !rankFormula x ⊆ !rankFormula t”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem eval_forcingNameRankLowerFormula (v : Fin 6 → V) :
    forcingNameRankLowerFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) → v 3 ∈ v 0 →
        IsForcingName (v 0) (v 4) →
        v 3 ∈ atomicEquality (v 0) (v 1) (v 4) (checkName (v 2) (v 5)) →
        rank (v 5) ⊆ rank (v 4)) := by
  simp [forcingNameRankLowerFormula]

private theorem forcingName_rank_lower_countable [Countable V] {P R one p τ x : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hp : p ∈ P)
    (hτ : IsForcingName P τ) (he : p ∈ atomicEquality P R τ (checkName one x)) :
    rank x ⊆ rank τ := by
  obtain ⟨G, hG, hpG⟩ := exists_externalForcingGeneric hR hp
  let A : ForcingContext V := ⟨P, R, one, G, hR, ht, hG⟩
  have hv : A.ofName ⟨τ, hτ⟩ = A.check x :=
    Quotient.sound (s := forcingNameSetoid P R G hR hG.1) ⟨p, hpG, he⟩
  have hr := A.rank_ofName_subset ⟨τ, hτ⟩
  have hm : A.check (rank x) = rank (A.check x) := A.checkEmbedding.map_rank x
  rw [hv, ← hm] at hr
  intro β hβ
  exact (A.check_mem_iff β (rank τ)).mp (hr _ ((A.check_mem_iff β (rank x)).mpr hβ))

/-- A name forced equal to a checked ground set cannot have smaller set rank. -/
theorem forcingName_rank_lower_of_check {P R one p τ x : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hp : p ∈ P)
    (hτ : IsForcingName P τ) (he : p ∈ atomicEquality P R τ (checkName one x)) :
    rank x ⊆ rank τ := by
  have h := eval_of_countable_zf forcingNameRankLowerFormula (by
    intro W _ _ _ _ v
    exact (eval_forcingNameRankLowerFormula v).mpr
      (fun hR ht hp hτ he ↦ forcingName_rank_lower_countable hR ht hp hτ he))
    ![P, R, one, p, τ, x]
  exact (eval_forcingNameRankLowerFormula _).mp h hR ht hp hτ he

end ZFVP
