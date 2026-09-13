import ZFVP.ModelTheory.GeneratedZFVPModels

/-! Every external ZF+VP proof is represented by a checked finite internal proof. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem zfVPTheory_provable_standardCoded {φ : SetTheorySentence} (hφ : zfVPTheory ⊢ φ) :
    StandardCodedProvable (zfVPOpenAxiomCodes : V) 0 {encodeMembershipFormula φ} :=
  generatedZFVPTheory_provable_coded (Entailment.WeakerThan.pbl hφ)

theorem zfVPTheory_provable_internal {φ : SetTheorySentence} (hφ : zfVPTheory ⊢ φ) :
    ∃ p, IsOpenCodedSequentProof (zfVPOpenAxiomCodes : V) p 0 {encodeMembershipFormula φ} :=
  (zfVPTheory_provable_standardCoded hφ).to_internal

theorem zfVPTheory_inconsistent_internal_refutation (h : Entailment.Inconsistent zfVPTheory) :
    ∃ p, IsOpenCodedSequentProof (zfVPOpenAxiomCodes : V) p 0 ∅ := by
  apply coded_refutation_of_foundation_inconsistent h
    (fun _ hφ ↦ zfVPTheory_provable_standardCoded (Entailment.by_axm hφ))
  exact fixedZFTheory_coded (φ := Axiom.empty) (by simp [fixedZFTheory])

theorem OpenCodedSequentConsistent.zfVP_consistent
    (h : OpenCodedSequentConsistent (zfVPOpenAxiomCodes : V)) : Entailment.Consistent zfVPTheory := by
  apply Entailment.not_inconsistent_iff_consistent.mp
  exact fun hi ↦ h (zfVPTheory_inconsistent_internal_refutation (V := V) hi)

end ZFVP
