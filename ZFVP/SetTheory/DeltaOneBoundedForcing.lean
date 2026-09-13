import ZFVP.Syntax.SigmaOneBoundedForcing
import ZFVP.SetTheory.FormulaForcing
import ZFVP.SetTheory.SymmetricFormulaForcing

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem BoundedFormulaTree.forcingCertificate_ordinary_meaning {P R : V} (hR : IsForcingPreorder P R)
    {n : ℕ} (φ : BoundedFormulaTree n) (v : Fin n → V) (hv : ∀ i, IsForcingName P (v i))
    (answer : Bool) (p : V) :
    (φ.forcingCertificate answer).Evalb (P :> R :> p :> v) ↔
      TruthAnswer answer (p ∈ forcingFormula P R φ.formula (standardTuple v)) :=
  φ.forcingCertificate_meaning hR (IsForcingName P) (by definability) (fun _ h ↦ h)
    (fun _ h _ _ hus ↦ forcingName_subname h hus) v hv answer p

theorem BoundedFormulaTree.forcingPi_ordinary_meaning {P R : V} (hR : IsForcingPreorder P R)
    {n : ℕ} (φ : BoundedFormulaTree n) (v : Fin n → V) (hv : ∀ i, IsForcingName P (v i)) (p : V) :
    φ.forcingPi.Evalb (P :> R :> p :> v) ↔ p ∈ forcingFormula P R φ.formula (standardTuple v) :=
  φ.forcingPi_meaning hR (IsForcingName P) (by definability) (fun _ h ↦ h)
    (fun _ h _ _ hus ↦ forcingName_subname h hus) v hv p

theorem BoundedFormulaTree.forcingCertificate_symmetric_meaning {P R : V} (hR : IsForcingPreorder P R)
    (Γ F : V) {n : ℕ} (φ : BoundedFormulaTree n) (v : Fin n → V)
    (hv : ∀ i, IsHereditarilySymmetricName P Γ F (v i)) (answer : Bool) (p : V) :
    (φ.forcingCertificate answer).Evalb (P :> R :> p :> v) ↔
      TruthAnswer answer (p ∈ symmetricForcingFormula P R Γ F φ.formula (standardTuple v)) :=
  φ.forcingCertificate_meaning hR (IsHereditarilySymmetricName P Γ F) (by definability) (fun _ h ↦ h.1)
    (fun _ h _ _ hus ↦ hereditarilySymmetric_mem_closure h (subname_mem_nameClosure hus)) v hv answer p

theorem BoundedFormulaTree.forcingPi_symmetric_meaning {P R : V} (hR : IsForcingPreorder P R)
    (Γ F : V) {n : ℕ} (φ : BoundedFormulaTree n) (v : Fin n → V)
    (hv : ∀ i, IsHereditarilySymmetricName P Γ F (v i)) (p : V) :
    φ.forcingPi.Evalb (P :> R :> p :> v) ↔ p ∈ symmetricForcingFormula P R Γ F φ.formula (standardTuple v) :=
  φ.forcingPi_meaning hR (IsHereditarilySymmetricName P Γ F) (by definability) (fun _ h ↦ h.1)
    (fun _ h _ _ hus ↦ hereditarilySymmetric_mem_closure h (subname_mem_nameClosure hus)) v hv p

theorem symmetricForcingFormula_bounded_eq_ordinary {P R : V} (hR : IsForcingPreorder P R)
    (Γ F : V) {n : ℕ} {φ : SetTheorySemisentence n} (hφ : IsBoundedSetFormula φ)
    (v : Fin n → V) (hv : ∀ i, IsHereditarilySymmetricName P Γ F (v i)) :
    symmetricForcingFormula P R Γ F φ (standardTuple v) = forcingFormula P R φ (standardTuple v) := by
  obtain ⟨t, rfl⟩ := boundedFormulaTree_exists hφ
  apply mem_ext
  intro p
  exact (t.forcingCertificate_symmetric_meaning hR Γ F v hv true p).symm.trans
    (t.forcingCertificate_ordinary_meaning hR v (fun i ↦ (hv i).1) true p)

end ZFVP
