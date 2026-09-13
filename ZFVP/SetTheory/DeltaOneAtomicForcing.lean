import ZFVP.SetTheory.BoundedAtomicMembership
import ZFVP.Syntax.SigmaOneBoundedModelTruth

/-! Atomic forcing and its complement have existential bounded certificates. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def atomicCertificateFormula (entry : SetTheorySemisentence 7) : SetTheorySemisentence 5 :=
  “P R σ τ p. ∃ T, ∃ H, !IsTransitive.dfn T ∧ σ ∈ T ∧ τ ∈ T ∧
    !boundedAtomicTruthTableFormula T P R H ∧ !entry T P R H σ τ p”

theorem atomicCertificateFormula_sigmaOne {entry : SetTheorySemisentence 7}
    (h : IsBoundedSetFormula entry) : IsSigmaFormula 1 (atomicCertificateFormula entry) :=
  .exs (.exs (.and (.bounded (isTransitiveFormula_bounded.subst _))
    (.and (.bounded (.rel _ _)) (.and (.bounded (.rel _ _))
      (.and (.bounded (boundedAtomicTruthTableFormula_bounded.subst _)) (.bounded (h.subst _)))))))

def boundedAtomicEqualityEntryFormula : SetTheorySemisentence 7 :=
  “T P R H σ τ p. p ∈ P ∧ !boundedTripleMemberFormula H σ τ p”

theorem boundedAtomicEqualityEntryFormula_bounded : IsBoundedSetFormula boundedAtomicEqualityEntryFormula :=
  .and (.rel _ _) (boundedTripleMemberFormula_bounded.subst _)

def sigmaOneAtomicEqualityFormula (answer : Bool) : SetTheorySemisentence 5 :=
  atomicCertificateFormula (if answer then boundedAtomicEqualityEntryFormula else ∼boundedAtomicEqualityEntryFormula)

def sigmaOneAtomicMembershipFormula (answer : Bool) : SetTheorySemisentence 5 :=
  atomicCertificateFormula (if answer then boundedAtomicMembershipFormula else ∼boundedAtomicMembershipFormula)

def piOneAtomicEqualityFormula : SetTheorySemisentence 5 := ∼sigmaOneAtomicEqualityFormula false

def piOneAtomicMembershipFormula : SetTheorySemisentence 5 := ∼sigmaOneAtomicMembershipFormula false

theorem sigmaOneAtomicEqualityFormula_sigmaOne (answer : Bool) :
    IsSigmaFormula 1 (sigmaOneAtomicEqualityFormula answer) := by
  cases answer
  · exact atomicCertificateFormula_sigmaOne boundedAtomicEqualityEntryFormula_bounded.neg
  · exact atomicCertificateFormula_sigmaOne boundedAtomicEqualityEntryFormula_bounded

theorem sigmaOneAtomicMembershipFormula_sigmaOne (answer : Bool) :
    IsSigmaFormula 1 (sigmaOneAtomicMembershipFormula answer) := by
  cases answer
  · exact atomicCertificateFormula_sigmaOne boundedAtomicMembershipFormula_bounded.neg
  · exact atomicCertificateFormula_sigmaOne boundedAtomicMembershipFormula_bounded

theorem piOneAtomicEqualityFormula_piOne : IsPiFormula 1 piOneAtomicEqualityFormula :=
  (sigmaOneAtomicEqualityFormula_sigmaOne false).neg

theorem piOneAtomicMembershipFormula_piOne : IsPiFormula 1 piOneAtomicMembershipFormula :=
  (sigmaOneAtomicMembershipFormula_sigmaOne false).neg

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_atomicCertificateFormula (entry : SetTheorySemisentence 7) (P R σ τ p : V) (Q : Prop)
    (he : ∀ T H : V, IsTransitive T → σ ∈ T → τ ∈ T → IsAtomicTruthTable P R T H →
      (entry.Evalb ![T, P, R, H, σ, τ, p] ↔ Q)) :
    (atomicCertificateFormula entry).Evalb ![P, R, σ, τ, p] ↔ Q := by
  have hev : (atomicCertificateFormula entry).Evalb ![P, R, σ, τ, p] ↔
      ∃ T H : V, IsTransitive T ∧ σ ∈ T ∧ τ ∈ T ∧
        boundedAtomicTruthTableFormula.Evalb ![T, P, R, H] ∧ entry.Evalb ![T, P, R, H, σ, τ, p] := by
    simp [atomicCertificateFormula, Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
      Function.comp_def]
  rw [hev]
  constructor
  · rintro ⟨T, H, hT, hσ, hτ, htable, hentry⟩
    let := hT
    exact (he T H hT hσ hτ ((eval_boundedAtomicTruthTableFormula P R H).mp htable)).mp hentry
  · intro hQ
    let T := transitiveClosure ({σ, τ} : V)
    have hT : IsTransitive T := transitiveClosure_transitive _
    let := hT
    have hσ : σ ∈ T := subset_transitiveClosure _ σ (by simp)
    have hτ : τ ∈ T := subset_transitiveClosure _ τ (by simp)
    obtain ⟨H, hH⟩ := atomicTruthTable_exists P R T (transitive_subnameClosed hT)
    exact ⟨T, H, hT, hσ, hτ, (eval_boundedAtomicTruthTableFormula P R H).mpr hH,
      (he T H hT hσ hτ hH).mpr hQ⟩

theorem eval_sigmaOneAtomicEqualityFormula (answer : Bool) (P R σ τ p : V) :
    (sigmaOneAtomicEqualityFormula answer).Evalb ![P, R, σ, τ, p] ↔
      TruthAnswer answer (p ∈ atomicEquality P R σ τ) := by
  apply eval_atomicCertificateFormula
  intro T H hT hσ hτ hH
  have he := hH.entry (transitive_subnameClosed hT) hσ hτ (p := p)
  cases answer <;> simp [boundedAtomicEqualityEntryFormula, TruthAnswer, he]
  tauto

theorem eval_sigmaOneAtomicMembershipFormula (answer : Bool) (P R σ τ p : V) :
    (sigmaOneAtomicMembershipFormula answer).Evalb ![P, R, σ, τ, p] ↔
      TruthAnswer answer (p ∈ atomicMembership P R σ τ) := by
  apply eval_atomicCertificateFormula
  intro T H hT hσ hτ hH
  let := hT
  have he := eval_boundedAtomicMembershipFormula hH hσ hτ p
  cases answer <;> simp [TruthAnswer, he]

theorem eval_piOneAtomicEqualityFormula (P R σ τ p : V) :
    piOneAtomicEqualityFormula.Evalb ![P, R, σ, τ, p] ↔ p ∈ atomicEquality P R σ τ := by
  simp [piOneAtomicEqualityFormula, eval_sigmaOneAtomicEqualityFormula, TruthAnswer]

theorem eval_piOneAtomicMembershipFormula (P R σ τ p : V) :
    piOneAtomicMembershipFormula.Evalb ![P, R, σ, τ, p] ↔ p ∈ atomicMembership P R σ τ := by
  simp [piOneAtomicMembershipFormula, eval_sigmaOneAtomicMembershipFormula, TruthAnswer]

instance sigmaOneAtomicEqualityFormula_defined (answer : Bool) :
    Defined (fun v : Fin 5 → V ↦ TruthAnswer answer (v 4 ∈ atomicEquality (v 0) (v 1) (v 2) (v 3))) (sigmaOneAtomicEqualityFormula answer) :=
  ⟨fun (v : Fin 5 → V) ↦ by
    have hv : ![v 0, v 1, v 2, v 3, v 4] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
        (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun z ↦ Fin.elim0 z) m) l) k) j) i
    change (sigmaOneAtomicEqualityFormula answer).Evalb v ↔ TruthAnswer answer (v 4 ∈ atomicEquality (v 0) (v 1) (v 2) (v 3))
    rw [← hv]
    exact eval_sigmaOneAtomicEqualityFormula answer (v 0) (v 1) (v 2) (v 3) (v 4)⟩

instance piOneAtomicEqualityFormula_defined :
    Defined (fun v : Fin 5 → V ↦ v 4 ∈ atomicEquality (v 0) (v 1) (v 2) (v 3)) piOneAtomicEqualityFormula :=
  ⟨fun (v : Fin 5 → V) ↦ by
    have hv : ![v 0, v 1, v 2, v 3, v 4] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
        (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun z ↦ Fin.elim0 z) m) l) k) j) i
    change piOneAtomicEqualityFormula.Evalb v ↔ v 4 ∈ atomicEquality (v 0) (v 1) (v 2) (v 3)
    rw [← hv]
    exact eval_piOneAtomicEqualityFormula (v 0) (v 1) (v 2) (v 3) (v 4)⟩

instance sigmaOneAtomicMembershipFormula_defined (answer : Bool) :
    Defined (fun v : Fin 5 → V ↦ TruthAnswer answer (v 4 ∈ atomicMembership (v 0) (v 1) (v 2) (v 3))) (sigmaOneAtomicMembershipFormula answer) :=
  ⟨fun (v : Fin 5 → V) ↦ by
    have hv : ![v 0, v 1, v 2, v 3, v 4] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
        (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun z ↦ Fin.elim0 z) m) l) k) j) i
    change (sigmaOneAtomicMembershipFormula answer).Evalb v ↔ TruthAnswer answer (v 4 ∈ atomicMembership (v 0) (v 1) (v 2) (v 3))
    rw [← hv]
    exact eval_sigmaOneAtomicMembershipFormula answer (v 0) (v 1) (v 2) (v 3) (v 4)⟩

instance piOneAtomicMembershipFormula_defined :
    Defined (fun v : Fin 5 → V ↦ v 4 ∈ atomicMembership (v 0) (v 1) (v 2) (v 3)) piOneAtomicMembershipFormula :=
  ⟨fun (v : Fin 5 → V) ↦ by
    have hv : ![v 0, v 1, v 2, v 3, v 4] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
        (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun z ↦ Fin.elim0 z) m) l) k) j) i
    change piOneAtomicMembershipFormula.Evalb v ↔ v 4 ∈ atomicMembership (v 0) (v 1) (v 2) (v 3)
    rw [← hv]
    exact eval_piOneAtomicMembershipFormula (v 0) (v 1) (v 2) (v 3) (v 4)⟩

end ZFVP
