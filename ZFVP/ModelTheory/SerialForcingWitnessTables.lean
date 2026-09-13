import ZFVP.ModelTheory.SerialForcingCandidates

/-! Set-sized tables of initial and successor forcing witnesses. These tables
can be parameters of a small elementary hull; their definitions do not choose
one witness from each fiber. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private def serialWitnessForces {n : ℕ} (φ : SetTheorySemisentence n) (P R p b : V) : Prop :=
  p ∈ forcingFormula P R φ b

private instance forcingMembership_definable {n : ℕ} (φ : SetTheorySemisentence n) :
    ℒₛₑₜ-relation₄[V] (serialWitnessForces φ) := by
  exact Language.Definable.substitution
    (f := ![(fun v : Fin 4 → V ↦ v 0), (fun v ↦ v 1), (fun v ↦ v 0),
      (fun v ↦ v 0), (fun v ↦ v 2), (fun v ↦ v 3)])
    (ordinaryForcingTranslation_defined (V := V) φ).to_definable (by
      intro i
      exact Fin.cases (by definability) (fun j ↦ Fin.cases (by definability)
        (fun k ↦ Fin.cases (by definability) (fun l ↦ Fin.cases (by definability)
          (fun m ↦ Fin.cases (by definability) (fun n ↦ Fin.cases (by definability)
            (fun t ↦ Fin.elim0 t) n) m) l) k) j) i)

noncomputable def serialInitialWitnessTable (P R A : V) : V :=
  {z ∈ P ×ˢ (P ×ˢ domain A) ;
    ⟨kpair.π₁ (kpair.π₂ z), kpair.π₁ z⟩ₖ ∈ R ∧
      serialWitnessForces serialHullInitialFormula P R (kpair.π₁ (kpair.π₂ z))
        (standardTuple ![A, kpair.π₂ (kpair.π₂ z)])}

noncomputable def serialNextWitnessTable (P R A S : V) : V :=
  {z ∈ (P ×ˢ domain A) ×ˢ (P ×ˢ domain A) ;
    ⟨kpair.π₁ (kpair.π₂ z), kpair.π₁ (kpair.π₁ z)⟩ₖ ∈ R ∧
      serialWitnessForces serialHullNextFormula P R (kpair.π₁ (kpair.π₂ z))
        (standardTuple ![A, S, kpair.π₂ (kpair.π₁ z), kpair.π₂ (kpair.π₂ z)])}

instance serialInitialWitnessTable_definable : ℒₛₑₜ-function₃[V] serialInitialWitnessTable := by
  have h : ℒₛₑₜ-relation₄ (fun T P R A : V ↦ ∀ z, z ∈ T ↔
      z ∈ P ×ˢ (P ×ˢ domain A) ∧
        ⟨kpair.π₁ (kpair.π₂ z), kpair.π₁ z⟩ₖ ∈ R ∧
          serialWitnessForces serialHullInitialFormula P R (kpair.π₁ (kpair.π₂ z))
            (standardTuple ![A, kpair.π₂ (kpair.π₂ z)])) := by
    simp only [standardTuple]
    apply Language.Definable.all
    apply Language.Definable.biconditional (by definability)
    apply Language.Definable.and (by definability)
    apply Language.Definable.and (by definability)
    exact Language.DefinableRel₄.comp (P := serialWitnessForces serialHullInitialFormula)
      (by definability) (by definability) (by definability) (by definability)
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [serialInitialWitnessTable, mem_sep_iff]
  rfl

instance serialNextWitnessTable_definable : ℒₛₑₜ-function₄[V] serialNextWitnessTable := by
  have h : ℒₛₑₜ-relation₅ (fun T P R A S : V ↦ ∀ z, z ∈ T ↔
      z ∈ (P ×ˢ domain A) ×ˢ (P ×ˢ domain A) ∧
        ⟨kpair.π₁ (kpair.π₂ z), kpair.π₁ (kpair.π₁ z)⟩ₖ ∈ R ∧
          serialWitnessForces serialHullNextFormula P R (kpair.π₁ (kpair.π₂ z))
            (standardTuple ![A, S, kpair.π₂ (kpair.π₁ z), kpair.π₂ (kpair.π₂ z)])) := by
    simp only [standardTuple]
    apply Language.Definable.all
    apply Language.Definable.biconditional (by definability)
    apply Language.Definable.and (by definability)
    apply Language.Definable.and (by definability)
    exact Language.DefinableRel₄.comp (P := serialWitnessForces serialHullNextFormula)
      (by definability) (by definability) (by definability) (by definability)
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [serialNextWitnessTable, mem_sep_iff]
  rfl

theorem mem_serialInitialWitnessTable (P R A q r ν : V) :
    ⟨q, ⟨r, ν⟩ₖ⟩ₖ ∈ serialInitialWitnessTable P R A ↔
      q ∈ P ∧ r ∈ P ∧ ν ∈ domain A ∧ ⟨r, q⟩ₖ ∈ R ∧
        r ∈ forcingFormula P R serialHullInitialFormula (standardTuple ![A, ν]) := by
  simp [serialInitialWitnessTable, serialWitnessForces, and_assoc]

theorem mem_serialNextWitnessTable (P R A S q τ r ν : V) :
    ⟨⟨q, τ⟩ₖ, ⟨r, ν⟩ₖ⟩ₖ ∈ serialNextWitnessTable P R A S ↔
      q ∈ P ∧ τ ∈ domain A ∧ r ∈ P ∧ ν ∈ domain A ∧ ⟨r, q⟩ₖ ∈ R ∧
        r ∈ forcingFormula P R serialHullNextFormula (standardTuple ![A, S, τ, ν]) := by
  simp [serialNextWitnessTable, serialWitnessForces, and_assoc]

theorem serialInitialWitnessTable_fiber_countable [Countable V] {P R one p q : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (A S : ForcingName P)
    (hp : p ∈ forcingFormula P R serialHullPremiseFormula (standardTuple ![A.val, S.val]))
    (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R) :
    ∃ r ν : V, ⟨q, ⟨r, ν⟩ₖ⟩ₖ ∈ serialInitialWitnessTable P R A.val := by
  obtain ⟨r, hr, ν, hν, _, hrq, hf⟩ :=
    serialHull_initial_candidate_countable hR htop A S hp hq hqp
  exact ⟨r, ν, (mem_serialInitialWitnessTable _ _ _ _ _ _).mpr ⟨hq, hr, hν, hrq, hf⟩⟩

theorem serialNextWitnessTable_fiber_countable [Countable V] {P R one p q τ : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (A S : ForcingName P)
    (hp : p ∈ forcingFormula P R serialHullPremiseFormula (standardTuple ![A.val, S.val]))
    (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R) (hτd : τ ∈ domain A.val)
    (hτ : q ∈ forcingFormula P R serialHullInitialFormula (standardTuple ![A.val, τ])) :
    ∃ r ν : V, ⟨⟨q, τ⟩ₖ, ⟨r, ν⟩ₖ⟩ₖ ∈ serialNextWitnessTable P R A.val S.val := by
  have hτN : IsForcingName P τ := by
    obtain ⟨t, hτt⟩ := mem_domain_iff.mp hτd
    exact forcingName_subname A.property hτt
  obtain ⟨r, hr, ν, hν, _, hrq, hf⟩ :=
    serialHull_next_candidate_countable hR htop A S ⟨τ, hτN⟩ hp hq hqp hτ
  exact ⟨r, ν, (mem_serialNextWitnessTable _ _ _ _ _ _ _ _).mpr ⟨hq, hτd, hr, hν, hrq, hf⟩⟩

end ZFVP
