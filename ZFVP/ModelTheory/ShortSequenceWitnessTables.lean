import ZFVP.ModelTheory.ForcingDependentChoiceSeriality
import ZFVP.ModelTheory.ReflectedPairWitnessTable

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- The input is a sequence shorter than the dependent-choice length. -/
def shortSequenceInputFormula : SetTheorySemisentence 3 :=
  f“κ A s. ∃ γ ∈ κ, s ∈ !function.dfn A γ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_shortSequenceInputFormula (v : Fin 3 → V) :
    shortSequenceInputFormula.Evalb v ↔ v 2 ∈ shorterSequences (v 0) (v 1) := by
  simp [shortSequenceInputFormula, mem_shorterSequences]

theorem shortSequence_candidate_countable [Countable V] {P R one κ p q t : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (A S : ForcingName P) (ht : IsNameSequence P t)
    (hp : p ∈ forcingFormula P R dependentChoiceSerialFormula
      (standardTuple ![checkName one κ, A.val, S.val]))
    (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R)
    (hinput : q ∈ forcingFormula P R shortSequenceInputFormula
      (standardTuple ![checkName one κ, A.val, sequenceName one t])) :
    ∃ r ∈ P, ∃ ν ∈ domain A.val, ⟨r, q⟩ₖ ∈ R ∧
      r ∈ forcingFormula P R dependentChoiceNextFormula
        (standardTuple ![sequenceName one t, ν, A.val, S.val]) := by
  obtain ⟨G, hG, hqG⟩ := exists_externalForcingGeneric hR hq
  let M : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  let c : ForcingName P := ⟨checkName one κ, checkName_isName htop.1 κ⟩
  let τ : ForcingName P := ⟨sequenceName one t, sequenceName_isName htop.1 ht⟩
  have hqpre := (forcingFormula_regular hR dependentChoiceSerialFormula _).2.1 p hp q hq hqp
  have hpre := (eval_dependentChoiceSerialFormula _).mp
    ((M.formula_truth dependentChoiceSerialFormula ![c, A, S]).mpr ⟨q, hqG, hqpre⟩)
  have htA := (eval_shortSequenceInputFormula _).mp
    ((M.formula_truth shortSequenceInputFormula ![c, A, τ]).mpr ⟨q, hqG, hinput⟩)
  obtain ⟨y, hy, hty⟩ := hpre.2 (M.ofName τ) htA
  obtain ⟨ν, u, _, hνu, rfl⟩ := (M.mem_ofName_iff A y).mp hy
  have he : dependentChoiceNextFormula.Evalb (fun i ↦ M.ofName (![τ, ν, A, S] i)) :=
    (eval_dependentChoiceNextFormula _).mpr ⟨hy, hty⟩
  obtain ⟨u, huG, hu⟩ := (M.formula_truth dependentChoiceNextFormula ![τ, ν, A, S]).mp he
  obtain ⟨r, hrG, hrq, hru⟩ := hG.1.2.2.2 q hqG u huG
  have hr := hG.1.1 r hrG
  exact ⟨r, hr, ν.val, mem_domain_of_kpair_mem hνu, hrq,
    (forcingFormula_regular hR dependentChoiceNextFormula _).2.1 u hu r hr hru⟩

private def shortWitnessForces {n : ℕ} (φ : SetTheorySemisentence n) (P R p b : V) : Prop :=
  p ∈ forcingFormula P R φ b

private instance forcingMembership_definable {n : ℕ} (φ : SetTheorySemisentence n) :
    ℒₛₑₜ-relation₄[V] (shortWitnessForces φ) := by
  exact Language.Definable.substitution
    (f := ![(fun v : Fin 4 → V ↦ v 0), (fun v ↦ v 1), (fun v ↦ v 0),
      (fun v ↦ v 0), (fun v ↦ v 2), (fun v ↦ v 3)])
    (ordinaryForcingTranslation_defined (V := V) φ).to_definable (by
      intro i
      exact Fin.cases (by definability) (fun j ↦ Fin.cases (by definability)
        (fun k ↦ Fin.cases (by definability) (fun l ↦ Fin.cases (by definability)
          (fun m ↦ Fin.cases (by definability) (fun n ↦ Fin.cases (by definability)
            (fun t ↦ Fin.elim0 t) n) m) l) k) j) i)

noncomputable def shortSequenceWitnessTable (P R one κ A S : V) : V :=
  {z ∈ (P ×ˢ shorterSequences κ (domain A)) ×ˢ (P ×ˢ domain A) ;
    ⟨kpair.π₁ (kpair.π₂ z), kpair.π₁ (kpair.π₁ z)⟩ₖ ∈ R ∧
      shortWitnessForces dependentChoiceNextFormula P R (kpair.π₁ (kpair.π₂ z))
        (standardTuple ![sequenceName one (kpair.π₂ (kpair.π₁ z)),
          kpair.π₂ (kpair.π₂ z), A, S])}

theorem mem_shortSequenceWitnessTable (P R one κ A S q t r ν : V) :
    ⟨⟨q, t⟩ₖ, ⟨r, ν⟩ₖ⟩ₖ ∈ shortSequenceWitnessTable P R one κ A S ↔
      q ∈ P ∧ t ∈ shorterSequences κ (domain A) ∧ r ∈ P ∧ ν ∈ domain A ∧
        ⟨r, q⟩ₖ ∈ R ∧ r ∈ forcingFormula P R dependentChoiceNextFormula
          (standardTuple ![sequenceName one t, ν, A, S]) := by
  simp [shortSequenceWitnessTable, shortWitnessForces, and_assoc]

theorem shortSequenceWitnessTable_fiber_countable [Countable V] {P R one κ p q t : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (A S : ForcingName P)
    (hp : p ∈ forcingFormula P R dependentChoiceSerialFormula
      (standardTuple ![checkName one κ, A.val, S.val]))
    (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R) (ht : t ∈ shorterSequences κ (domain A.val))
    (hinput : q ∈ forcingFormula P R shortSequenceInputFormula
      (standardTuple ![checkName one κ, A.val, sequenceName one t])) :
    ∃ r ν : V, ⟨⟨q, t⟩ₖ, ⟨r, ν⟩ₖ⟩ₖ ∈ shortSequenceWitnessTable P R one κ A.val S.val := by
  obtain ⟨γ, _, htγ⟩ := (mem_shorterSequences _ _ _).mp ht
  have htN : IsNameSequence P t := by
    intro i hi
    have hv := function_value_mem htγ ((domain_eq_of_mem_function htγ) ▸ hi)
    obtain ⟨u, hu⟩ := mem_domain_iff.mp hv
    exact forcingName_subname A.property hu
  obtain ⟨r, hr, ν, hν, hrq, hf⟩ :=
    shortSequence_candidate_countable hR htop A S htN hp hq hqp hinput
  exact ⟨r, ν, (mem_shortSequenceWitnessTable _ _ _ _ _ _ _ _ _ _).mpr
    ⟨hq, ht, hr, hν, hrq, hf⟩⟩

namespace IsElementaryInclusion
variable {X B P R one κ p : V} [IsTransitive B] [Countable V]

theorem short_sequence_witness_dense (h : IsElementaryInclusion X B)
    (hP : P ⊆ X) (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (A S : ForcingName P) (hT : shortSequenceWitnessTable P R one κ A.val S.val ∈ X)
    (hpairs : ∀ q ∈ P, ∀ t ∈ shorterSequences κ (domain A.val), ⟨q, t⟩ₖ ∈ B)
    (hp : p ∈ forcingFormula P R dependentChoiceSerialFormula
      (standardTuple ![checkName one κ, A.val, S.val])) :
    ∀ t ∈ X ∩ shorterSequences κ (domain A.val), ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R →
      q ∈ forcingFormula P R shortSequenceInputFormula
        (standardTuple ![checkName one κ, A.val, sequenceName one t]) →
      ∃ r ∈ P, ∃ ν ∈ X ∩ domain A.val, ⟨r, q⟩ₖ ∈ R ∧
        r ∈ forcingFormula P R dependentChoiceNextFormula
          (standardTuple ![sequenceName one t, ν, A.val, S.val]) := by
  intro t ht q hq hqp hfτ
  obtain ⟨htX, htd⟩ := mem_inter_iff.mp ht
  have hinput : ⟨q, t⟩ₖ ∈ X := h.kpair_mem (hP q hq) htX (hpairs q hq t htd)
  obtain ⟨r, _, ν, hνX, hmem⟩ := h.table_pair_fiber_witness hT hinput
    (shortSequenceWitnessTable_fiber_countable hR htop A S hp hq hqp htd hfτ)
  obtain ⟨_, _, hr, hνd, hrq, hf⟩ := (mem_shortSequenceWitnessTable _ _ _ _ _ _ _ _ _ _).mp hmem
  exact ⟨r, hr, ν, mem_inter_iff.mpr ⟨hνX, hνd⟩, hrq, hf⟩

end IsElementaryInclusion
end ZFVP
