import ZFVP.SetTheory.CorrectDomainReflection

/-! Correct partial truth at every positive standard Levy level. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem correctDomain_reflectingMembership (k : ℕ) {n : ℕ} (φ : SetTheorySemisentence n)
    (b : Fin n → V) (X : V) :
    ∃ A : V, CorrectDomain k A ∧ X ∈ A ∧ standardTuple b ∈ A ^ (n : V) ∧
      (MembershipSatisfies A (n : V) (encodeMembershipFormula φ) (standardTuple b) ↔ φ.Evalb b) := by
  obtain ⟨δ, hδ, hp, _, _, hD, href⟩ := correctDomain_formula_reflection k φ ⟨X, range (standardTuple b)⟩ₖ
  let := hδ
  let := hD.support
  obtain ⟨hX, hr⟩ := kpair_components_mem_transitive hp
  have hb : ∀ i, b i ∈ hierarchy δ := fun i ↦ hD.support.mem_trans
    (mem_range_of_kpair_mem ((mem_standardTuple_iff b _).mpr ⟨i, rfl⟩)) hr
  let c : Fin n → SetDomain (hierarchy δ) := fun i ↦ ⟨b i, hb i⟩
  exact ⟨hierarchy δ, hD, hX, standardTuple_mem_function b hb,
    (membershipSatisfies_encode hD.nonempty φ c).trans (href c)⟩

theorem domainSigmaTruth_correct (k : ℕ) {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsSigmaFormula (k + 1) φ) (b : Fin n → V) :
    DomainSigmaTruth k (n : V) (encodeMembershipFormula φ) (standardTuple b) ↔ φ.Evalb b := by
  constructor
  · rintro ⟨A, hA, hbA, hsA⟩
    obtain ⟨B, hB, hAB, _, href⟩ := correctDomain_reflectingMembership k φ b A
    exact href.mp (correctDomainCode_upward k hφ.encode A B hA hB (hB.support.transitive A hAB) _ hbA hsA)
  · intro h
    obtain ⟨A, hA, _, hb, href⟩ := correctDomain_reflectingMembership k φ b (∅ : V)
    exact ⟨A, hA, hb, href.mpr h⟩

theorem domainPiTruth_correct (k : ℕ) {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsPiFormula (k + 1) φ) (b : Fin n → V) :
    DomainPiTruth k (n : V) (encodeMembershipFormula φ) (standardTuple b) ↔ φ.Evalb b := by
  constructor
  · intro h
    obtain ⟨A, hA, _, hb, href⟩ := correctDomain_reflectingMembership k φ b (∅ : V)
    exact href.mp (h A hA hb)
  · intro h A hA hbA
    obtain ⟨B, hB, hAB, _, href⟩ := correctDomain_reflectingMembership k φ b A
    exact correctDomainCode_downward k hφ.encode hA hB (hB.support.transitive A hAB) hbA (href.mpr h)

theorem domainSigmaTruthFormula_correct (k : ℕ) {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsSigmaFormula (k + 1) φ) (b : Fin n → V) :
    (domainSigmaTruthFormula (correctDomainFormula k)).Evalb
      ![(n : V), encodeMembershipFormula φ, standardTuple b] ↔ φ.Evalb b :=
  (eval_domainSigmaTruthFormula k _ _ _).trans (domainSigmaTruth_correct k hφ b)

theorem domainPiTruthFormula_correct (k : ℕ) {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsPiFormula (k + 1) φ) (b : Fin n → V) :
    (domainPiTruthFormula (correctDomainFormula k)).Evalb
      ![(n : V), encodeMembershipFormula φ, standardTuple b] ↔ φ.Evalb b :=
  (eval_domainPiTruthFormula k _ _ _).trans (domainPiTruth_correct k hφ b)

theorem domainSigmaTruthFormula_exact_complexity (k : ℕ) :
    IsSigmaFormula (k + 1) (domainSigmaTruthFormula (correctDomainFormula k)) :=
  domainSigmaTruthFormula_sigma (correctDomainFormula_pi k)

theorem domainPiTruthFormula_exact_complexity (k : ℕ) :
    IsPiFormula (k + 1) (domainPiTruthFormula (correctDomainFormula k)) :=
  domainPiTruthFormula_pi (correctDomainFormula_pi k)

instance domainSigmaTruthFormula_defined (k : ℕ) :
    ℒₛₑₜ-relation₃[V] (DomainSigmaTruth k) via domainSigmaTruthFormula (correctDomainFormula k) :=
  ⟨fun (v : Fin 3 → V) ↦ by
    have hv : ![v 0, v 1, v 2] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.cases rfl (fun u ↦ Fin.elim0 u) t) j) i
    change (domainSigmaTruthFormula (correctDomainFormula k)).Evalb v ↔ DomainSigmaTruth k (v 0) (v 1) (v 2)
    rw [← hv]
    exact eval_domainSigmaTruthFormula k (v 0) (v 1) (v 2)⟩

instance domainPiTruthFormula_defined (k : ℕ) :
    ℒₛₑₜ-relation₃[V] (DomainPiTruth k) via domainPiTruthFormula (correctDomainFormula k) :=
  ⟨fun (v : Fin 3 → V) ↦ by
    have hv : ![v 0, v 1, v 2] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.cases rfl (fun u ↦ Fin.elim0 u) t) j) i
    change (domainPiTruthFormula (correctDomainFormula k)).Evalb v ↔ DomainPiTruth k (v 0) (v 1) (v 2)
    rw [← hv]
    exact eval_domainPiTruthFormula k (v 0) (v 1) (v 2)⟩

theorem domainPiTruth_iff_not_sigma_negate (k : ℕ) {n φ b : V}
    (hφ : IsMembershipFormulaCode n φ) :
    DomainPiTruth k n φ b ↔ ¬DomainSigmaTruth k n (negateFormula membershipLanguageCode ∅ n φ) b := by
  simp only [DomainPiTruth, DomainSigmaTruth, not_exists, not_and]
  refine forall_congr' fun A ↦ imp_congr_right fun _ ↦ imp_congr_right fun hb ↦ ?_
  have hb' : b ∈ structureDomain (membershipStructureCode A) ^ n := by simpa using hb
  exact ((not_congr (satisfies_negateFormula (e := ∅) membershipLanguageCode_valid hφ.valid hb')).trans not_not).symm

end ZFVP
