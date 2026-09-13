import ZFVP.ModelTheory.ForcingQuotient
import ZFVP.SetTheory.FormulaForcing

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def forcingNameTerm {P : V} {n : ℕ} (v : Fin n → ForcingName P) :
    Semiterm ℒₛₑₜ Empty n → ForcingName P
  | .bvar i => v i
  | .fvar x => Empty.elim x
  | .func f _ => Empty.elim f

theorem forcingTermValue_tuple {P : V} {n : ℕ} (v : Fin n → ForcingName P)
    (t : Semiterm ℒₛₑₜ Empty n) :
    forcingTermValue t (standardTuple (fun i ↦ (v i).val)) = (forcingNameTerm v t).val := by
  cases t with
  | bvar i => exact value_standardTuple _ i
  | fvar x => exact Empty.elim x
  | func f _ => exact Empty.elim f

def forcingQuotientAssignment (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingFilter P R G) {n : ℕ} (v : Fin n → ForcingName P) :
    Fin n → ForcingQuotient P R G hR hG := fun i ↦ forcingQuotientMk P R G hR hG (v i)

theorem forcingNameTerm_quotient_value (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingFilter P R G) {n : ℕ} (v : Fin n → ForcingName P)
    (t : Semiterm ℒₛₑₜ Empty n) :
    t.val (forcingQuotientAssignment P R G hR hG v) Empty.elim =
      forcingQuotientMk P R G hR hG (forcingNameTerm v t) := by
  cases t with
  | bvar _ => rfl
  | fvar x => exact Empty.elim x
  | func f _ => exact Empty.elim f

theorem forcingQuotientAssignment_cons (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingFilter P R G) {n : ℕ} (v : Fin n → ForcingName P) (σ : ForcingName P) :
    forcingQuotientAssignment P R G hR hG (σ :> v) =
      forcingQuotientMk P R G hR hG σ :> forcingQuotientAssignment P R G hR hG v := by
  funext i
  exact Fin.cases rfl (fun _ ↦ rfl) i

theorem forcingNameTuple_cons {P : V} {n : ℕ} (v : Fin n → ForcingName P) (σ : ForcingName P) :
    standardTuple (fun i ↦ ((σ :> v) i).val) =
      assignmentPrepend (n : V) (standardTuple (fun i ↦ (v i).val)) σ.val := rfl

theorem forcingAtomic_quotient_truth (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingFilter P R G) {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → Semiterm ℒₛₑₜ Empty n) (v : Fin n → ForcingName P) :
    (Semiformula.rel r ts).Evalb (forcingQuotientAssignment P R G hR hG v) ↔
      GenericMeets G (forcingAtomic P R r ts (standardTuple (fun i ↦ (v i).val))) := by
  cases r <;> simp only [forcingAtomic, Semiformula.eval_rel, forcingNameTerm_quotient_value,
    forcingTermValue_tuple, Function.comp_def]
  · exact forcingQuotientMk_eq_iff P R G hR hG _ _
  · exact forcingQuotientMk_mem_iff P R G hR hG _ _

theorem forcingFormula_quotient_truth (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) {n : ℕ} (φ : SetTheorySemisentence n)
    (v : Fin n → ForcingName P) :
    φ.Evalb (forcingQuotientAssignment P R G hR hG.1 v) ↔
      GenericMeets G (forcingFormula P R φ (standardTuple (fun i ↦ (v i).val))) := by
  unfold IsExternalForcingGeneric at hG
  induction φ with
  | verum =>
    change True ↔ GenericMeets G P
    constructor
    · intro _
      obtain ⟨p, hpG⟩ := hG.1.2.1
      exact ⟨p, hpG, hG.1.1 p hpG⟩
    · intro _
      trivial
  | falsum =>
    change False ↔ GenericMeets G ∅
    simp [GenericMeets]
  | rel r ts => exact forcingAtomic_quotient_truth P R G hR hG.1 r ts v
  | nrel r ts =>
    rw [forcingFormula_nrel, genericMeets_negation hR hG
      (forcingAtomic_regular hR r ts _).1 (forcingAtomic_regular hR r ts _).2.1]
    exact not_congr (forcingAtomic_quotient_truth P R G hR hG.1 r ts v)
  | and φ ψ ihφ ihψ =>
    rw [forcingFormula_and, genericMeets_inter hG.1
      (forcingFormula_regular hR φ _).2.1 (forcingFormula_regular hR ψ _).2.1]
    exact and_congr (ihφ v) (ihψ v)
  | or φ ψ ihφ ihψ =>
    have hAP : forcingFormula P R φ (standardTuple (fun i ↦ (v i).val)) ∪
        forcingFormula P R ψ (standardTuple (fun i ↦ (v i).val)) ⊆ P := by
      intro p hp
      rcases mem_union_iff.mp hp with hφ | hψ
      · exact (forcingFormula_regular hR φ _).1 p hφ
      · exact (forcingFormula_regular hR ψ _).1 p hψ
    have hd : IsForcingDownwardClosed P R (forcingFormula P R φ (standardTuple (fun i ↦ (v i).val)) ∪
        forcingFormula P R ψ (standardTuple (fun i ↦ (v i).val))) := by
      intro p hp q hq hqp
      rcases mem_union_iff.mp hp with hφ | hψ
      · exact mem_union_iff.mpr (Or.inl ((forcingFormula_regular hR φ _).2.1 p hφ q hq hqp))
      · exact mem_union_iff.mpr (Or.inr ((forcingFormula_regular hR ψ _).2.1 p hψ q hq hqp))
    rw [forcingFormula_or, genericMeets_closure hR hG hAP hd, genericMeets_union]
    exact or_congr (ihφ v) (ihψ v)
  | @all n φ ih =>
    change (∀ q : ForcingQuotient P R G hR hG.1,
      φ.Evalb (q :> forcingQuotientAssignment P R G hR hG.1 v)) ↔ _
    rw [forcingFormula_all, genericMeets_classIntersection hR hG
      (IsForcingName P) (by definability) _ (by definability)
      (fun x _ ↦ forcingFormula_regular hR φ _)]
    constructor
    · intro hall x hx
      let σ : ForcingName P := ⟨x, hx⟩
      have hv := (ih (σ :> v)).mp (by
        rw [forcingQuotientAssignment_cons]
        exact hall (forcingQuotientMk P R G hR hG.1 σ))
      simpa only [forcingNameTuple_cons] using hv
    · intro hall q
      obtain ⟨σ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 q
      have hv := (ih (σ :> v)).mpr (by
        simpa only [forcingNameTuple_cons] using hall σ.val σ.property)
      simpa only [forcingQuotientAssignment_cons] using hv
  | @exs n φ ih =>
    change (∃ q : ForcingQuotient P R G hR hG.1,
      φ.Evalb (q :> forcingQuotientAssignment P R G hR hG.1 v)) ↔ _
    rw [forcingFormula_exs, genericMeets_existential hR hG
      (IsForcingName P) (by definability) _ (by definability)
      (fun x _ ↦ (forcingFormula_regular hR φ _).2.1)]
    constructor
    · rintro ⟨q, hq⟩
      obtain ⟨σ, rfl⟩ := forcingQuotientMk_surjective P R G hR hG.1 q
      refine ⟨σ.val, σ.property, ?_⟩
      have hv := (ih (σ :> v)).mp (by simpa only [forcingQuotientAssignment_cons] using hq)
      simpa only [forcingNameTuple_cons] using hv
    · rintro ⟨x, hx, hF⟩
      let σ : ForcingName P := ⟨x, hx⟩
      refine ⟨forcingQuotientMk P R G hR hG.1 σ, ?_⟩
      have hv := (ih (σ :> v)).mpr (by simpa only [forcingNameTuple_cons] using hF)
      simpa only [forcingQuotientAssignment_cons] using hv

end ZFVP
