import ZFVP.Syntax.BoundedSetForcingTranslation
import ZFVP.Syntax.BoundedForcingMeaning
import ZFVP.Syntax.ForcingTranslationSemantics

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_and {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.and ψ).Evalb v ↔ φ.Evalb v ∧ ψ.Evalb v := Iff.rfl
omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_or {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.or ψ).Evalb v ↔ φ.Evalb v ∨ ψ.Evalb v := Iff.rfl

theorem eval_setForcingNegation {n : ℕ} (φ : SetTheorySemisentence (n + 6))
    (T P R D H p : V) (v : Fin n → V) :
    (setForcingNegation φ).Evalb (T :> P :> R :> D :> H :> p :> v) ↔
      p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ¬φ.Evalb (T :> P :> R :> D :> H :> q :> v) := by
  simp [setForcingNegation, eval_and, eval_or, eval_boundedSetAll,
    setForcingSubst, Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
    Function.comp_def, forcingParameterTerms, Structure.rel, ← imp_iff_not_or]

theorem eval_setForcingDisjunction {n : ℕ} (φ ψ : SetTheorySemisentence (n + 6))
    (T P R D H p : V) (v : Fin n → V) :
    (setForcingDisjunction φ ψ).Evalb (T :> P :> R :> D :> H :> p :> v) ↔
      p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
        (φ.Evalb (T :> P :> R :> D :> H :> r :> v) ∨
          ψ.Evalb (T :> P :> R :> D :> H :> r :> v)) := by
  simp [setForcingDisjunction, eval_and, eval_or, eval_boundedSetAll, eval_boundedSetExs,
    setForcingSubst, Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
    Function.comp_def, forcingParameterTerms, Structure.rel, ← imp_iff_not_or]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_setForcingUniversal {n : ℕ} (φ : SetTheorySemisentence (n + 1 + 6))
    (T P R D H p : V) (v : Fin n → V) :
    (setForcingUniversal φ).Evalb (T :> P :> R :> D :> H :> p :> v) ↔
      p ∈ P ∧ ∀ x ∈ D, φ.Evalb (T :> P :> R :> D :> H :> p :> x :> v) := by
  simp [setForcingUniversal, eval_and, eval_boundedSetAll,
    setForcingSubst, Semiformula.eval_substs, Matrix.comp_vecCons',
    Function.comp_def, forcingParameterTerms, Structure.rel]

theorem eval_setForcingExistential {n : ℕ} (φ : SetTheorySemisentence (n + 1 + 6))
    (T P R D H p : V) (v : Fin n → V) :
    (setForcingExistential φ).Evalb (T :> P :> R :> D :> H :> p :> v) ↔
      p ∈ P ∧ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
        ∃ x ∈ D, φ.Evalb (T :> P :> R :> D :> H :> r :> x :> v) := by
  simp [setForcingExistential, eval_and, eval_or, eval_boundedSetAll, eval_boundedSetExs,
    setForcingSubst, Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
    Function.comp_def, forcingParameterTerms, Structure.rel, ← imp_iff_not_or]

theorem eval_setForcingAtomic {T P R H : V} [hT : IsTransitive T]
    (hH : IsAtomicTruthTable P R T H) {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → SetTheorySemiterm Empty n) (D p : V) (v : Fin n → V)
    (hv : ∀ i, v i ∈ T) :
    (setForcingAtomic r ts).Evalb (T :> P :> R :> D :> H :> p :> v) ↔
      p ∈ forcingAtomic P R r ts (standardTuple v) := by
  have ht (t : SetTheorySemiterm Empty n) : t.val v Empty.elim ∈ T := by
    simpa only [forcingTermValue_standard] using
      forcingTermValue_standard_property t v (fun x ↦ x ∈ T) hv
  cases r with
  | eq =>
    simpa [setForcingAtomic, Semiformula.eval_substs, Semiterm.val_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def,
      forcingParameterTerms, boundedAtomicEqualityEntryFormula, forcingAtomic,
      forcingTermValue_standard] using hH.entry (transitive_subnameClosed hT) (ht (ts 0)) (ht (ts 1)) (p := p)
  | mem =>
    simpa [setForcingAtomic, Semiformula.eval_substs, Semiterm.val_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def,
      forcingParameterTerms, forcingAtomic, forcingTermValue_standard] using
      eval_boundedAtomicMembershipFormula hH (ht (ts 0)) (ht (ts 1)) p

theorem boundedSetForcingTranslation_meaning {T P R D H : V} [IsTransitive T]
    (hD : D ⊆ T) (hH : IsAtomicTruthTable P R T H)
    {n : ℕ} (φ : SetTheorySemisentence n) :
    ∀ (v : Fin n → V), (∀ i, v i ∈ D) → ∀ p : V,
      (boundedSetForcingTranslation φ).Evalb (T :> P :> R :> D :> H :> p :> v) ↔
        p ∈ classForcingFormula P R (fun x ↦ x ∈ D) (by definability) φ (standardTuple v) := by
  induction φ with
  | verum => intro v hv p; rfl
  | falsum => intro v hv p; change False ↔ p ∈ (∅ : V); simp
  | rel r ts => intro v hv p; exact eval_setForcingAtomic hH r ts D p v (fun i ↦ hD _ (hv i))
  | nrel r ts =>
    intro v hv p
    rw [boundedSetForcingTranslation, eval_setForcingNegation, classForcingFormula_nrel, mem_forcingNegation_iff]
    simp only [eval_setForcingAtomic hH r ts D _ v (fun i ↦ hD _ (hv i))]
  | and φ ψ ihφ ihψ =>
    intro v hv p
    rw [boundedSetForcingTranslation, eval_and, ihφ v hv p, ihψ v hv p,
      classForcingFormula_and, mem_inter_iff]
  | or φ ψ ihφ ihψ =>
    intro v hv p
    rw [boundedSetForcingTranslation, eval_setForcingDisjunction, classForcingFormula_or, mem_forcingClosure_iff]
    simp only [ihφ v hv, ihψ v hv, mem_union_iff]
    apply and_congr_right
    intro _
    apply forall_congr'
    intro q
    apply imp_congr_right
    intro _
    apply imp_congr_right
    intro _
    constructor
    · rintro ⟨r, _, hrq, hr⟩
      exact ⟨r, hr, hrq⟩
    · rintro ⟨r, hr, hrq⟩
      exact ⟨r, hr.elim (classForcingFormula_subset P R _ (by definability) φ _ r)
        (classForcingFormula_subset P R _ (by definability) ψ _ r), hrq, hr⟩
  | all φ ih =>
    intro v hv p
    rw [boundedSetForcingTranslation, eval_setForcingUniversal,
      classForcingFormula_all, mem_forcingClassIntersection_iff]
    apply and_congr Iff.rfl
    exact forall_congr' fun x ↦ imp_congr_right fun hx ↦ ih (x :> v) (fun i ↦ Fin.cases hx hv i) p
  | exs φ ih =>
    intro v hv p
    rw [boundedSetForcingTranslation, eval_setForcingExistential, classForcingFormula_exs_dense_iff]
    apply and_congr Iff.rfl
    apply forall_congr'
    intro q
    apply imp_congr_right
    intro _
    apply imp_congr_right
    intro _
    apply exists_congr
    intro r
    apply and_congr_right
    intro _
    apply and_congr Iff.rfl
    exact exists_congr fun x ↦ and_congr_right fun hx ↦ ih (x :> v) (fun i ↦ Fin.cases hx hv i) r

end ZFVP
