import ZFVP.ModelTheory.ClassForcingTowerFormula

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V) {G : Set V}
    (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)

noncomputable def classAssignment {n : ℕ} (v : Fin n → T.Name) : Fin n → T.ClassModel hG :=
  fun i ↦ T.ofClassName hG (v i)

theorem classAssignment_cons {n : ℕ} (v : Fin n → T.Name) (σ : T.Name) :
    T.classAssignment hG (σ :> v) = T.ofClassName hG σ :> T.classAssignment hG v := by
  funext i
  exact Fin.cases rfl (fun _ ↦ rfl) i

theorem classTerm_value {n : ℕ} (v : Fin n → T.Name) (t : Semiterm ℒₛₑₜ Empty n) :
    t.val (T.classAssignment hG v) Empty.elim =
      T.ofClassName hG (ClassForcingQuotient.nameTerm T.IsName v t) := by
  cases t with
  | bvar _ => rfl
  | fvar x => exact Empty.elim x
  | func f _ => exact Empty.elim f

theorem towerAtomic_truth {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → Semiterm ℒₛₑₜ Empty n) (v : Fin n → T.Name) :
    (Semiformula.rel r ts).Evalb (T.classAssignment hG v) ↔
      T.ClassMeets G (T.towerAtomic r ts (standardTuple (fun i ↦ (v i).val))) := by
  cases r <;> unfold towerAtomic <;> dsimp only
  all_goals simp only [Semiformula.eval_rel, classTerm_value,
    ClassForcingQuotient.term_tuple, Function.comp_def]
  · exact T.equal_truth hG _ _
  · exact T.member_truth hG _ _

/-- Truth for every standard finite formula in the actual class tower extension. -/
theorem towerFormula_truth [Countable V] {n : ℕ} (φ : SetTheorySemisentence n)
    (v : Fin n → T.Name) :
    φ.Evalb (T.classAssignment hG v) ↔
      T.ClassMeets G (T.towerFormula φ (standardTuple (fun i ↦ (v i).val))) := by
  induction φ with
  | verum =>
    change True ↔ T.ClassMeets G T.Condition
    constructor
    · intro _
      obtain ⟨p, hp⟩ := hG.1.2.1
      exact ⟨p, hp, hG.1.1 p hp⟩
    · intro _; trivial
  | falsum =>
    change False ↔ T.ClassMeets G (fun _ ↦ False)
    simp [ClassMeets]
  | rel r ts => exact T.towerAtomic_truth hG r ts v
  | nrel r ts =>
    change ¬(Semiformula.rel r ts).Evalb (T.classAssignment hG v) ↔
      T.ClassMeets G (T.ClassNegation (T.towerAtomic r ts _))
    rw [T.classMeets_negation hG _ (by definability)
      (T.towerAtomic_regular r ts v).1 (T.towerAtomic_regular r ts v).2.1]
    exact not_congr (T.towerAtomic_truth hG r ts v)
  | and φ ψ ihφ ihψ =>
    change (φ.Evalb _ ∧ ψ.Evalb _) ↔ T.ClassMeets G
      (fun p ↦ T.towerFormula φ _ p ∧ T.towerFormula ψ _ p)
    rw [T.classMeets_and hG (T.towerFormula_regular φ v).2.1
      (T.towerFormula_regular ψ v).2.1]
    exact and_congr (ihφ v) (ihψ v)
  | or φ ψ ihφ ihψ =>
    change (φ.Evalb _ ∨ ψ.Evalb _) ↔ T.ClassMeets G
      (T.ClassClosure (fun p ↦ T.towerFormula φ _ p ∨ T.towerFormula ψ _ p))
    rw [T.classMeets_or hG _ _ (by definability) (by definability)
      (T.towerFormula_regular φ v) (T.towerFormula_regular ψ v)]
    exact or_congr (ihφ v) (ihψ v)
  | @all n φ ih =>
    change (∀ q : T.ClassModel hG, φ.Evalb (q :> T.classAssignment hG v)) ↔
      T.ClassMeets G (fun p ↦ T.Condition p ∧ ∀ x, T.IsName x →
        T.towerFormula φ (assignmentPrepend (n : V) (standardTuple (fun i ↦ (v i).val)) x) p)
    rw [T.classMeets_all hG T.IsName _ (by definability) (by definability)
      (fun x hx ↦ T.towerFormula_regular φ (⟨x, hx⟩ :> v))]
    constructor
    · intro hall x hx
      exact (ih (⟨x, hx⟩ :> v)).mp (by
        rw [classAssignment_cons]; exact hall _)
    · intro hall q
      obtain ⟨σ, rfl⟩ := T.ofClassName_surjective hG q
      have hv := (ih (σ :> v)).mpr (hall σ.val σ.property)
      simpa only [classAssignment_cons] using hv
  | @exs n φ ih =>
    change (∃ q : T.ClassModel hG, φ.Evalb (q :> T.classAssignment hG v)) ↔
      T.ClassMeets G (T.ClassClosure (fun p ↦ ∃ x, T.IsName x ∧
        T.towerFormula φ (assignmentPrepend (n : V) (standardTuple (fun i ↦ (v i).val)) x) p))
    rw [T.classMeets_exists hG T.IsName _ (by definability) (by definability)
      (fun x hx ↦ T.towerFormula_regular φ (⟨x, hx⟩ :> v))]
    constructor
    · rintro ⟨q, hq⟩
      obtain ⟨σ, rfl⟩ := T.ofClassName_surjective hG q
      exact ⟨σ.val, σ.property, (ih (σ :> v)).mp (by
        simpa only [classAssignment_cons] using hq)⟩
    · rintro ⟨x, hx, hF⟩
      refine ⟨T.ofClassName hG ⟨x, hx⟩, ?_⟩
      have hv := (ih (⟨x, hx⟩ :> v)).mpr hF
      simpa only [classAssignment_cons] using hv

end DefinableForcingTower
end ZFVP
