import ZFVP.ModelTheory.InfinitaryAdequateQuotientStructure

namespace ZFVP.Infinitary
open LO LO.FirstOrder
universe u v
namespace WeakModel.AdequateGenericChain
open AdequateFiniteCondition
variable {L : Language.{u}} [L.Eq] [L.Encodable]
  {M : WeakModel.{u,v} L} {S : Set (TaggedFormula L)}
  {p₀ : AdequateFiniteCondition M S} (C : AdequateGenericChain M S p₀)

theorem termValues_eventually {n m} (us : Fin m → Semiterm L Empty n)
    (ts : Fin n → ℕ) (rs : Fin m → ℕ) (hv : ∀ i, C.TermValue (us i) ts (rs i)) :
    ∃ k, ∀ l, k ≤ l → ∃ ht : ∀ i, ts i < 1 + (C.point l).1,
      ∃ hr : ∀ i, rs i < 1 + (C.point l).1,
      ∀ b, (C.point l).2.formula.Eval b → ∀ i,
        b (RightCoordinate.index (hr i)) = (us i).val
          (fun j ↦ b (RightCoordinate.index (ht j))) Empty.elim := by
  classical
  choose k hk using hv
  obtain ⟨a, ha⟩ := C.coordinate_cofinal (RightCoordinate.width ts)
  refine ⟨max a (Finset.univ.sup k), ?_⟩
  intro l hl
  have hal : a ≤ l := (Nat.le_max_left _ _).trans hl
  have hkl (i : Fin m) : k i ≤ l :=
    (Finset.le_sup (by simp)).trans ((Nat.le_max_right _ _).trans hl)
  have hval (i : Fin m) := termValueAt_persistent (C.refines (hkl i)) (hk i)
  choose hr hts hh using hval
  have ht (i : Fin n) : ts i < 1 + (C.point l).1 :=
    (RightCoordinate.lt_width ts i).trans_le (ha.trans (Nat.add_le_add_left (C.refines hal).choose 1))
  exact ⟨ht, hr, fun b hb i ↦ hh i b hb⟩

theorem termValue_func {n m} (f : L.Func m) (us : Fin m → Semiterm L Empty n)
    {ts : Fin n → ℕ} {rs : Fin m → ℕ} {r : ℕ}
    (hu : ∀ i, C.TermValue (us i) ts (rs i))
    (hf : C.TermValue (.func f (fun i ↦ .bvar i)) rs r) :
    C.TermValue (.func f us) ts r := by
  obtain ⟨k, hk⟩ := C.termValues_eventually us ts rs hu
  obtain ⟨l, hl⟩ := hf
  obtain ⟨ht, hr, hh⟩ := hk (max k l) (Nat.le_max_left _ _)
  obtain ⟨hres, hrs, hg⟩ := termValueAt_persistent (C.refines (Nat.le_max_right k l)) hl
  refine ⟨max k l, hres, ht, ?_⟩
  intro b hb
  exact (hg b hb).trans (congrArg (Structure.func f) (funext fun i ↦ hh b hb i))

theorem term_val {n} (t : Semiterm L Empty n) (ts : Fin n → ℕ) :
    t.val (s := C.extensionStructure) (C.classOf ∘ ts) Empty.elim =
      C.classOf (C.termCoordinate t ts) := by
  induction t with
  | bvar i =>
    apply C.classOf_eq_iff.mpr
    apply C.termValue_unique ?_ (C.termCoordinate_value (.bvar i) ts)
    obtain ⟨k, hk⟩ := C.coordinate_cofinal (RightCoordinate.width ts)
    have ht (j : Fin n) : ts j < 1 + (C.point k).1 := (RightCoordinate.lt_width ts j).trans_le hk
    exact ⟨k, ht i, ht, fun _ _ ↦ rfl⟩
  | fvar x => exact x.elim
  | @func m f us ih =>
    change Structure.func (self := C.extensionStructure) f
      (fun i ↦ (us i).val (C.classOf ∘ ts) Empty.elim) = _
    rw [funext (fun i ↦ ih i)]
    refine (C.func_classOf f (fun i ↦ C.termCoordinate (us i) ts)).trans ?_
    apply C.classOf_eq_iff.mpr
    exact C.termValue_unique
      (C.termValue_func f us (fun i ↦ C.termCoordinate_value (us i) ts)
        (C.termCoordinate_value (.func f (fun i ↦ .bvar i)) _))
      (C.termCoordinate_value (.func f us) ts)

theorem eval_rel_terms {n m} (r : L.Rel m) (us : Fin m → Semiterm L Empty n)
    (ts : Fin n → ℕ) :
    C.Eval (ParameterInstance.ofFirstOrder (.rel r us)) ts ↔
      C.Eval (ParameterInstance.atom r) (fun i ↦ C.termCoordinate (us i) ts) := by
  obtain ⟨k, hk⟩ := C.termValues_eventually us ts (fun i ↦ C.termCoordinate (us i) ts)
    (fun i ↦ C.termCoordinate_value (us i) ts)
  constructor
  · rintro ⟨l, hl⟩
    obtain ⟨ht, hr, hh⟩ := hk (max k l) (Nat.le_max_left _ _)
    obtain ⟨hs, hg⟩ := evalAt_persistent (C.refines (Nat.le_max_right k l)) hl
    refine ⟨max k l, hr, ?_⟩
    intro b hb
    apply (ParameterInstance.eval_atom _ _).mpr
    have h := (ParameterInstance.eval_ofFirstOrder (.rel r us) _).mp (hg b hb)
    change Structure.rel r (fun i ↦ (us i).val (fun j ↦ b (RightCoordinate.index (ht j))) Empty.elim) at h
    exact (funext fun i ↦ hh b hb i).symm ▸ h
  · rintro ⟨l, hl⟩
    obtain ⟨ht, hr, hh⟩ := hk (max k l) (Nat.le_max_left _ _)
    obtain ⟨hs, hg⟩ := evalAt_persistent (C.refines (Nat.le_max_right k l)) hl
    refine ⟨max k l, ht, ?_⟩
    intro b hb
    apply (ParameterInstance.eval_ofFirstOrder (.rel r us) _).mpr
    change Structure.rel r (fun i ↦ (us i).val (fun j ↦ b (RightCoordinate.index (ht j))) Empty.elim)
    exact (funext fun i ↦ hh b hb i) ▸ (ParameterInstance.eval_atom _ _).mp (hg b hb)

/-- First-order truth in the actual coordinate quotient structure. -/
theorem firstOrder_truth {n} (φ : Semisentence L n) (ts : Fin n → ℕ) :
    φ.Evalb (s := C.extensionStructure) (C.classOf ∘ ts) ↔
      C.Eval (ParameterInstance.ofFirstOrder φ) ts := by
  induction φ with
  | verum =>
    exact iff_of_true trivial (C.eval_of_valid _ _ (by
      intro b; exact (ParameterInstance.eval_ofFirstOrder _ _).mpr trivial))
  | falsum =>
    have he : C.Eval (ParameterInstance.ofFirstOrder (M := M) (S := S) .falsum) ts ↔
        C.Eval (ParameterInstance.ofFirstOrder .verum).neg ts :=
      C.eval_congr (by
        intro b
        simp only [ParameterInstance.eval_neg, ParameterInstance.eval_ofFirstOrder]
        exact iff_of_false id (fun h ↦ h trivial))
    rw [he, C.eval_neg]
    exact iff_of_false id (fun h ↦ h (C.eval_of_valid _ _ (by
      intro b; exact (ParameterInstance.eval_ofFirstOrder _ _).mpr trivial)))
  | rel r us =>
    change Structure.rel (self := C.extensionStructure) r
      (fun i ↦ (us i).val (C.classOf ∘ ts) Empty.elim) ↔ _
    rw [funext (fun i ↦ C.term_val (us i) ts)]
    exact (C.rel_classOf r (fun i ↦ C.termCoordinate (us i) ts)).trans (C.eval_rel_terms r us ts).symm
  | nrel r us =>
    have he : C.Eval (ParameterInstance.ofFirstOrder (M := M) (S := S) (.nrel r us)) ts ↔
        C.Eval (ParameterInstance.ofFirstOrder (.rel r us)).neg ts :=
      C.eval_congr (by intro b; simp)
    change (¬Structure.rel (self := C.extensionStructure) r
      (fun i ↦ (us i).val (C.classOf ∘ ts) Empty.elim)) ↔ _
    rw [he, C.eval_neg, funext (fun i ↦ C.term_val (us i) ts)]
    exact not_congr ((C.rel_classOf r (fun i ↦ C.termCoordinate (us i) ts)).trans
      (C.eval_rel_terms r us ts).symm)
  | and φ ψ ihφ ihψ =>
    have he : C.Eval (ParameterInstance.ofFirstOrder (M := M) (S := S) (.and φ ψ)) ts ↔
        C.Eval ((ParameterInstance.ofFirstOrder φ).and (ParameterInstance.ofFirstOrder ψ)) ts :=
      C.eval_congr (by
        intro b
        simp only [ParameterInstance.eval_and, ParameterInstance.eval_ofFirstOrder]
        rfl)
    rw [he, C.eval_and]
    exact and_congr (ihφ ts) (ihψ ts)
  | or φ ψ ihφ ihψ =>
    have he : C.Eval (ParameterInstance.ofFirstOrder (M := M) (S := S) (.or φ ψ)) ts ↔
        C.Eval (((ParameterInstance.ofFirstOrder φ).neg.and (ParameterInstance.ofFirstOrder ψ).neg).neg) ts :=
      C.eval_congr (by
        intro b
        simp only [ParameterInstance.eval_neg, ParameterInstance.eval_and, ParameterInstance.eval_ofFirstOrder]
        change (_ ∨ _) ↔ ¬(¬_ ∧ ¬_)
        tauto)
    rw [he, C.eval_neg, C.eval_and, C.eval_neg, C.eval_neg]
    have h := or_congr (ihφ ts) (ihψ ts)
    change (_ ∨ _) ↔ ¬(¬_ ∧ ¬_)
    tauto
  | all φ ih =>
    have he : C.Eval (ParameterInstance.ofFirstOrder (M := M) (S := S) (.all φ)) ts ↔
        C.Eval (ParameterInstance.ofFirstOrder φ).all ts := C.eval_congr (by
          intro b
          simp only [ParameterInstance.eval_all, ParameterInstance.eval_ofFirstOrder]
          rfl)
    change (∀ x : C.Domain, φ.Evalb (x :> (C.classOf ∘ ts))) ↔ _
    rw [he, C.eval_all, C.classOf_surjective.forall]
    apply forall_congr'
    intro t
    simpa only [C.classOf_cons] using ih (t :> ts)
  | exs φ ih =>
    have he : C.Eval (ParameterInstance.ofFirstOrder (M := M) (S := S) (.exs φ)) ts ↔
        C.Eval (ParameterInstance.ofFirstOrder φ).exs ts := C.eval_congr (by
          intro b
          simp only [ParameterInstance.eval_exs, ParameterInstance.eval_ofFirstOrder]
          rfl)
    change (∃ x : C.Domain, φ.Evalb (x :> (C.classOf ∘ ts))) ↔ _
    rw [he, C.eval_exs, C.classOf_surjective.exists]
    apply exists_congr
    intro t
    simpa only [C.classOf_cons] using ih (t :> ts)

end WeakModel.AdequateGenericChain
end ZFVP.Infinitary
