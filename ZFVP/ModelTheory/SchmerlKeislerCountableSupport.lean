import ZFVP.ModelTheory.SchmerlGeneralizedInfinitarySemantics
import ZFVP.ModelTheory.InfinitarySubformulas

/-! A derivation needs Q-union and Q-interchange only on countably many
specified formulas. Its soundness certificate is uniform in the model and Q. -/

namespace ZFVP.Infinitary

open LO LO.FirstOrder

universe u

structure QuantifierLawsOn {Λ : Language} (A : Set (Σ n, Formula Λ n))
    {M : Type*} [Structure Λ M] (Q : Set M → Prop) : Prop where
  monotone : ∀ {S T : Set M}, S ⊆ T → Q S → Q T
  small : ∀ x y : M, ¬Q {z | z = x ∨ z = y}
  countableUnion : ∀ {n} (φ : ℕ → Formula Λ (n + 1)), ⟨n + 1, Formula.disj φ⟩ ∈ A →
    ∀ b : Fin n → M, Formula.EvalWithQ Q (Formula.qCountableUnion φ) b
  interchange : ∀ {n} (φ : Formula Λ (n + 1 + 1)), ⟨n + 1 + 1, φ⟩ ∈ A →
    ∀ b : Fin n → M, Formula.EvalWithQ Q (Formula.qInterchange φ) b

theorem QuantifierLawsOn.mono {Λ : Language} {A B : Set (Σ n, Formula Λ n)}
    {M : Type*} [Structure Λ M] {Q : Set M → Prop} (h : QuantifierLawsOn B Q) (hAB : A ⊆ B) :
    QuantifierLawsOn A Q :=
  ⟨h.monotone, h.small, fun φ hφ b ↦ h.countableUnion φ (hAB hφ) b,
    fun φ hφ b ↦ h.interchange φ (hAB hφ) b⟩

def BooleanSoundOn {Λ : Language} (A : Set (Σ n, Formula Λ n)) {n} (φ : Formula Λ n) : Prop :=
  ∀ {M : Type u} [Structure Λ M] (Q : Set M → Prop), QuantifierLawsOn A Q →
    ∀ b : Fin n → M, Formula.EvalWithQ Q φ b

theorem BooleanDerivation.exists_countable_soundness_support {Λ : Language} {n} {φ : Formula Λ n}
    (d : BooleanDerivation ∅ φ) :
    ∃ A : Set (Σ n, Formula Λ n), A.Countable ∧ BooleanSoundOn.{u} A φ := by
  classical
  induction d with
  | hypothesis h => exact False.elim h
  | k φ ψ =>
    refine ⟨∅, Set.countable_empty, ?_⟩
    intro M s Q h b
    simp only [Formula.evalWithQ_imp]
    exact fun hφ _ ↦ hφ
  | s φ ψ χ =>
    refine ⟨∅, Set.countable_empty, ?_⟩
    intro M s Q h b
    simp only [Formula.evalWithQ_imp]
    exact fun h₁ h₂ hφ ↦ h₁ hφ (h₂ hφ)
  | dne φ =>
    refine ⟨∅, Set.countable_empty, ?_⟩
    intro M s Q h b
    simp
  | contraposition φ ψ =>
    refine ⟨∅, Set.countable_empty, ?_⟩
    intro M s Q h b
    simp only [Formula.evalWithQ_imp, Formula.evalWithQ_neg]
    tauto
  | projection φ i =>
    refine ⟨∅, Set.countable_empty, ?_⟩
    intro M s Q h b
    simp only [Formula.countableProjection, Formula.evalWithQ_imp, Formula.evalWithQ_conj]
    exact fun hφ ↦ hφ i
  | distribution φ ψ =>
    refine ⟨∅, Set.countable_empty, ?_⟩
    intro M s Q h b
    simp only [Formula.countableDistribution, Formula.evalWithQ_imp, Formula.evalWithQ_conj]
    exact fun hh hφ i ↦ hh i hφ
  | qMono φ ψ =>
    refine ⟨∅, Set.countable_empty, ?_⟩
    intro M s Q h b
    simp only [Formula.qMonotonicity, Formula.evalWithQ_imp, Formula.evalWithQ_all, Formula.evalWithQ_q]
    exact fun hh hφ ↦ h.monotone (fun x hx ↦ hh x hx) hφ
  | qUnion φ =>
    refine ⟨{⟨n + 1, Formula.disj φ⟩}, Set.countable_singleton _, ?_⟩
    intro M s Q h b
    exact h.countableUnion φ (Set.mem_singleton _) b
  | mp _ _ ih₁ ih₂ =>
    obtain ⟨A, hA, hsA⟩ := ih₁
    obtain ⟨B, hB, hsB⟩ := ih₂
    refine ⟨A ∪ B, hA.union hB, ?_⟩
    intro M s Q h b
    exact (Formula.evalWithQ_imp Q _ _ _).mp (hsA Q (h.mono Set.subset_union_left) b)
      (hsB Q (h.mono Set.subset_union_right) b)
  | conjunction φ _ ih =>
    choose A hA hs using ih
    refine ⟨⋃ i, A i, Set.countable_iUnion hA, ?_⟩
    intro M s Q h b i
    exact hs i Q (h.mono (Set.subset_iUnion _ i)) b

def KeislerSoundOn {Λ : Language} [Λ.Eq] (A : Set (Σ n, Formula Λ n))
    (Γ : Set (Sentence Λ)) {n} (φ : Formula Λ n) : Prop :=
  ∀ {M : Type u} [Nonempty M] [Structure Λ M] [Structure.Eq Λ M] (Q : Set M → Prop),
    QuantifierLawsOn A Q → (∀ ψ ∈ Γ, Formula.EvalWithQ Q ψ ![]) →
    ∀ b : Fin n → M, Formula.EvalWithQ Q φ b

theorem KeislerDerivation.exists_countable_soundness_support {Λ : Language} [Λ.Eq]
    {Γ : Set (Sentence Λ)} {n} {φ : Formula Λ n} (d : KeislerDerivation Γ φ) :
    ∃ A : Set (Σ n, Formula Λ n), A.Countable ∧ KeislerSoundOn.{u} A Γ φ := by
  classical
  induction d with
  | hypothesis hφ =>
    refine ⟨∅, Set.countable_empty, ?_⟩
    intro M ne s seq Q h hΓ b
    rw [Formula.evalWithQ_rename]
    have he : b ∘ (Fin.elim0 : Fin 0 → _) = ![] := Subsingleton.elim _ _
    simpa only [he] using hΓ _ hφ
  | boolean d =>
    obtain ⟨A, hA, hs⟩ := d.exists_countable_soundness_support
    refine ⟨A, hA, ?_⟩
    intro M ne s seq Q h hΓ b
    exact hs Q h b
  | truth =>
    refine ⟨∅, Set.countable_empty, ?_⟩
    intro M ne s seq Q h hΓ b
    trivial
  | nonempty =>
    refine ⟨∅, Set.countable_empty, ?_⟩
    intro M ne s seq Q h hΓ b
    exact ⟨Classical.choice ne, trivial⟩
  | expansion φ =>
    refine ⟨∅, Set.countable_empty, ?_⟩
    intro M ne s seq Q h hΓ b
    simp
  | instantiation φ t =>
    refine ⟨∅, Set.countable_empty, ?_⟩
    intro M ne s seq Q h hΓ b
    simp only [Formula.universalInstantiation, Formula.evalWithQ_imp, Formula.evalWithQ_all,
      Formula.evalWithQ_substFirst]
    exact fun hh ↦ hh (t.val b Empty.elim)
  | distribution φ ψ =>
    refine ⟨∅, Set.countable_empty, ?_⟩
    intro M ne s seq Q h hΓ b
    simp only [Formula.universalDistribution, Formula.evalWithQ_imp, Formula.evalWithQ_all]
    exact fun hh hφ x ↦ hh x (hφ x)
  | exDistribution φ ψ =>
    refine ⟨∅, Set.countable_empty, ?_⟩
    intro M ne s seq Q h hΓ b
    simp only [Formula.existentialDistribution, Formula.evalWithQ_imp, Formula.evalWithQ_all,
      Formula.evalWithQ_exs]
    rintro hh ⟨x, hx⟩
    exact ⟨x, hh x hx⟩
  | vacuous φ =>
    refine ⟨∅, Set.countable_empty, ?_⟩
    intro M ne s seq Q h hΓ b
    simp only [Formula.vacuousGeneralization, Formula.evalWithQ_imp, Formula.evalWithQ_all,
      Formula.evalWithQ_rename]
    intro hh x
    have he : (x :> b) ∘ Fin.succ = b := by funext i; rfl
    simpa only [he] using hh
  | eqRefl t =>
    refine ⟨∅, Set.countable_empty, ?_⟩
    intro M ne s seq Q h hΓ b
    simp [Formula.equalityReflexivity]
  | eqSubst φ s t =>
    refine ⟨∅, Set.countable_empty, ?_⟩
    intro M ne str seq Q h hΓ b
    simp only [Formula.equalitySubstitution, Formula.evalWithQ_imp, Formula.evalWithQ_termEqual,
      Formula.evalWithQ_iff, Formula.evalWithQ_substFirst]
    intro hh
    rw [hh]
  | qSmall i j =>
    refine ⟨∅, Set.countable_empty, ?_⟩
    intro M ne str seq Q h hΓ b
    simp only [Formula.qTwoPoints, Formula.evalWithQ_neg, Formula.evalWithQ_q,
      Formula.evalWithQ_or, Formula.evalWithQ_equal, Matrix.cons_val_zero, Matrix.cons_val_succ]
    exact h.small (b i) (b j)
  | qInterchange φ =>
    refine ⟨{⟨_, φ⟩}, Set.countable_singleton _, ?_⟩
    intro M ne str seq Q h hΓ b
    exact h.interchange φ (Set.mem_singleton _) b
  | mp _ _ ih₁ ih₂ =>
    obtain ⟨A, hA, hsA⟩ := ih₁
    obtain ⟨B, hB, hsB⟩ := ih₂
    refine ⟨A ∪ B, hA.union hB, ?_⟩
    intro M ne s seq Q h hΓ b
    exact (Formula.evalWithQ_imp Q _ _ _).mp (hsA Q (h.mono Set.subset_union_left) hΓ b)
      (hsB Q (h.mono Set.subset_union_right) hΓ b)
  | conjunction φ _ ih =>
    choose A hA hs using ih
    refine ⟨⋃ i, A i, Set.countable_iUnion hA, ?_⟩
    intro M ne s seq Q h hΓ b i
    exact hs i Q (h.mono (Set.subset_iUnion _ i)) hΓ b
  | generalization _ ih =>
    obtain ⟨A, hA, hs⟩ := ih
    refine ⟨A, hA, ?_⟩
    intro M ne s seq Q h hΓ b
    exact (Formula.evalWithQ_all Q _ _).mpr fun x ↦ hs Q h hΓ (x :> b)
  | substitution σ _ ih =>
    obtain ⟨A, hA, hs⟩ := ih
    refine ⟨A, hA, ?_⟩
    intro M ne s seq Q h hΓ b
    exact (Formula.evalWithQ_subst Q _ _ _).mpr (hs Q h hΓ _)

end ZFVP.Infinitary
