import ZFVP.Syntax.SigmaOneBoundedModelTruth

/-! Sigma-one and Pi-one definitions of guarded bounded truth in the ambient universe. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedNonemptyFormula : SetTheorySemisentence 1 := “A. ∃ x ∈ A, ⊤”

theorem boundedNonemptyFormula_bounded : IsBoundedSetFormula boundedNonemptyFormula := .exs (.bvar 0) .verum

def sigmaOneBoundedTruthFormula (answer : Bool) : SetTheorySemisentence 3 :=
  “n φ b. ∃ A, !boundedNonemptyFormula A ∧ !(sigmaOneBoundedModelTruthFormula answer) A n φ b”

theorem sigmaOneBoundedTruthFormula_sigmaOne (answer : Bool) :
    IsLevyFormula .sigma 1 (sigmaOneBoundedTruthFormula answer) :=
  .exs (.and (.bounded (boundedNonemptyFormula_bounded.subst _))
    ((sigmaOneBoundedModelTruthFormula_sigmaOne answer).subst _))

def sigmaOneNotBoundedTruthFormula : SetTheorySemisentence 3 :=
  “n φ b. ∃ F, !sigmaOneBoundedFamilyFormula F ∧ ∃ U, !codingSupportFormula U ∧ n ∈ U ∧ b ∈ U ∧
    (¬!boundedPairMemberFormula F n φ ∨ ¬!boundedFunctionFormula b n U ∨ !(sigmaOneBoundedTruthFormula false) n φ b)”

def piOneBoundedTruthFormula : SetTheorySemisentence 3 := ∼sigmaOneNotBoundedTruthFormula

theorem sigmaOneNotBoundedTruthFormula_sigmaOne : IsLevyFormula .sigma 1 sigmaOneNotBoundedTruthFormula := by
  refine .exs (.and (sigmaOneBoundedFamilyFormula_sigmaOne.subst _) (.exs ?_))
  refine .and (.bounded (codingSupportFormula_bounded.subst _)) (.and (.bounded (.rel _ _)) (.and (.bounded (.rel _ _)) ?_))
  exact .or (.bounded (boundedPairMemberFormula_bounded.subst _).neg)
    (.or (.bounded (boundedFunctionFormula_bounded.subst _).neg) ((sigmaOneBoundedTruthFormula_sigmaOne false).subst _))

theorem piOneBoundedTruthFormula_piOne : IsLevyFormula .pi 1 piOneBoundedTruthFormula :=
  sigmaOneNotBoundedTruthFormula_sigmaOne.neg

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance boundedNonemptyFormula_defined : ℒₛₑₜ-predicate[V] IsNonempty via boundedNonemptyFormula :=
  ⟨fun v ↦ by
    simp [boundedNonemptyFormula]
    exact ⟨fun h ↦ ⟨h⟩, fun h ↦ h.nonempty⟩⟩

def BoundedPartialTruth (n φ b : V) : Prop :=
  IsBoundedFormulaCode n φ ∧ IsFunction b ∧ domain b = n ∧ BoundedTruth n φ b

theorem function_on_support_iff {U b : V} [IsCodingSupport U] (hb : b ∈ U) (n : V) :
    b ∈ U ^ n ↔ IsFunction b ∧ domain b = n := by
  constructor
  · intro hf
    exact ⟨IsFunction.of_mem hf, domain_eq_of_mem_function hf⟩
  · rintro ⟨hf, rfl⟩
    let := hf
    exact mem_function_of_mem_function_of_subset (IsFunction.mem_function b) (range_subset_codingSupport hb)

theorem eval_sigmaOneBoundedTruthFormula (answer : Bool) (n φ b : V) :
    (sigmaOneBoundedTruthFormula answer).Evalb ![n, φ, b] ↔
      IsBoundedFormulaCode n φ ∧ IsFunction b ∧ domain b = n ∧ TruthAnswer answer (BoundedTruth n φ b) := by
  simp [sigmaOneBoundedTruthFormula, eval_sigmaOneBoundedModelTruthFormula]
  constructor
  · rintro ⟨A, hA, ht, hφ, hb, hanswer⟩
    let := ht
    have hfunc : IsFunction b := IsFunction.of_mem hb
    exact ⟨hφ, hfunc, domain_eq_of_mem_function hb,
      (truthAnswer_congr answer (boundedTruth_iff_membershipSatisfies hφ hA hb)).mpr hanswer⟩
  · rintro ⟨hφ, hf, hb, hanswer⟩
    let := hf
    have hbA := assignment_mem_boundedTruthDomain hb
    refine ⟨boundedTruthDomain b, boundedTruthDomain_nonempty b, inferInstance, hφ, hbA, ?_⟩
    exact (truthAnswer_congr answer (boundedTruth_iff_membershipSatisfies hφ (boundedTruthDomain_nonempty b) hbA)).mp hanswer

theorem eval_sigmaOneNotBoundedTruthFormula (n φ b : V) :
    sigmaOneNotBoundedTruthFormula.Evalb ![n, φ, b] ↔ ¬BoundedPartialTruth n φ b := by
  simp [sigmaOneNotBoundedTruthFormula, eval_sigmaOneBoundedTruthFormula, TruthAnswer]
  constructor
  · rintro ⟨U, hU, _, hb, h⟩ ⟨hφ, hf, hd, ht⟩
    let := hU
    rcases h with h | h | ⟨_, _, _, h⟩
    · exact h hφ
    · exact h ((function_on_support_iff hb n).mpr ⟨hf, hd⟩)
    · exact h ht
  · intro h
    obtain ⟨U, hU, hpair⟩ := codingSupport_containing ⟨n, b⟩ₖ
    let := hU
    obtain ⟨hnU, hbU⟩ := kpair_components_mem_transitive hpair
    refine ⟨U, hU, hnU, hbU, ?_⟩
    by_cases hφ : IsBoundedFormulaCode n φ
    · by_cases hf : b ∈ U ^ n
      · obtain ⟨hf', hd⟩ := (function_on_support_iff hbU n).mp hf
        exact Or.inr (Or.inr ⟨hφ, hf', hd, fun ht ↦ h ⟨hφ, hf', hd, ht⟩⟩)
      · exact Or.inr (Or.inl hf)
    · exact Or.inl hφ

theorem eval_piOneBoundedTruthFormula (n φ b : V) :
    piOneBoundedTruthFormula.Evalb ![n, φ, b] ↔ BoundedPartialTruth n φ b := by
  simp [piOneBoundedTruthFormula, eval_sigmaOneNotBoundedTruthFormula]

theorem eval_sigmaOneBoundedTruth_true (n φ b : V) :
    (sigmaOneBoundedTruthFormula true).Evalb ![n, φ, b] ↔ BoundedPartialTruth n φ b := by
  simpa only [TruthAnswer, ite_true, BoundedPartialTruth] using eval_sigmaOneBoundedTruthFormula true n φ b

instance sigmaOneBoundedPartialTruth_defined :
    ℒₛₑₜ-relation₃[V] BoundedPartialTruth via sigmaOneBoundedTruthFormula true :=
  ⟨fun (v : Fin 3 → V) ↦ by
    have hv : ![v 0, v 1, v 2] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) k) j) i
    change (sigmaOneBoundedTruthFormula true).Evalb v ↔ BoundedPartialTruth (v 0) (v 1) (v 2)
    rw [← hv]
    exact eval_sigmaOneBoundedTruth_true (v 0) (v 1) (v 2)⟩

instance piOneBoundedPartialTruth_defined :
    ℒₛₑₜ-relation₃[V] BoundedPartialTruth via piOneBoundedTruthFormula :=
  ⟨fun (v : Fin 3 → V) ↦ by
    have hv : ![v 0, v 1, v 2] = v := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) k) j) i
    change piOneBoundedTruthFormula.Evalb v ↔ BoundedPartialTruth (v 0) (v 1) (v 2)
    rw [← hv]
    exact eval_piOneBoundedTruthFormula (v 0) (v 1) (v 2)⟩

theorem boundedPartialTruth_correct {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsBoundedSetFormula φ) (b : Fin n → V) :
    BoundedPartialTruth (n : V) (encodeMembershipFormula φ) (standardTuple b) ↔ φ.Evalb b := by
  simp only [BoundedPartialTruth, hφ.encode, true_and,
    show IsFunction (standardTuple b) from inferInstance, domain_standardTuple]
  exact boundedTruth_correct hφ b

theorem sigmaOneBoundedPartialTruth_correct {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsBoundedSetFormula φ) (b : Fin n → V) :
    (sigmaOneBoundedTruthFormula true).Evalb ![(n : V), encodeMembershipFormula φ, standardTuple b] ↔ φ.Evalb b :=
  (eval_sigmaOneBoundedTruth_true _ _ _).trans (boundedPartialTruth_correct hφ b)

theorem piOneBoundedPartialTruth_correct {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : IsBoundedSetFormula φ) (b : Fin n → V) :
    piOneBoundedTruthFormula.Evalb ![(n : V), encodeMembershipFormula φ, standardTuple b] ↔ φ.Evalb b :=
  (eval_piOneBoundedTruthFormula _ _ _).trans (boundedPartialTruth_correct hφ b)

end ZFVP
