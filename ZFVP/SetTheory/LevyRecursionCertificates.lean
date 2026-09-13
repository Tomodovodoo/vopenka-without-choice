import ZFVP.SetTheory.BoundedRestriction
import ZFVP.SetTheory.BoundedValue
import ZFVP.SetTheory.BoundedFunctionDomain
import ZFVP.SetTheory.LevyGraphAssembly
import ZFVP.SetTheory.UniformRecursion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaRecursionAttemptFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “α f. !IsOrdinal.dfn α ∧ !boundedFunctionDomainFormula f α ∧
    ∀ β ∈ α, ∃ g, !boundedRestrictFormula g f β ∧ ∃ y, !boundedValueFormula y f β ∧ !φ y g”

def piRecursionAttemptFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “α f. !IsOrdinal.dfn α ∧ !boundedFunctionDomainFormula f α ∧
    ∀ β ∈ α, ∀ g, !boundedRestrictFormula g f β → ∀ y, !boundedValueFormula y f β → !φ y g”

theorem sigmaRecursionAttemptFormula_sigma {k : ℕ} {φ : SetTheorySemisentence 2}
    (hφ : IsSigmaFormula (k + 1) φ) : IsSigmaFormula (k + 1) (sigmaRecursionAttemptFormula φ) :=
  .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.and (.bounded (boundedFunctionDomainFormula_bounded.subst _))
      (.boundedAll (.bvar 0) (.exs (.and (.bounded (boundedRestrictFormula_bounded.subst _))
        (.exs (.and (.bounded (boundedValueFormula_bounded.subst _)) (hφ.subst _)))))))

theorem piRecursionAttemptFormula_pi {k : ℕ} {φ : SetTheorySemisentence 2}
    (hφ : IsPiFormula (k + 1) φ) : IsPiFormula (k + 1) (piRecursionAttemptFormula φ) :=
  .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.and (.bounded (boundedFunctionDomainFormula_bounded.subst _))
      (.boundedAll (.bvar 0) (.all (.or (.bounded (boundedRestrictFormula_bounded.subst _).neg)
        (.all (.or (.bounded (boundedValueFormula_bounded.subst _).neg) (hφ.subst _)))))))

def sigmaTransfiniteRecFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “y α. (∃ f, !(sigmaRecursionAttemptFormula φ) α f ∧ !φ y f) ∨
    (¬!IsOrdinal.dfn α ∧ !boundedEmptyFormula y)”

def piTransfiniteRecFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “y α. ∀ z, !(sigmaTransfiniteRecFormula φ) z α → y = z”

theorem sigmaTransfiniteRecFormula_sigma {k : ℕ} {φ : SetTheorySemisentence 2}
    (hφ : IsSigmaFormula (k + 1) φ) : IsSigmaFormula (k + 1) (sigmaTransfiniteRecFormula φ) :=
  .or (.exs (.and ((sigmaRecursionAttemptFormula_sigma hφ).subst _) (hφ.subst _)))
    (.bounded (.and (isOrdinalFormula_bounded.subst _).neg (boundedEmptyFormula_bounded.subst _)))

theorem piTransfiniteRecFormula_pi {k : ℕ} {φ : SetTheorySemisentence 2}
    (hφ : IsSigmaFormula (k + 1) φ) : IsPiFormula (k + 1) (piTransfiniteRecFormula φ) :=
  .all (.or ((sigmaTransfiniteRecFormula_sigma hφ).subst _).neg (.bounded (.rel _ _)))

def sigmaTransfiniteHistoryFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  graphAssemblyFormula (sigmaTransfiniteRecFormula φ)

theorem sigmaTransfiniteHistoryFormula_sigma {k : ℕ} {φ : SetTheorySemisentence 2}
    (hφ : IsSigmaFormula (k + 1) φ) : IsSigmaFormula (k + 1) (sigmaTransfiniteHistoryFormula φ) :=
  graphAssemblyFormula_levy (sigmaTransfiniteRecFormula_sigma hφ)

def piTransfiniteHistoryFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  graphAssemblyFormula (piTransfiniteRecFormula φ)

theorem piTransfiniteHistoryFormula_pi {k : ℕ} {φ : SetTheorySemisentence 2}
    (hφ : IsSigmaFormula (k + 1) φ) : IsPiFormula (k + 1) (piTransfiniteHistoryFormula φ) :=
  graphAssemblyFormula_levy (piTransfiniteRecFormula_pi hφ)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem isAttempt_iff_value (F : V → V) (α f : V) :
    IsAttempt F α f ↔ IsOrdinal α ∧ IsFunction f ∧ domain f = α ∧
      ∀ β ∈ α, f ‘ β = F (f ↾ β) := by
  constructor
  · rintro ⟨hα, hf, hd, hs⟩
    let := hf
    exact ⟨hα, hf, hd, fun β hβ ↦ (hs β hβ (f ‘ β)).mp (kpair_value_mem (hd.symm ▸ hβ))⟩
  · rintro ⟨hα, hf, hd, hs⟩
    let := hf
    refine ⟨hα, hf, hd, fun β hβ y ↦ ?_⟩
    rw [kpair_mem_iff_value, hd, hs β hβ]
    simp [hβ, eq_comm]

instance sigmaRecursionAttemptFormula_defined (F : V → V) (φ : SetTheorySemisentence 2)
    [ℒₛₑₜ-function₁ F via φ] : ℒₛₑₜ-relation (IsAttempt F) via sigmaRecursionAttemptFormula φ :=
  ⟨fun v ↦ by
    change (sigmaRecursionAttemptFormula φ).Evalb v ↔ IsAttempt F (v 0) (v 1)
    rw [isAttempt_iff_value]
    simp [sigmaRecursionAttemptFormula, and_assoc]⟩

instance piRecursionAttemptFormula_defined (F : V → V) (φ : SetTheorySemisentence 2)
    [ℒₛₑₜ-function₁ F via φ] : ℒₛₑₜ-relation (IsAttempt F) via piRecursionAttemptFormula φ :=
  ⟨fun v ↦ by
    change (piRecursionAttemptFormula φ).Evalb v ↔ IsAttempt F (v 0) (v 1)
    rw [isAttempt_iff_value]
    simp [piRecursionAttemptFormula, and_assoc]⟩

instance sigmaTransfiniteRecFormula_defined (F : V → V) (φ : SetTheorySemisentence 2)
    [hF : ℒₛₑₜ-function₁ F via φ] :
    ℒₛₑₜ-function₁ (Replacement.transfiniteRec F hF.to_definable) via sigmaTransfiniteRecFormula φ :=
  ⟨fun v ↦ by simp [sigmaTransfiniteRecFormula, transfiniteRec_eq_iff]⟩

instance piTransfiniteRecFormula_defined (F : V → V) (φ : SetTheorySemisentence 2)
    [hF : ℒₛₑₜ-function₁ F via φ] :
    ℒₛₑₜ-function₁ (Replacement.transfiniteRec F hF.to_definable) via piTransfiniteRecFormula φ :=
  ⟨fun v ↦ by simp [piTransfiniteRecFormula]⟩

instance sigmaTransfiniteHistoryFormula_defined (F : V → V) (φ : SetTheorySemisentence 2)
    [hF : ℒₛₑₜ-function₁ F via φ] :
    ℒₛₑₜ-function₁ (fun θ ↦ definableGraph θ (Replacement.transfiniteRec F hF.to_definable)
      (Replacement.transfiniteRec_definable hF.to_definable)) via sigmaTransfiniteHistoryFormula φ :=
  ⟨fun v ↦ by
    have hv : v = ![v 0, v 1] := by
      funext i
      exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.elim0 i) i) i
    exact (Iff.of_eq (congrArg (fun w ↦ (sigmaTransfiniteHistoryFormula φ).Evalb w) hv)).trans
      (eval_graphAssemblyFormula (sigmaTransfiniteRecFormula φ) (v 0) (v 1) ![]
        (Replacement.transfiniteRec F hF.to_definable) _ (fun i _ y ↦ by simp))⟩

instance piTransfiniteHistoryFormula_defined (F : V → V) (φ : SetTheorySemisentence 2)
    [hF : ℒₛₑₜ-function₁ F via φ] :
    ℒₛₑₜ-function₁ (fun θ ↦ definableGraph θ (Replacement.transfiniteRec F hF.to_definable)
      (Replacement.transfiniteRec_definable hF.to_definable)) via piTransfiniteHistoryFormula φ :=
  ⟨fun v ↦ by
    have hv : v = ![v 0, v 1] := by
      funext i
      exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.elim0 i) i) i
    exact (Iff.of_eq (congrArg (fun w ↦ (piTransfiniteHistoryFormula φ).Evalb w) hv)).trans
      (eval_graphAssemblyFormula (piTransfiniteRecFormula φ) (v 0) (v 1) ![]
        (Replacement.transfiniteRec F hF.to_definable) _ (fun i _ y ↦ by simp))⟩

end ZFVP
