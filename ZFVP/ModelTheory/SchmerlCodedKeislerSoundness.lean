import ZFVP.ModelTheory.SchmerlCodedQuantifierAxioms
import ZFVP.ModelTheory.SchmerlKeislerCountableSupport

/-! Soundness of a standard Keisler derivation in internally coded models.
The countable support is extracted from the derivation before any model is
chosen, and its Q laws are then proved from the actual internal code fragment. -/

namespace ZFVP.Infinitary

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Schmerl

universe u

noncomputable def subformulaClosure {Λ : Language} (A : Set (Σ n, Formula Λ n)) :
    Set (Σ n, Formula Λ n) := ⋃ a ∈ A, Formula.subformulas a.2

theorem subset_subformulaClosure {Λ : Language} (A : Set (Σ n, Formula Λ n)) : A ⊆ subformulaClosure A := by
  intro a ha
  exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, Formula.self_mem_subformulas a.2⟩⟩

theorem subformulaClosure_countable {Λ : Language} {A : Set (Σ n, Formula Λ n)} (hA : A.Countable) :
    (subformulaClosure A).Countable := hA.biUnion fun a _ ↦ Formula.subformulas_countable a.2

theorem subformulaClosure_closed {Λ : Language} (A : Set (Σ n, Formula Λ n)) :
    Internal.SubformulaClosed (subformulaClosure A) := by
  intro a ha b hb
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp ha
  obtain ⟨hcA, hca⟩ := Set.mem_iUnion.mp hc
  exact Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hcA, Formula.subformulas_subset_of_mem hca hb⟩⟩

theorem KeislerDerivation.exists_closed_countable_soundness_support {Λ : Language} [Λ.Eq]
    {Γ : Set (Sentence Λ)} (hΓ : Γ.Countable) {n} {φ : Formula Λ n} (d : KeislerDerivation Γ φ) :
    ∃ A : Set (Σ n, Formula Λ n), A.Countable ∧ Internal.SubformulaClosed A ∧
      (∀ ψ ∈ Γ, ⟨0, ψ⟩ ∈ A) ∧ ⟨n, φ⟩ ∈ A ∧ KeislerSoundOn.{u} A Γ φ := by
  obtain ⟨B, hB, hs⟩ := d.exists_countable_soundness_support
  let S := insert ⟨n, φ⟩ (B ∪ ((fun ψ : Sentence Λ ↦ (⟨0, ψ⟩ : Σ k, Formula Λ k)) '' Γ))
  have hS : S.Countable := (hB.union (hΓ.image _)).insert _
  have hBS : B ⊆ subformulaClosure S :=
    Set.subset_union_left.trans ((Set.subset_insert _ _).trans (subset_subformulaClosure S))
  refine ⟨subformulaClosure S, subformulaClosure_countable hS, subformulaClosure_closed S, ?_, ?_, ?_⟩
  · intro ψ hψ
    exact subset_subformulaClosure S (Or.inr (Or.inr ⟨ψ, hψ, rfl⟩))
  · exact subset_subformulaClosure S (Or.inl rfl)
  · intro M ne str seq Q h hΓ b
    exact hs Q (h.mono hBS) hΓ b

namespace Internal

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Λ : Language} {L H M : V}
  {F : ∀ {k}, Λ.Func k → V} {R : ∀ {k}, Λ.Rel k → V}
  {C : {n : ℕ} → Formula Λ n → V} {A : Set (Σ n, Formula Λ n)}

theorem IsFragmentCoding.quantifierLawsOn (h : IsFragmentCoding L H F R C A)
    (hω : HasStandardOmega V) (hAC : InternalChoice V) (hM : IsStructureCode L M)
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧ (functionArities L) ‘ (F f) = (k : V))
    (hR : ∀ k (r : Λ.Rel k), R r ∈ relationSymbols L ∧ (relationArities L) ‘ (R r) = (k : V)) :
    @QuantifierLawsOn Λ A (CodedDomain M) (codedFoundationStructure hM F R hF) (InternalQ M) := by
  let := codedFoundationStructure hM F R hF
  exact ⟨fun {S T} hST hS ↦ internalQ_mono hST hS, not_internalQ_twoPoints,
    fun φ hφ b ↦ h.evalWithQ_qCountableUnion hω hAC hM hF hR φ hφ b,
    fun φ hφ b ↦ h.evalWithQ_qInterchange hω hAC hM hF hR φ hφ b⟩

theorem IsFragmentCoding.holds_of_soundness_support [Λ.Eq] (h : IsFragmentCoding L H F R C A)
    (hω : HasStandardOmega V) (hAC : InternalChoice V) (hM : IsStructureCode L M)
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧ (functionArities L) ‘ (F f) = (k : V))
    (hR : ∀ k (r : Λ.Rel k), R r ∈ relationSymbols L ∧ (relationArities L) ‘ (R r) = (k : V))
    (hEq : @Structure.Eq Λ (CodedDomain M) (codedFoundationStructure hM F R hF) inferInstance)
    {Γ : Set (Sentence Λ)} {n} {φ : Formula Λ n} (hs : KeislerSoundOn.{u} A Γ φ)
    (hΓmem : ∀ ψ ∈ Γ, ⟨0, ψ⟩ ∈ A) (hφ : ⟨n, φ⟩ ∈ A)
    (hΓ : ∀ ψ ∈ Γ, Holds L H M (0 : V) (C ψ) ∅) (b : Fin n → CodedDomain M) :
    Holds L H M (n : V) (C φ) (standardTuple (fun i ↦ (b i).val)) := by
  let := codedFoundationStructure hM F R hF
  let := codedDomain_nonempty hM
  let := hEq
  have hQ := h.quantifierLawsOn hω hAC hM hF hR
  have hΓ' : ∀ ψ ∈ Γ, Formula.EvalWithQ (InternalQ M) ψ ![] := by
    intro ψ hψ
    exact (h.holds_iff_evalWithQ hω hM hF hR ψ (hΓmem ψ hψ) ![]).mp (hΓ ψ hψ)
  exact (h.holds_iff_evalWithQ hω hM hF hR φ hφ b).mpr (hs (InternalQ M) hQ hΓ' b)

end Internal
end ZFVP.Infinitary
