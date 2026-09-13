import ZFVP.ModelTheory.ForcingRetractionModel
import ZFVP.ModelTheory.ForcingModelSequences
import ZFVP.ModelTheory.ForcingModelEvaluation
import ZFVP.ModelTheory.ForcingDependentChoiceTransfer
import ZFVP.ModelTheory.ForcingClosedSequences
import ZFVP.SetTheory.OrdinalIndexedChoice

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

variable (A B : ForcingContext V) {π : V} (hπ : IsForcingRetraction A.P A.R B.P B.R π)
  (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P) (hone : A.one = B.one)

include hone

theorem retractionInclusion_sequenceValue (s : V) (hs : IsNameSequence A.P s) :
    retractionInclusion A B hπ hG (A.sequenceValue s hs) =
      B.sequenceValue s (fun i hi ↦ (hs i hi).mono hπ.inclusion) := by
  change B.ofName ⟨sequenceName A.one s, _⟩ = B.ofName ⟨sequenceName B.one s, _⟩
  congr 1
  exact Subtype.ext (congrArg (fun one ↦ sequenceName one s) hone)

omit hone in
set_option maxHeartbeats 1200000 in
theorem retractionInclusion_function_sequence_of_closed {γ : V} [IsOrdinal γ]
    (hDC : InternalDependentChoiceAt γ)
    (hclosed : ∀ α, IsOrdinal α → α ⊆ γ → IsForcingClosedAt B.P B.R α)
    {τ : ForcingName A.P} {f : B.Model}
    (hf : f ∈ retractionInclusion A B hπ hG (A.ofName τ) ^ B.check γ) :
    ∃ s, ∃ hsN : IsNameSequence A.P s, s ∈ (domain τ.val) ^ γ ∧
      B.sequenceValue s (fun i hi ↦ (hsN i hi).mono hπ.inclusion) = f := by
  let := IsFunction.of_mem hf
  let C := domain τ.val
  have hC : ∀ σ ∈ C, IsForcingName A.P σ := by
    intro σ hσ
    obtain ⟨p, hp⟩ := mem_domain_iff.mp hσ
    exact forcingName_subname τ.property hp
  have hCB : ∀ σ ∈ C, IsForcingName B.P σ := fun σ hσ ↦ (hC σ hσ).mono hπ.inclusion
  let E := B.evaluationGraph C hCB
  let F : B.Model → B.Model := fun i ↦ {ν ∈ B.check C ; E ‘ ν = f ‘ i}
  have hF : ℒₛₑₜ-function₁ F := by
    have h : ℒₛₑₜ-relation (fun Y i : B.Model ↦ ∀ ν, ν ∈ Y ↔ ν ∈ B.check C ∧ E ‘ ν = f ‘ i) := by
      definability
    apply Language.Definable.of_iff h
    intro v
    rw [mem_ext_iff]
    simp only [F, mem_sep_iff]
    rfl
  have hn : ∀ i ∈ B.check γ, IsNonempty (F i) := by
    intro i hi
    have hx := function_value_mem hf hi
    obtain ⟨ν, p, _, hp, he⟩ := (B.mem_ofName_iff _ _).mp hx
    have hνC : ν.val ∈ C := mem_domain_of_kpair_mem hp
    refine ⟨B.check ν.val, mem_sep_iff.mpr ⟨(B.check_mem_iff _ _).mpr hνC, ?_⟩⟩
    exact (B.evaluationGraph_value C hCB ν.val hνC).trans he.symm
  obtain ⟨g, hgF, hgd, hg⟩ := ordinal_choice_for_definable_family
    (B.dependentChoiceAt_of_closed hDC hclosed) F hF hn
  let := hgF
  have hgtype : g ∈ B.check C ^ B.check γ := by
    apply mem_function.intro
    · intro z hz
      obtain ⟨i, ν, rfl⟩ := IsFunction.mem_eq_kpair hz
      have hi : i ∈ B.check γ := hgd ▸ mem_domain_of_kpair_mem hz
      exact kpair_mem_iff.mpr ⟨hi, (value_eq_of_kpair_mem hz) ▸ (mem_sep_iff.mp (hg i hi)).1⟩
    · intro i hi
      have hid : i ∈ domain g := hgd.symm ▸ hi
      exact ⟨g ‘ i, kpair_value_mem hid, fun y hy ↦ (value_eq_of_kpair_mem hy).symm⟩
  obtain ⟨s, hs, hsg⟩ := B.function_eq_check_of_closed hDC hclosed hgtype
  let := IsFunction.of_mem hs
  have hsd := domain_eq_of_mem_function hs
  have hsN : IsNameSequence A.P s := fun i hi ↦ hC _ (function_value_mem hs (hsd ▸ hi))
  have hsNB : IsNameSequence B.P s := fun i hi ↦ (hsN i hi).mono hπ.inclusion
  have hv : ∀ i : V, ∀ hi : i ∈ γ,
      B.ofName ⟨s ‘ i, hsNB i (hsd.symm ▸ hi)⟩ = f ‘ (B.check i) := by
    intro i hi
    have hgval := (mem_sep_iff.mp (hg (B.check i) ((B.check_mem_iff _ _).mpr hi))).2
    rw [← hsg, B.check_value (hsd.symm ▸ hi)] at hgval
    exact (B.evaluationGraph_value C hCB (s ‘ i) (function_value_mem hs hi)).symm.trans hgval
  have heq : B.sequenceValue s hsNB = f := by
    apply functions_eq_of_domain_values
    · rw [B.sequenceValue_domain, hsd, domain_eq_of_mem_function hf]
    · intro i hi
      rw [B.sequenceValue_domain, hsd] at hi
      obtain ⟨j, hj, rfl⟩ := (B.mem_check_iff γ i).mp hi
      exact (B.sequenceValue_value s hsNB (hsd.symm ▸ hj)).trans (hv j hj)
  exact ⟨s, hsN, hs, heq⟩

theorem retractionInclusion_function_of_closed {γ : V} [IsOrdinal γ]
    (hDC : InternalDependentChoiceAt γ)
    (hclosed : ∀ α, IsOrdinal α → α ⊆ γ → IsForcingClosedAt B.P B.R α)
    {X : A.Model} {f : B.Model}
    (hf : f ∈ retractionInclusion A B hπ hG X ^ B.check γ) :
    ∃ g ∈ X ^ A.check γ, retractionInclusion A B hπ hG g = f := by
  obtain ⟨τ, rfl⟩ := A.ofName_surjective X
  obtain ⟨s, hsN, _, heq⟩ := retractionInclusion_function_sequence_of_closed A B hπ hG
    hDC hclosed hf
  let j := retractionEmbedding A B hπ hG
  have himage : j (A.sequenceValue s hsN) = f :=
    (retractionInclusion_sequenceValue A B hπ hG hone s hsN).trans heq
  refine ⟨A.sequenceValue s hsN, ?_, himage⟩
  apply (j.function_iff _ _ _).mp
  change j (A.sequenceValue s hsN) ∈ j (A.ofName τ) ^ retractionInclusion A B hπ hG (A.check γ)
  rw [himage, retractionInclusion_check A B hπ hG hone]
  exact hf

end ForcingContext
end ZFVP
