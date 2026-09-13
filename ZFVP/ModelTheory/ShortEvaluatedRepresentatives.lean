import ZFVP.ModelTheory.ForcingModelSequences
import ZFVP.ModelTheory.ForcingModelEvaluation
import ZFVP.ModelTheory.ForcingDependentChoiceTransfer
import ZFVP.ModelTheory.ForcingClosedSequences
import ZFVP.SetTheory.OrdinalIndexedChoice

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

set_option maxHeartbeats 1200000 in
/-- Lift an ordinal sequence of evaluated names to a ground sequence of representatives. -/
theorem sequenceValue_representative_of_noNewSequences (S : ForcingContext V)
    {γ C : V} [IsOrdinal γ] (hC : ∀ σ ∈ C, IsForcingName S.P σ)
    (hDC : InternalDependentChoiceAt (S.check γ))
    (hno : ∀ g : S.Model, g ∈ S.check C ^ S.check γ →
      ∃ t ∈ C ^ γ, S.check t = g)
    {f : S.Model} (hf : f ∈ range (S.evaluationGraph C hC) ^ S.check γ) :
    ∃ s, ∃ hsN : IsNameSequence S.P s, s ∈ C ^ γ ∧
      S.sequenceValue s hsN = f := by
  let := IsFunction.of_mem hf
  let E := S.evaluationGraph C hC
  let F : S.Model → S.Model := fun i ↦ {ν ∈ S.check C ; E ‘ ν = f ‘ i}
  have hF : ℒₛₑₜ-function₁ F := by
    have h : ℒₛₑₜ-relation (fun Y i : S.Model ↦ ∀ ν, ν ∈ Y ↔ ν ∈ S.check C ∧ E ‘ ν = f ‘ i) := by
      definability
    apply Language.Definable.of_iff h
    intro v
    rw [mem_ext_iff]
    simp only [F, mem_sep_iff]
    rfl
  have hn : ∀ i ∈ S.check γ, IsNonempty (F i) := by
    intro i hi
    have hx := function_value_mem hf hi
    obtain ⟨x, hx⟩ := mem_range_iff.mp hx
    obtain ⟨ν, hνC, _, he⟩ := (S.pair_mem_evaluationGraph_iff C hC x (f ‘ i)).mp hx
    refine ⟨S.check ν, mem_sep_iff.mpr ⟨(S.check_mem_iff _ _).mpr hνC, ?_⟩⟩
    exact (S.evaluationGraph_value C hC ν hνC).trans he.symm
  obtain ⟨g, hgF, hgd, hg⟩ := ordinal_choice_for_definable_family
    hDC F hF hn
  let := hgF
  have hgtype : g ∈ S.check C ^ S.check γ := by
    apply mem_function.intro
    · intro z hz
      obtain ⟨i, ν, rfl⟩ := IsFunction.mem_eq_kpair hz
      have hi : i ∈ S.check γ := hgd ▸ mem_domain_of_kpair_mem hz
      exact kpair_mem_iff.mpr ⟨hi, (value_eq_of_kpair_mem hz) ▸ (mem_sep_iff.mp (hg i hi)).1⟩
    · intro i hi
      have hid : i ∈ domain g := hgd.symm ▸ hi
      exact ⟨g ‘ i, kpair_value_mem hid, fun y hy ↦ (value_eq_of_kpair_mem hy).symm⟩
  obtain ⟨s, hs, hsg⟩ := hno g hgtype
  let := IsFunction.of_mem hs
  have hsd := domain_eq_of_mem_function hs
  have hsN : IsNameSequence S.P s := fun i hi ↦ hC _ (function_value_mem hs (hsd ▸ hi))
  have hv : ∀ i : V, ∀ hi : i ∈ γ,
      S.ofName ⟨s ‘ i, hsN i (hsd.symm ▸ hi)⟩ = f ‘ (S.check i) := by
    intro i hi
    have hgval := (mem_sep_iff.mp (hg (S.check i) ((S.check_mem_iff _ _).mpr hi))).2
    rw [← hsg, S.check_value (hsd.symm ▸ hi)] at hgval
    exact (S.evaluationGraph_value C hC (s ‘ i) (function_value_mem hs hi)).symm.trans hgval
  have heq : S.sequenceValue s hsN = f := by
    apply functions_eq_of_domain_values
    · rw [S.sequenceValue_domain, hsd, domain_eq_of_mem_function hf]
    · intro i hi
      rw [S.sequenceValue_domain, hsd] at hi
      obtain ⟨j, hj, rfl⟩ := (S.mem_check_iff γ i).mp hi
      exact (S.sequenceValue_value s hsN (hsd.symm ▸ hj)).trans (hv j hj)
  exact ⟨s, hsN, hs, heq⟩

/-- Closed forcing supplies both choice and the absence of new ground sequences. -/
theorem sequenceValue_representative_of_closed (S : ForcingContext V)
    {γ C : V} [IsOrdinal γ] (hC : ∀ σ ∈ C, IsForcingName S.P σ)
    (hDC : InternalDependentChoiceAt γ)
    (hclosed : ∀ α, IsOrdinal α → α ⊆ γ → IsForcingClosedAt S.P S.R α)
    {f : S.Model} (hf : f ∈ range (S.evaluationGraph C hC) ^ S.check γ) :
    ∃ s, ∃ hsN : IsNameSequence S.P s, s ∈ C ^ γ ∧
      S.sequenceValue s hsN = f :=
  S.sequenceValue_representative_of_noNewSequences hC
    (S.dependentChoiceAt_of_closed hDC hclosed)
    (fun _ hg ↦ S.function_eq_check_of_closed hDC hclosed hg) hf

end ForcingContext
end ZFVP
