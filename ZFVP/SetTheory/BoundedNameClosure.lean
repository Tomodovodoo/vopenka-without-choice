import ZFVP.SetTheory.NameClosureIteration
import ZFVP.SetTheory.BoundedCodingPrimitives
import ZFVP.SetTheory.BoundedNaturals

/-! Bounded certificates for the omega iteration computing name closure. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedSubnameStepFormula : SetTheorySemisentence 3 :=
  “T Y X. !isSubsetOf Y T ∧ ∀ u ∈ T,
    u ∈ Y ↔ u ∈ X ∨ ∃ σ ∈ X, ∃ p ∈ T, !boundedPairMemberFormula σ u p”

theorem boundedSubnameStepFormula_bounded : IsBoundedSetFormula boundedSubnameStepFormula := by
  exact .and (isSubsetOf_bounded.subst _) (.all (.bvar 0)
    (.and (.or (.nrel _ _) (.or (.rel _ _) (.exs (.bvar 3) (.exs (.bvar 2)
      (boundedPairMemberFormula_bounded.subst _)))))
      (.or (.and (.nrel _ _) (.all (.bvar 3) (.all (.bvar 2)
        (boundedPairMemberFormula_bounded.subst _).neg))) (.rel _ _))))

def boundedSubnameInitialFormula : SetTheorySemisentence 4 :=
  “T w f τ. ∃ z ∈ w, !boundedEmptyFormula z ∧ ∃ X ∈ T,
    !boundedPairMemberFormula f z X ∧ !boundedSingletonFormula X τ”

def boundedSubnameSuccessorsFormula : SetTheorySemisentence 3 :=
  “T w f. ∀ n ∈ w, ∃ m ∈ w, !boundedSuccFormula m n ∧ ∃ X ∈ T, ∃ Y ∈ T,
    !boundedPairMemberFormula f n X ∧ !boundedPairMemberFormula f m Y ∧ !boundedSubnameStepFormula T Y X”

def boundedSubnameIterationFormula : SetTheorySemisentence 4 :=
  “T w f τ. !boundedFunctionFormula f w T ∧ !boundedSubnameInitialFormula T w f τ ∧
    !boundedSubnameSuccessorsFormula T w f”

def boundedIterationUnionFormula : SetTheorySemisentence 4 :=
  “C T w f. !isSubsetOf C T ∧ ∀ u ∈ T,
    u ∈ C ↔ ∃ n ∈ w, ∃ X ∈ T, !boundedPairMemberFormula f n X ∧ u ∈ X”

theorem boundedSubnameInitialFormula_bounded : IsBoundedSetFormula boundedSubnameInitialFormula :=
  .exs (.bvar 1) (.and (boundedEmptyFormula_bounded.subst _) (.exs (.bvar 1)
    (.and (boundedPairMemberFormula_bounded.subst _) (boundedSingletonFormula_bounded.subst _))))

theorem boundedSubnameSuccessorsFormula_bounded : IsBoundedSetFormula boundedSubnameSuccessorsFormula :=
  .all (.bvar 1) (.exs (.bvar 2) (.and (boundedSuccFormula_bounded.subst _)
    (.exs (.bvar 2) (.exs (.bvar 3) (.and (boundedPairMemberFormula_bounded.subst _)
      (.and (boundedPairMemberFormula_bounded.subst _) (boundedSubnameStepFormula_bounded.subst _)))))))

theorem boundedSubnameIterationFormula_bounded : IsBoundedSetFormula boundedSubnameIterationFormula :=
  .and (boundedFunctionFormula_bounded.subst _) (.and (boundedSubnameInitialFormula_bounded.subst _)
    (boundedSubnameSuccessorsFormula_bounded.subst _))

theorem boundedIterationUnionFormula_bounded : IsBoundedSetFormula boundedIterationUnionFormula :=
  .and (isSubsetOf_bounded.subst _) (.all (.bvar 1)
    (.and (.or (.nrel _ _) (.exs (.bvar 3) (.exs (.bvar 3)
      (.and (boundedPairMemberFormula_bounded.subst _) (.rel _ _)))))
      (.or (.all (.bvar 3) (.all (.bvar 3) (.or (boundedPairMemberFormula_bounded.subst _).neg (.nrel _ _))))
        (.rel _ _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedSubnameStepFormula {T X : V} [hT : IsTransitive T] (hX : X ∈ T) (Y : V) :
    boundedSubnameStepFormula.Evalb ![T, Y, X] ↔ Y = subnameStep X := by
  have hxT := hT.transitive X hX
  have hg (u : V) : (∃ σ ∈ X, ∃ p ∈ T, ⟨u, p⟩ₖ ∈ σ) ↔ ∃ σ ∈ X, u ∈ domain σ := by
    constructor
    · rintro ⟨σ, hσ, p, _, hp⟩
      exact ⟨σ, hσ, mem_domain_of_kpair_mem hp⟩
    · rintro ⟨σ, hσ, hu⟩
      obtain ⟨p, hp⟩ := mem_domain_iff.mp hu
      have hpair := hT.mem_trans hp (hxT σ hσ)
      have hdouble : ({u, p} : V) ∈ T := hT.mem_trans (by simp [kpair]) hpair
      exact ⟨σ, hσ, p, hT.mem_trans (by simp) hdouble, hp⟩
  have hstep : subnameStep X ⊆ T := subnameStep_subset hxT (transitive_subnameClosed hT)
  have hev : boundedSubnameStepFormula.Evalb ![T, Y, X] ↔
      Y ⊆ T ∧ ∀ u ∈ T, u ∈ Y ↔ u ∈ X ∨ ∃ σ ∈ X, ∃ p ∈ T, ⟨u, p⟩ₖ ∈ σ := by
    simp [boundedSubnameStepFormula]
  rw [hev]
  simp only [hg, ← mem_subnameStep_iff]
  constructor
  · rintro ⟨hY, he⟩
    apply mem_ext
    intro u
    exact ⟨fun hu ↦ (he u (hY u hu)).mp hu, fun hu ↦ (he u (hstep u hu)).mpr hu⟩
  · rintro rfl
    exact ⟨hstep, fun _ _ ↦ Iff.rfl⟩

theorem eval_boundedSubnameInitialFormula {T f : V} (hf : f ∈ T ^ (ω : V)) (τ : V) :
    boundedSubnameInitialFormula.Evalb ![T, ω, f, τ] ↔ f ‘ (0 : V) = {τ} := by
  let := IsFunction.of_mem hf
  simp [boundedSubnameInitialFormula, kpair_mem_iff_value, domain_eq_of_mem_function hf]
  change ({τ} ∈ T ∧ f ‘ (0 : V) = {τ}) ↔ f ‘ (0 : V) = {τ}
  exact ⟨And.right, fun h ↦ ⟨h ▸ function_value_mem hf (show (0 : V) ∈ (ω : V) by simp), h⟩⟩

theorem eval_boundedSubnameSuccessorsFormula {T f : V} [IsTransitive T] (hf : f ∈ T ^ (ω : V)) :
    boundedSubnameSuccessorsFormula.Evalb ![T, ω, f] ↔
      ∀ n ∈ (ω : V), f ‘ (succ n) = subnameStep (f ‘ n) := by
  let := IsFunction.of_mem hf
  have hev : boundedSubnameSuccessorsFormula.Evalb ![T, ω, f] ↔
      ∀ n ∈ (ω : V), ∃ m ∈ (ω : V), m = succ n ∧ ∃ X ∈ T, ∃ Y ∈ T,
        ⟨n, X⟩ₖ ∈ f ∧ ⟨m, Y⟩ₖ ∈ f ∧ boundedSubnameStepFormula.Evalb ![T, Y, X] := by
    simp [boundedSubnameSuccessorsFormula]
  rw [hev]
  constructor
  · intro h n hn
    obtain ⟨_, _, rfl, X, hX, Y, _, hnX, hmY, hstep⟩ := h n hn
    rw [value_eq_of_kpair_mem hnX, value_eq_of_kpair_mem hmY]
    exact (eval_boundedSubnameStepFormula hX Y).mp hstep
  · intro h n hn
    have hm := ω_succ_closed hn
    refine ⟨succ n, hm, rfl, f ‘ n, function_value_mem hf hn, f ‘ (succ n),
      function_value_mem hf hm, ?_, ?_, ?_⟩
    · exact kpair_value_mem (domain_eq_of_mem_function hf ▸ hn)
    · exact kpair_value_mem (domain_eq_of_mem_function hf ▸ hm)
    · exact (eval_boundedSubnameStepFormula (function_value_mem hf hn) _).mpr (h n hn)

theorem eval_boundedSubnameIterationFormula {T : V} [IsTransitive T] (f τ : V) :
    boundedSubnameIterationFormula.Evalb ![T, ω, f, τ] ↔ f ∈ T ^ (ω : V) ∧ f = subnameIterationGraph τ := by
  have hev : boundedSubnameIterationFormula.Evalb ![T, ω, f, τ] ↔
      f ∈ T ^ (ω : V) ∧ boundedSubnameInitialFormula.Evalb ![T, ω, f, τ] ∧
        boundedSubnameSuccessorsFormula.Evalb ![T, ω, f] := by
    simp [boundedSubnameIterationFormula]
  rw [hev]
  constructor
  · rintro ⟨hf, hz, hs⟩
    let := IsFunction.of_mem hf
    exact ⟨hf, subnameIterationGraph_eq_of_recursion (domain_eq_of_mem_function hf)
      ((eval_boundedSubnameInitialFormula hf τ).mp hz) ((eval_boundedSubnameSuccessorsFormula hf).mp hs)⟩
  · rintro ⟨hf, rfl⟩
    refine ⟨hf, (eval_boundedSubnameInitialFormula hf τ).mpr ?_,
      (eval_boundedSubnameSuccessorsFormula hf).mpr ?_⟩
    · rw [subnameIterationGraph_value τ (by simp), subnameIteration_zero]
    · intro n hn
      rw [subnameIterationGraph_value τ hn, subnameIterationGraph_value τ (ω_succ_closed hn), subnameIteration_succ τ hn]

theorem eval_boundedIterationUnionFormula {T w f : V} [hT : IsTransitive T]
    (hf : f ∈ T ^ w) (C : V) :
    boundedIterationUnionFormula.Evalb ![C, T, w, f] ↔ C = ⋃ˢ range f := by
  let := IsFunction.of_mem hf
  have hrg : ⋃ˢ range f ⊆ T := by
    intro u hu
    obtain ⟨X, hX, hu⟩ := mem_sUnion_iff.mp hu
    exact hT.mem_trans hu (range_subset_of_mem_function hf X hX)
  have he (u : V) : (∃ n ∈ w, ∃ X ∈ T, ⟨n, X⟩ₖ ∈ f ∧ u ∈ X) ↔ u ∈ ⋃ˢ range f := by
    constructor
    · rintro ⟨n, _, X, _, hp, hu⟩
      exact mem_sUnion_iff.mpr ⟨X, mem_range_of_kpair_mem hp, hu⟩
    · intro hu
      obtain ⟨X, hX, hu⟩ := mem_sUnion_iff.mp hu
      obtain ⟨n, hp⟩ := mem_range_iff.mp hX
      exact ⟨n, domain_eq_of_mem_function hf ▸ mem_domain_of_kpair_mem hp, X,
        range_subset_of_mem_function hf X (mem_range_of_kpair_mem hp), hp, hu⟩
  have hev : boundedIterationUnionFormula.Evalb ![C, T, w, f] ↔
      C ⊆ T ∧ ∀ u ∈ T, u ∈ C ↔ ∃ n ∈ w, ∃ X ∈ T, ⟨n, X⟩ₖ ∈ f ∧ u ∈ X := by
    simp [boundedIterationUnionFormula]
  rw [hev]
  simp only [he]
  constructor
  · rintro ⟨hC, hc⟩
    apply mem_ext
    intro u
    exact ⟨fun hu ↦ (hc u (hC u hu)).mp hu, fun hu ↦ (hc u (hrg u hu)).mpr hu⟩
  · rintro rfl
    exact ⟨hrg, fun _ _ ↦ Iff.rfl⟩

end ZFVP
