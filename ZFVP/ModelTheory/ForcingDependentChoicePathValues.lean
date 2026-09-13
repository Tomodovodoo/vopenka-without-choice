import ZFVP.ModelTheory.ForcingModelSequences
import ZFVP.ModelTheory.ForcingFunctionValues
import ZFVP.SetTheory.ForcingDependentChoicePaths

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem dependentChoiceNext_truth (S : ForcingContext V) (τA τB : ForcingName S.P)
    (s : V) (hs : IsNameSequence S.P (subnameSequence s)) (σ : ForcingName S.P) :
    (∃ q ∈ S.G, ForcesDependentChoiceNext S.P S.R S.one τA.val τB.val s q σ.val) ↔
      S.ofName σ ∈ S.ofName τA ∧
        ⟨S.sequenceValue (subnameSequence s) hs, S.ofName σ⟩ₖ ∈ S.ofName τB := by
  let t : ForcingName S.P := ⟨sequenceName S.one (subnameSequence s), sequenceName_isName S.top.1 hs⟩
  exact (S.formula_truth dependentChoiceNextFormula ![t, σ, τA, τB]).symm.trans
    (eval_dependentChoiceNextFormula _)

theorem sequenceValue_subname_restrict (S : ForcingContext V) {s A : V} [IsFunction s]
    (hs : IsNameSequence S.P (subnameSequence s)) (hA : A ⊆ domain s)
    (ht : IsNameSequence S.P (subnameSequence (s ↾ A))) :
    S.sequenceValue (subnameSequence (s ↾ A)) ht =
      (S.sequenceValue (subnameSequence s) hs) ↾ (S.check A) := by
  have hAs : A ⊆ domain (subnameSequence s) := by rwa [subnameSequence_domain]
  calc
    _ = S.sequenceValue ((subnameSequence s) ↾ A) (hs.restrict hAs) :=
      congrArg S.ofName (Subtype.ext (congrArg (sequenceName S.one) (subnameSequence_restrict hA)))
    _ = _ := S.sequenceValue_restrict hs hAs

theorem dependentChoiceForcingPath_value (S : ForcingContext V) (τA τB : ForcingName S.P)
    {p γ α s : V} [IsOrdinal α]
    (hs : IsDependentChoicePath (S.P ×ˢ domain τA.val)
      (dependentChoiceForcingRelation S.P S.R S.one τA.val τB.val p γ) α s)
    (hG : ∀ i ∈ α, kpair.π₁ (s ‘ i) ∈ S.G) :
    IsDependentChoicePath (S.ofName τA) (S.ofName τB) (S.check α)
      (S.sequenceValue (subnameSequence s) (subnameSequence_isNameSequence τA.property hs.1)) := by
  let := IsFunction.of_mem hs.1
  have hN := subnameSequence_isNameSequence τA.property hs.1
  have hd : domain (subnameSequence s) = α := (subnameSequence_domain s).trans (domain_eq_of_mem_function hs.1)
  have hni (i : V) (hi : i ∈ α) : IsForcingName S.P (kpair.π₂ (s ‘ i)) := by
    have hh := hN i (hd.symm ▸ hi)
    rwa [subnameSequence_value (by rw [domain_eq_of_mem_function hs.1]; exact hi)] at hh
  have hprefix (i : V) (hi : i ∈ α) : IsNameSequence S.P (subnameSequence (s ↾ i)) :=
    subnameSequence_isNameSequence τA.property
      (function_restrict_mem hs.1 (IsOrdinal.toIsTransitive.transitive _ hi))
  have hstep (i : V) (hi : i ∈ α) :
      S.ofName ⟨kpair.π₂ (s ‘ i), hni i hi⟩ ∈ S.ofName τA ∧
      ⟨S.sequenceValue (subnameSequence (s ↾ i)) (hprefix i hi),
        S.ofName ⟨kpair.π₂ (s ‘ i), hni i hi⟩⟩ₖ ∈ S.ofName τB := by
    apply (S.dependentChoiceNext_truth τA τB _ (hprefix i hi) _).mp
    exact ⟨kpair.π₁ (s ‘ i), hG i hi,
      ((pair_mem_dependentChoiceForcingRelation _ _ _ _ _ _ _ _ _).mp (hs.2 i hi)).2.2.2.2⟩
  have hvalue (i : V) (hi : i ∈ α) :
      (S.sequenceValue (subnameSequence s) hN) ‘ (S.check i) =
        S.ofName ⟨kpair.π₂ (s ‘ i), hni i hi⟩ := by
    rw [S.sequenceValue_value _ _ (hd.symm ▸ hi)]
    exact congrArg S.ofName (Subtype.ext (subnameSequence_value
      (by rw [domain_eq_of_mem_function hs.1]; exact hi)))
  constructor
  · have hf := S.sequenceValue_mem_function (subnameSequence s) hN (A := S.ofName τA) (by
      intro i hi
      have hiα : i ∈ α := hd ▸ hi
      have he : S.ofName ⟨(subnameSequence s) ‘ i, hN i hi⟩ =
          S.ofName ⟨kpair.π₂ (s ‘ i), hni i hiα⟩ :=
        congrArg S.ofName (Subtype.ext (subnameSequence_value
          (by rw [domain_eq_of_mem_function hs.1]; exact hiα)))
      rw [he]
      exact (hstep i hiα).1)
    simpa only [hd] using hf
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := (S.mem_check_iff α a).mp ha
    have hsub : i ⊆ domain s := by
      rw [domain_eq_of_mem_function hs.1]
      exact IsOrdinal.toIsTransitive.transitive _ hi
    have hh := (hstep i hi).2
    rw [S.sequenceValue_subname_restrict hN hsub (hprefix i hi)] at hh
    rw [hvalue i hi]
    exact hh

end ForcingContext
end ZFVP
