import ZFVP.ModelTheory.SchmerlInternalCodedHullClosure
import ZFVP.Syntax.FormulaInduction
import ZFVP.Syntax.StandardTuples

/-! Countability of all internally finite formulas from countability of
the symbol sets. No hereditary countability of the symbols is assumed. -/

set_option autoImplicit false

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def finiteCodingOperation (i s : V) : V := by
  classical
  exact if i = 0 then s else ⟨s ‘ 0, s ‘ 1⟩ₖ

instance finiteCodingOperation_definable : ℒₛₑₜ-function₂[V] finiteCodingOperation := by
  classical
  have h : ℒₛₑₜ-relation₃[V] (fun y i s ↦
      (i = 0 ∧ y = s) ∨ (i ≠ 0 ∧ y = ⟨s ‘ 0, s ‘ 1⟩ₖ)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change (v 0 = if v 1 = 0 then v 2 else ⟨(v 2) ‘ 0, (v 2) ‘ 1⟩ₖ) ↔ _
  split <;> simp_all

noncomputable def finiteCodingEnvelope (A : V) : V :=
  finiteOperationHull (ω : V) finiteCodingOperation inferInstance ((ω : V) ∪ A)

theorem subset_finiteCodingEnvelope (A : V) : A ⊆ finiteCodingEnvelope A :=
  subset_trans (fun _ h ↦ mem_union_iff.mpr (Or.inr h)) (subset_finiteOperationHull _ _ _ _)

theorem omega_subset_finiteCodingEnvelope (A : V) : (ω : V) ⊆ finiteCodingEnvelope A :=
  subset_trans (fun _ h ↦ mem_union_iff.mpr (Or.inl h)) (subset_finiteOperationHull _ _ _ _)

theorem finiteCodingEnvelope_countable (hAC : InternalChoice V) {A : V}
    (hA : IsInternallyCountable A) : IsInternallyCountable (finiteCodingEnvelope A) :=
  finiteOperationHull_countable hAC internallyCountable_omega
    (internallyCountable_union internallyCountable_omega hA) _ _

theorem finiteCodingEnvelope_tuple {A s : V} (hs : s ∈ finiteSequences (finiteCodingEnvelope A)) :
    s ∈ finiteCodingEnvelope A := by
  have h := finiteOperationHull_closed (ω : V) finiteCodingOperation inferInstance ((ω : V) ∪ A)
    (i := 0) (by simp) hs
  rw [show finiteCodingOperation 0 s = s by simp [finiteCodingOperation]] at h
  exact h

theorem finiteCodingEnvelope_pair {A x y : V}
    (hx : x ∈ finiteCodingEnvelope A) (hy : y ∈ finiteCodingEnvelope A) :
    ⟨x, y⟩ₖ ∈ finiteCodingEnvelope A := by
  have hs : standardTuple ![x, y] ∈ finiteSequences (finiteCodingEnvelope A) :=
    (mem_finiteSequences_iff _ _).mpr ⟨2, by simp, standardTuple_mem_function _ (by simp [hx, hy])⟩
  have h := finiteOperationHull_closed (ω : V) finiteCodingOperation inferInstance ((ω : V) ∪ A)
    (i := 1) (by simp) hs
  have h0 : (standardTuple ![x, y]) ‘ (0 : V) = x := value_standardTuple ![x, y] 0
  have h1 : (standardTuple ![x, y]) ‘ (1 : V) = y := value_standardTuple ![x, y] 1
  rw [show finiteCodingOperation 1 (standardTuple ![x, y]) = ⟨x, y⟩ₖ by
    simp only [finiteCodingOperation, SetTheory.one_ne_zero, ↓reduceIte, h0, h1]] at h
  exact h

noncomputable def languageSyntaxEnvelope (L Γ : V) : V :=
  finiteCodingEnvelope ((functionSymbols L ∪ relationSymbols L) ∪ Γ)

theorem languageSyntaxEnvelope_natural (L Γ : V) {n : V} (hn : n ∈ (ω : V)) :
    n ∈ languageSyntaxEnvelope L Γ := omega_subset_finiteCodingEnvelope _ n hn

theorem languageSyntaxEnvelope_function {L Γ f : V} (hf : f ∈ functionSymbols L) :
    f ∈ languageSyntaxEnvelope L Γ :=
  subset_finiteCodingEnvelope _ f (mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inl hf))))

theorem languageSyntaxEnvelope_relation {L Γ r : V} (hr : r ∈ relationSymbols L) :
    r ∈ languageSyntaxEnvelope L Γ :=
  subset_finiteCodingEnvelope _ r (mem_union_iff.mpr (Or.inl (mem_union_iff.mpr (Or.inr hr))))

theorem languageSyntaxEnvelope_variable {L Γ x : V} (hx : x ∈ Γ) :
    x ∈ languageSyntaxEnvelope L Γ := subset_finiteCodingEnvelope _ x (mem_union_iff.mpr (Or.inr hx))

theorem termSet_subset_languageSyntaxEnvelope {L Γ n : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V)) :
    termSet L Γ n ⊆ languageSyntaxEnvelope L Γ := by
  apply termSet_minimal
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact finiteCodingEnvelope_pair (languageSyntaxEnvelope_natural _ _ (by simp))
      (languageSyntaxEnvelope_natural _ _ (IsOrdinal.toIsTransitive.mem_trans hi hn))
  · intro x hx
    exact finiteCodingEnvelope_pair (languageSyntaxEnvelope_natural _ _ (by simp))
      (languageSyntaxEnvelope_variable hx)
  · intro f hf args ha
    exact finiteCodingEnvelope_pair (languageSyntaxEnvelope_natural _ _ (by simp))
      (finiteCodingEnvelope_pair (languageSyntaxEnvelope_function hf)
        (finiteCodingEnvelope_tuple ((mem_finiteSequences_iff _ _).mpr
          ⟨_, hL.function_arity_natural hf, ha⟩)))

theorem atomicArguments_mem_languageSyntaxEnvelope {L Γ n r args : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (ha : IsAtomicArguments L Γ n r args) :
    r ∈ languageSyntaxEnvelope L Γ ∧ args ∈ languageSyntaxEnvelope L Γ := by
  have hsub := termSet_subset_languageSyntaxEnvelope (Γ := Γ) hL hn
  rcases ha with ⟨rfl, ha⟩ | ⟨s, hs, rfl, ha⟩
  · exact ⟨languageSyntaxEnvelope_natural _ _ (by simp [equalityToken]),
      finiteCodingEnvelope_tuple ((mem_finiteSequences_iff _ _).mpr
        ⟨2, by simp, mem_function_of_mem_function_of_subset ha hsub⟩)⟩
  · exact ⟨finiteCodingEnvelope_pair (languageSyntaxEnvelope_natural _ _ (by simp))
      (languageSyntaxEnvelope_relation hs),
      finiteCodingEnvelope_tuple ((mem_finiteSequences_iff _ _).mpr
        ⟨_, hL.relation_arity_natural hs, mem_function_of_mem_function_of_subset ha hsub⟩)⟩

theorem formulaFamily_subset_languageSyntaxEnvelope {L Γ : V} (hL : IsLanguageCode L) :
    formulaFamily L Γ ⊆ (ω : V) ×ˢ languageSyntaxEnvelope L Γ := by
  apply formulaFamily_minimal
  intro n hn
  have htag (k : ℕ) : (k : V) ∈ languageSyntaxEnvelope L Γ := languageSyntaxEnvelope_natural _ _ (by simp)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨kpair_mem_iff.mpr ⟨hn, finiteCodingEnvelope_pair (htag 0) (htag 0)⟩,
      kpair_mem_iff.mpr ⟨hn, finiteCodingEnvelope_pair (htag 1) (htag 0)⟩⟩
  · intro r args ha
    obtain ⟨hr, hargs⟩ := atomicArguments_mem_languageSyntaxEnvelope hL hn ha
    exact ⟨kpair_mem_iff.mpr ⟨hn, finiteCodingEnvelope_pair (htag 2) (finiteCodingEnvelope_pair hr hargs)⟩,
      kpair_mem_iff.mpr ⟨hn, finiteCodingEnvelope_pair (htag 3) (finiteCodingEnvelope_pair hr hargs)⟩⟩
  · intro φ ψ hφ hψ
    have hφ := (kpair_mem_iff.mp hφ).2
    have hψ := (kpair_mem_iff.mp hψ).2
    exact ⟨kpair_mem_iff.mpr ⟨hn, finiteCodingEnvelope_pair (htag 4) (finiteCodingEnvelope_pair hφ hψ)⟩,
      kpair_mem_iff.mpr ⟨hn, finiteCodingEnvelope_pair (htag 5) (finiteCodingEnvelope_pair hφ hψ)⟩⟩
  · intro φ hφ
    have hφ := (kpair_mem_iff.mp hφ).2
    exact ⟨kpair_mem_iff.mpr ⟨hn, finiteCodingEnvelope_pair (htag 6) hφ⟩,
      kpair_mem_iff.mpr ⟨hn, finiteCodingEnvelope_pair (htag 7) hφ⟩⟩

theorem formulaFamily_countable (hAC : InternalChoice V) {L Γ : V}
    (hL : IsLanguageCode L) (hF : IsInternallyCountable (functionSymbols L))
    (hR : IsInternallyCountable (relationSymbols L)) (hΓ : IsInternallyCountable Γ) :
    IsInternallyCountable (formulaFamily L Γ) :=
  internallyCountable_subset
    ((prod_cardLE_prod internallyCountable_omega
      (finiteCodingEnvelope_countable hAC (internallyCountable_union (internallyCountable_union hF hR) hΓ))).trans
      omega_prod_cardLE_omega) (formulaFamily_subset_languageSyntaxEnvelope hL)

end ZFVP.Schmerl
