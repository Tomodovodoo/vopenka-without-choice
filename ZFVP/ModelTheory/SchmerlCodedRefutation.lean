import ZFVP.ModelTheory.SchmerlCodedKeislerSoundness

/-! A coded realization of a refutation's countable support contradicts the
actual syntactic refutation, using internal uncountability throughout. -/
namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory ZFVP.Schmerl
variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Λ : Language} [Λ.Eq] {L H M : V}
  {F : ∀ {k}, Λ.Func k → V} {R : ∀ {k}, Λ.Rel k → V}
  {C : {n : ℕ} → Formula Λ n → V} {A : Set (Σ n, Formula Λ n)}

theorem IsFragmentCoding.false_of_refutation_support (h : IsFragmentCoding L H F R C A)
    (hω : HasStandardOmega V) (hAC : InternalChoice V) (hM : IsStructureCode L M)
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧ (functionArities L) ‘ (F f) = (k : V))
    (hR : ∀ k (r : Λ.Rel k), R r ∈ relationSymbols L ∧ (relationArities L) ‘ (R r) = (k : V))
    (hEq : @Structure.Eq Λ (CodedDomain M) (codedFoundationStructure hM F R hF) inferInstance)
    {Γ : Set (Sentence Λ)} (hs : KeislerSoundOn.{u} A Γ (.neg (.fo .verum : Sentence Λ)))
    (hΓmem : ∀ ψ ∈ Γ, ⟨0, ψ⟩ ∈ A)
    (hΓ : ∀ ψ ∈ Γ, Holds L H M (0 : V) (C ψ) ∅) : False := by
  let := codedFoundationStructure hM F R hF
  let := codedDomain_nonempty hM
  let := hEq
  have hQ := h.quantifierLawsOn hω hAC hM hF hR
  have hΓ' : ∀ ψ ∈ Γ, Formula.EvalWithQ (InternalQ M) ψ ![] := by
    intro ψ hψ
    exact (h.holds_iff_evalWithQ hω hM hF hR ψ (hΓmem ψ hψ) ![]).mp (hΓ ψ hψ)
  exact hs (InternalQ M) hQ hΓ' ![] trivial

end ZFVP.Infinitary.Internal
