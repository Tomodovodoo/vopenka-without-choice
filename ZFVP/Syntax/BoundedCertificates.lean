import ZFVP.SetTheory.FiniteDerivations
import ZFVP.Syntax.MembershipAtomicSyntax

/-! Internally finite derivations of bounded formula codes.
Each step checks a constructor and previously derived codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def BoundedDerivationStep (S q : V) : Prop := ∃ n ∈ (ω : V), ∃ φ, q = ⟨n, φ⟩ₖ ∧
  (φ = truthCode ∨ φ = falsityCode ∨
    (∃ r args, IsMembershipAtomicArguments n r args ∧ (φ = atomCode r args ∨ φ = negAtomCode r args)) ∨
    (∃ ψ χ, ⟨n, ψ⟩ₖ ∈ S ∧ ⟨n, χ⟩ₖ ∈ S ∧ (φ = andCode ψ χ ∨ φ = orCode ψ χ)) ∨
    ∃ i ∈ n, ∃ ψ, ⟨succ n, ψ⟩ₖ ∈ S ∧ (φ = boundedAllCode i ψ ∨ φ = boundedExistsCode i ψ))

instance boundedDerivationStep_definable : ℒₛₑₜ-relation[V] BoundedDerivationStep := by
  unfold BoundedDerivationStep truthCode falsityCode
  definability

theorem boundedDerivationStep_mono {S T q : V} (hST : S ⊆ T)
    (h : BoundedDerivationStep S q) : BoundedDerivationStep T q := by
  obtain ⟨n, hn, φ, rfl, h⟩ := h
  refine ⟨n, hn, φ, rfl, ?_⟩
  rcases h with h | h | h | ⟨ψ, χ, hψ, hχ, h⟩ | ⟨i, hi, ψ, hψ, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ψ, χ, hST _ hψ, hST _ hχ, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, ψ, hST _ hψ, h⟩)))

theorem boundedDerivationStep_closed {S Q q : V} (hQ : IsBoundedFormulaClosed Q) (hS : S ⊆ Q)
    (h : BoundedDerivationStep S q) : q ∈ Q := by
  obtain ⟨n, hn, φ, rfl, h⟩ := h
  have hc := hQ n hn
  rcases h with rfl | rfl | ⟨r, args, ha, h⟩ | ⟨ψ, χ, hψ, hχ, h⟩ | ⟨i, hi, ψ, hψ, h⟩
  · exact hc.1.1
  · exact hc.1.2
  · have hv := hc.2.1 r args ((membershipAtomicArguments_iff hn).mpr ha)
    exact h.elim (fun h ↦ h ▸ hv.1) (fun h ↦ h ▸ hv.2)
  · have hv := hc.2.2.1 ψ χ (hS _ hψ) (hS _ hχ)
    exact h.elim (fun h ↦ h ▸ hv.1) (fun h ↦ h ▸ hv.2)
  · have hv := hc.2.2.2 i hi ψ (hS _ hψ)
    exact h.elim (fun h ↦ h ▸ hv.1) (fun h ↦ h ▸ hv.2)

def IsBoundedDerivation (s : V) : Prop :=
  IsFiniteDerivation BoundedDerivationStep (syntaxUniverse (membershipLanguageCode : V) ∅) s

instance isBoundedDerivation_definable : ℒₛₑₜ-predicate[V] IsBoundedDerivation :=
  isFiniteDerivation_definable BoundedDerivationStep (by definability) _

def HasBoundedDerivation (q : V) : Prop := ∃ s : V, IsBoundedDerivation s ∧ q ∈ range s

instance hasBoundedDerivation_definable : ℒₛₑₜ-predicate[V] HasBoundedDerivation := by
  unfold HasBoundedDerivation
  definability

theorem boundedDerivation_sound {s : V} (hs : IsBoundedDerivation s) : range s ⊆ (boundedFormulaFamily : V) :=
  finiteDerivation_sound BoundedDerivationStep (by definability) _ _
    (fun _ _ hS h ↦ boundedDerivationStep_closed boundedFormulaFamily_closed hS h) s hs

theorem hasBoundedDerivation_extend {q s : V} (hs : IsBoundedDerivation s)
    (hq : q ∈ syntaxUniverse (membershipLanguageCode : V) ∅) (hr : BoundedDerivationStep (range s) q) :
    HasBoundedDerivation q := by
  obtain ⟨t, ht, hqt, _⟩ := finiteDerivation_extend BoundedDerivationStep hs hq hr
  exact ⟨t, ht, hqt⟩

theorem hasBoundedDerivation_base {q : V} (hq : q ∈ syntaxUniverse (membershipLanguageCode : V) ∅)
    (hr : BoundedDerivationStep ∅ q) : HasBoundedDerivation q :=
  hasBoundedDerivation_extend (isFiniteDerivation_empty BoundedDerivationStep _) hq (by simpa using hr)

theorem boundedFormulaFamily_derivation : ∀ q ∈ (boundedFormulaFamily : V), HasBoundedDerivation q := by
  have hU : ∀ q ∈ (boundedFormulaFamily : V), q ∈ syntaxUniverse membershipLanguageCode ∅ :=
    fun q hq ↦ formulaFamily_subset_syntaxUniverse _ _ q (boundedFormulaFamily_subset q hq)
  refine boundedFormulaFamily_induction HasBoundedDerivation (by definability) ?_ ?_ ?_ ?_
  · intro n hn
    have hc := (boundedFormulaFamily_closed (V := V) n hn).1
    exact ⟨hasBoundedDerivation_base (hU _ hc.1) ⟨n, hn, truthCode, rfl, Or.inl rfl⟩,
      hasBoundedDerivation_base (hU _ hc.2) ⟨n, hn, falsityCode, rfl, Or.inr (Or.inl rfl)⟩⟩
  · intro n hn r args ha
    have hc := (boundedFormulaFamily_closed (V := V) n hn).2.1 r args ha
    have ha' := (membershipAtomicArguments_iff hn).mp ha
    exact ⟨hasBoundedDerivation_base (hU _ hc.1)
        ⟨n, hn, atomCode r args, rfl, Or.inr (Or.inr (Or.inl ⟨r, args, ha', Or.inl rfl⟩))⟩,
      hasBoundedDerivation_base (hU _ hc.2)
        ⟨n, hn, negAtomCode r args, rfl, Or.inr (Or.inr (Or.inl ⟨r, args, ha', Or.inr rfl⟩))⟩⟩
  · intro n hn φ ψ hφ hψ ihφ ihψ
    have hc := (boundedFormulaFamily_closed (V := V) n hn).2.2.1 φ ψ hφ hψ
    obtain ⟨s, hs, hφs⟩ := ihφ
    obtain ⟨t, ht, hψt⟩ := ihψ
    obtain ⟨u, hu, hsu, htu⟩ := finiteDerivations_merge BoundedDerivationStep (by definability)
      (fun _ _ _ hST h ↦ boundedDerivationStep_mono hST h) hs ht
    exact ⟨hasBoundedDerivation_extend hu (hU _ hc.1)
        ⟨n, hn, andCode φ ψ, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, ψ, hsu _ hφs, htu _ hψt, Or.inl rfl⟩)))⟩,
      hasBoundedDerivation_extend hu (hU _ hc.2)
        ⟨n, hn, orCode φ ψ, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, ψ, hsu _ hφs, htu _ hψt, Or.inr rfl⟩)))⟩⟩
  · intro n hn i hi φ hφ ih
    have hc := (boundedFormulaFamily_closed (V := V) n hn).2.2.2 i hi φ hφ
    obtain ⟨s, hs, hφs⟩ := ih
    exact ⟨hasBoundedDerivation_extend hs (hU _ hc.1)
        ⟨n, hn, boundedAllCode i φ, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, φ, hφs, Or.inl rfl⟩)))⟩,
      hasBoundedDerivation_extend hs (hU _ hc.2)
        ⟨n, hn, boundedExistsCode i φ, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, φ, hφs, Or.inr rfl⟩)))⟩⟩

theorem isBoundedFormulaCode_iff_derivation (n φ : V) :
    IsBoundedFormulaCode n φ ↔ ∃ s : V, IsBoundedDerivation s ∧ ⟨n, φ⟩ₖ ∈ range s := by
  constructor
  · exact boundedFormulaFamily_derivation _
  · rintro ⟨s, hs, hφ⟩
    exact boundedDerivation_sound hs _ hφ

def IsBoundedCertificate (s : V) : Prop :=
  IsFunction s ∧ domain s ∈ (ω : V) ∧ ∀ i ∈ domain s, BoundedDerivationStep (range (s ↾ i)) (s ‘ i)

instance isBoundedCertificate_definable : ℒₛₑₜ-predicate[V] IsBoundedCertificate := by
  unfold IsBoundedCertificate
  definability

theorem isBoundedCertificate_iff (s : V) : IsBoundedCertificate s ↔
    IsFiniteDerivation BoundedDerivationStep (range s) s := by
  constructor
  · rintro ⟨hs, hn, hstep⟩
    let := hs
    exact ⟨(mem_finiteSequences_iff _ _).mpr ⟨domain s, hn, IsFunction.mem_function s⟩, hstep⟩
  · rintro ⟨hs, hstep⟩
    obtain ⟨hn, hf⟩ := (mem_finiteSequences_iff_domain _ _).mp hs
    exact ⟨IsFunction.of_mem hf, hn, hstep⟩

theorem IsBoundedDerivation.certificate {s : V} (hs : IsBoundedDerivation s) : IsBoundedCertificate s := by
  obtain ⟨hn, hf⟩ := (mem_finiteSequences_iff_domain _ _).mp hs.1
  exact ⟨IsFunction.of_mem hf, hn, hs.2⟩

theorem boundedCertificate_sound {s : V} (hs : IsBoundedCertificate s) : range s ⊆ (boundedFormulaFamily : V) :=
  finiteDerivation_sound BoundedDerivationStep (by definability) _ _
    (fun _ _ hS h ↦ boundedDerivationStep_closed boundedFormulaFamily_closed hS h) s
    ((isBoundedCertificate_iff s).mp hs)

theorem isBoundedFormulaCode_iff_certificate (n φ : V) :
    IsBoundedFormulaCode n φ ↔ ∃ s : V, IsBoundedCertificate s ∧ ⟨n, φ⟩ₖ ∈ range s := by
  constructor
  · intro h
    obtain ⟨s, hs, hφ⟩ := (isBoundedFormulaCode_iff_derivation n φ).mp h
    exact ⟨s, hs.certificate, hφ⟩
  · rintro ⟨s, hs, hφ⟩
    exact boundedCertificate_sound hs _ hφ

end ZFVP
