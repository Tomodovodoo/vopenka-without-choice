import ZFVP.Syntax.Atoms

/-! Eight formula constructors, corresponding to Foundation's classical syntax. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def truthCode : V := ⟨(0 : V), (∅ : V)⟩ₖ
noncomputable def falsityCode : V := ⟨(1 : V), (∅ : V)⟩ₖ
noncomputable def atomCode (r args : V) : V := ⟨(2 : V), ⟨r, args⟩ₖ⟩ₖ
noncomputable def negAtomCode (r args : V) : V := ⟨(3 : V), ⟨r, args⟩ₖ⟩ₖ
noncomputable def andCode (φ ψ : V) : V := ⟨(4 : V), ⟨φ, ψ⟩ₖ⟩ₖ
noncomputable def orCode (φ ψ : V) : V := ⟨(5 : V), ⟨φ, ψ⟩ₖ⟩ₖ
noncomputable def allCode (φ : V) : V := ⟨(6 : V), φ⟩ₖ
noncomputable def existsCode (φ : V) : V := ⟨(7 : V), φ⟩ₖ

instance atomCode_definable : ℒₛₑₜ-function₂[V] atomCode := by unfold atomCode; definability
instance negAtomCode_definable : ℒₛₑₜ-function₂[V] negAtomCode := by unfold negAtomCode; definability
instance andCode_definable : ℒₛₑₜ-function₂[V] andCode := by unfold andCode; definability
instance orCode_definable : ℒₛₑₜ-function₂[V] orCode := by unfold orCode; definability
instance allCode_definable : ℒₛₑₜ-function₁[V] allCode := by unfold allCode; definability
instance existsCode_definable : ℒₛₑₜ-function₁[V] existsCode := by unfold existsCode; definability

theorem naturalTag_mem_syntaxUniverse (L Γ : V) (k : ℕ) : (k : V) ∈ syntaxUniverse L Γ :=
  codingUniverse_natural_mem _ (by simp)

theorem truthCode_mem_syntaxUniverse (L Γ : V) : truthCode ∈ syntaxUniverse L Γ :=
  codingUniverse_kpair_closed (naturalTag_mem_syntaxUniverse L Γ 0) (codingUniverse_empty_mem _)

theorem falsityCode_mem_syntaxUniverse (L Γ : V) : falsityCode ∈ syntaxUniverse L Γ :=
  codingUniverse_kpair_closed (naturalTag_mem_syntaxUniverse L Γ 1) (codingUniverse_empty_mem _)

theorem atomCodes_mem_syntaxUniverse {L Γ n r args : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (ha : IsAtomicArguments L Γ n r args) :
    atomCode r args ∈ syntaxUniverse L Γ ∧ negAtomCode r args ∈ syntaxUniverse L Γ := by
  obtain ⟨hr, hargs⟩ := atomicArguments_mem_syntaxUniverse hL hn ha
  exact ⟨codingUniverse_kpair_closed (naturalTag_mem_syntaxUniverse L Γ 2)
      (codingUniverse_kpair_closed hr hargs),
    codingUniverse_kpair_closed (naturalTag_mem_syntaxUniverse L Γ 3)
      (codingUniverse_kpair_closed hr hargs)⟩

theorem binaryCodes_mem_syntaxUniverse {L Γ φ ψ : V} (hφ : φ ∈ syntaxUniverse L Γ)
    (hψ : ψ ∈ syntaxUniverse L Γ) :
    andCode φ ψ ∈ syntaxUniverse L Γ ∧ orCode φ ψ ∈ syntaxUniverse L Γ :=
  ⟨codingUniverse_kpair_closed (naturalTag_mem_syntaxUniverse L Γ 4)
      (codingUniverse_kpair_closed hφ hψ),
    codingUniverse_kpair_closed (naturalTag_mem_syntaxUniverse L Γ 5)
      (codingUniverse_kpair_closed hφ hψ)⟩

theorem quantifierCodes_mem_syntaxUniverse {L Γ φ : V} (hφ : φ ∈ syntaxUniverse L Γ) :
    allCode φ ∈ syntaxUniverse L Γ ∧ existsCode φ ∈ syntaxUniverse L Γ :=
  ⟨codingUniverse_kpair_closed (naturalTag_mem_syntaxUniverse L Γ 6) hφ,
    codingUniverse_kpair_closed (naturalTag_mem_syntaxUniverse L Γ 7) hφ⟩

end ZFVP

