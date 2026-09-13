import ZFVP.ModelTheory.SchmerlCodedSourceBridge
import ZFVP.ModelTheory.SchmerlCodedBranchFilter
import ZFVP.ModelTheory.SchmerlCodedDefinitionCardinality
import ZFVP.ModelTheory.SchmerlInternalWeakSpecialization

/-! The actual coded Rubin source supplies the full branch bound and hence
the internal weak-specializing forcing extension. Source existence is separate. -/

set_option autoImplicit false

namespace ZFVP.BinaryRelationRepresentation

open LO LO.FirstOrder LO.FirstOrder.SetTheory Schmerl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (R : BinaryRelationRepresentation (V := V) W)

attribute [local irreducible] codedBranchFilter

theorem selectedBranches_cardLE_definableSubsets {κ c : V} [IsOrdinal κ]
    (hc : IsInternalCofinalStrictChain κ (codedOrdinals R.code) (codedOrdinalOrder R.code) c)
    (hRubin : IsCodedRubin R.code κ) :
    internalCofinalBranches (codedSelectedClassNodes R.code κ c) (codedSelectedClassOrder R.code κ c) κ
      (codedSelectedClassRank R.code κ c) ≤# codedDefinableSubsets R.code := by
  apply cardLE_of_injective_map (codedBranchFilter R.code) (by definability)
  · intro B hB
    exact (mem_codedDefinableSubsets _ _).mpr
      (R.codedBranchFilter_isCodedDefinable hc ((mem_internalCofinalBranches _ _ _ _ _).mp hB) hRubin)
  · intro B hB C hC he
    have hB' := (mem_internalCofinalBranches _ _ _ _ _).mp hB
    have hC' := (mem_internalCofinalBranches _ _ _ _ _).mp hC
    calc
      B = codedBranchFilter R.code B ∩ codedSelectedClassNodes R.code κ c := (R.codedBranchFilter_recovers hB').symm
      _ = codedBranchFilter R.code C ∩ codedSelectedClassNodes R.code κ c := congrArg (fun F ↦ F ∩ _) he
      _ = C := R.codedBranchFilter_recovers hC'

theorem selectedBranches_cardLE (hAC : InternalChoice V) {c : V}
    (hc : IsInternalCofinalStrictChain (hartogsNumber (ω : V)) (codedOrdinals R.code) (codedOrdinalOrder R.code) c)
    (hRubin : IsCodedRubin R.code (hartogsNumber (ω : V)))
    (hcard : structureDomain R.code ≤# hartogsNumber (ω : V)) :
    internalCofinalBranches (codedSelectedClassNodes R.code (hartogsNumber (ω : V)) c)
      (codedSelectedClassOrder R.code (hartogsNumber (ω : V)) c) (hartogsNumber (ω : V))
      (codedSelectedClassRank R.code (hartogsNumber (ω : V)) c) ≤# hartogsNumber (ω : V) := by
  apply (R.selectedBranches_cardLE_definableSubsets hc hRubin).trans
  exact codedDefinableSubsets_cardLE hAC (hartogsNumber_initial (ω : V))
    (IsOrdinal.toIsTransitive.transitive _ omega_mem_hartogs_omega) hcard

end ZFVP.BinaryRelationRepresentation

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCodedRubinFinSmallSource.exists_weak_specialization_extension [Countable V]
    (hAC : InternalChoice V) {M : V} (h : IsCodedRubinFinSmallSource M) :
    ∃ c, IsInternalCofinalStrictChain (hartogsNumber (ω : V)) (codedOrdinals M) (codedOrdinalOrder M) c ∧
      ∃ F : ForcingContext V,
        InternalChoice F.Model ∧ F.check (hartogsNumber (ω : V)) = hartogsNumber (ω : F.Model) ∧
        (∃ f ∈ (ω : F.Model) ^ F.check (codedSelectedClassNodes M (hartogsNumber (ω : V)) c),
          InternallyWeakSpecialization (F.check (codedSelectedClassNodes M (hartogsNumber (ω : V)) c))
            (F.check (codedSelectedClassOrder M (hartogsNumber (ω : V)) c)) f) ∧
        ∀ B : F.Model,
          IsInternalCofinalBranch (F.check (codedSelectedClassNodes M (hartogsNumber (ω : V)) c))
            (F.check (codedSelectedClassOrder M (hartogsNumber (ω : V)) c)) (hartogsNumber (ω : F.Model))
            (F.check (codedSelectedClassRank M (hartogsNumber (ω : V)) c)) B →
          ∃ C : V,
            IsInternalCofinalBranch (codedSelectedClassNodes M (hartogsNumber (ω : V)) c)
              (codedSelectedClassOrder M (hartogsNumber (ω : V)) c) (hartogsNumber (ω : V))
              (codedSelectedClassRank M (hartogsNumber (ω : V)) c) C ∧ F.check C = B := by
  obtain ⟨⟨D, E, rfl, hE⟩, hZF, hcard, hRubin, _⟩ := h
  have hD : IsNonempty D := by simpa only [binaryRelationStructureCode_domain] using hZF.valid.domain_nonempty
  let R := binaryIdentityRepresentation hD hE
  let : Nonempty (BinaryRelationDomain D E) := binaryRelationDomain_nonempty hD
  let : (BinaryRelationDomain D E)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := R.models_zf_of_isCodedZFModel hZF
  obtain ⟨c, hc⟩ := R.exists_cofinal_ordinal_chain hRubin
  refine ⟨c, hc, ?_⟩
  exact exists_internal_weak_specialization_extension hAC (R.selectedClassTree hc)
    (R.selectedClassOrder_poset _ c)
    (fun _ hx _ hy hxy he ↦ R.selectedClassRank_comparable_injective hc hx hy hxy he)
    (R.selectedBranches_cardLE hAC hc hRubin hcard)

end ZFVP.Schmerl
