import ZFVP.ModelTheory.InternalZFExternal
import ZFVP.Syntax.ZFVPOpenAxiomSet
import ZFVP.ModelTheory.ProtoRankBerkeleyCodedVP

/-! External ZF+VP models obtained from the full internal axiom dictionary. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def vopenkaTheory : Theory ℒₛₑₜ := Set.range vopenkaSentence

def zfVPTheory : Theory ℒₛₑₜ := 𝗭𝗙 ∪ vopenkaTheory

def unboundedExtendibilityTheory : Theory ℒₛₑₜ :=
  Set.range (fun n : ℕ ↦ unboundedExtendibilitySentence (n + 1))

def zfUEVPTheory : Theory ℒₛₑₜ := zfVPTheory ∪ unboundedExtendibilityTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem localCodedVopenka_encode_iff {U : V} (hU : IsNonempty U)
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (φ : SetTheorySemisentence 2) :
    LocalCodedVopenka U (encodeMembershipFormula φ) ↔
      (SetDomain U)↓[ℒₛₑₜ] ⊧ vopenkaSentence φ := by
  have he (M a : SetDomain U) : MembershipSatisfies U 2 (encodeMembershipFormula φ)
      (standardTuple ![M.val, a.val]) ↔ φ.Evalb ![M, a] := by
    have hv : (fun i : Fin 2 ↦ (![M, a] i).val) = ![M.val, a.val] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    have htwo : ((2 : ℕ) : V) = (2 : V) := rfl
    simpa only [hv, htwo] using membershipSatisfies_encode hU φ ![M, a]
  simp only [LocalCodedVopenka, he]
  simp [models_iff, vopenkaSentence, Semiformula.Realize, Semiformula.Evalb]

theorem codedZFVP_models_external {U : V} [Nonempty (SetDomain U)]
    (hU : SatisfiesOpenCodes U zfVPOpenAxiomCodes) :
    (SetDomain U)↓[ℒₛₑₜ] ⊧* zfVPTheory := by
  obtain ⟨hzf, hvp⟩ := (satisfiesOpenCodes_zfVP_iff U).mp hU
  let := hzf.models_zf
  refine ⟨?_⟩
  intro ψ hψ
  rcases hψ with hψ | ⟨φ, rfl⟩
  · exact Theory.models (SetDomain U) 𝗭𝗙 hψ
  · apply (localCodedVopenka_encode_iff hU.1 φ).mp
    have hφ : IsMembershipFormulaCode (2 : V) (encodeMembershipFormula φ) :=
      (mem_formulaSet_iff _ _ _ _).mp (encodeMembershipFormula_mem φ)
    exact (vopenkaCode_satisfies hU.1 hφ).mp (hvp _ hφ)

theorem IsProtoRankBerkeley.externalZFVP_model {ζ δ : V} (hδ : IsProtoRankBerkeley ζ δ) :
    ∃ Λ : V, IsOrdinal Λ ∧ Λ ⊆ δ ∧ ζ ∈ Λ ∧ internalCofinality Λ = (ω : V) ∧
      ∃ hN : Nonempty (SetDomain (hierarchy Λ)),
        letI := hN; (SetDomain (hierarchy Λ))↓[ℒₛₑₜ] ⊧* zfVPTheory := by
  obtain ⟨Λ, ho, hb, hz, hc, hzf, hvp⟩ := hδ.exists_internalZF_codedVP
  have hn : Nonempty (SetDomain (hierarchy Λ)) := by
    obtain ⟨x, hx⟩ := hzf.1.1
    exact ⟨⟨x, hx⟩⟩
  let := hn
  exact ⟨Λ, ho, hb, hz, hc, hn,
    codedZFVP_models_external ((satisfiesOpenCodes_zfVP_iff _).mpr ⟨hzf, hvp⟩)⟩

theorem IsProtoRankBerkeley.externalZFVP_consistent {ζ δ : V} (hδ : IsProtoRankBerkeley ζ δ) :
    Entailment.Consistent zfVPTheory := by
  obtain ⟨Λ, _, _, _, _, hn, hm⟩ := hδ.externalZFVP_model
  let := hn
  exact Theory.consistent_of_satisfiable ⟨(SetDomain (hierarchy Λ))↓[ℒₛₑₜ], hm⟩

theorem IsProtoRankBerkeley.externalZFUEVP_model {ζ δ : V} (hδ : IsProtoRankBerkeley ζ δ) :
    ∃ Λ : V, IsOrdinal Λ ∧ Λ ⊆ δ ∧ ζ ∈ Λ ∧ internalCofinality Λ = (ω : V) ∧
      ∃ hN : Nonempty (SetDomain (hierarchy Λ)),
        letI := hN; (SetDomain (hierarchy Λ))↓[ℒₛₑₜ] ⊧* zfUEVPTheory := by
  obtain ⟨Λ, ho, hb, hz, hc, hzf, hue, hvp⟩ := hδ.exists_zf_ue_vopenka
  have hn : Nonempty (SetDomain (hierarchy Λ)) := by
    obtain ⟨x, hx⟩ := hzf.1.1
    exact ⟨⟨x, hx⟩⟩
  let := hn
  let := hzf.models_zf
  refine ⟨Λ, ho, hb, hz, hc, hn, ⟨?_⟩⟩
  intro ψ hψ
  rcases hψ with (hψ | ⟨φ, rfl⟩) | ⟨n, rfl⟩
  · exact Theory.models (SetDomain (hierarchy Λ)) 𝗭𝗙 hψ
  · exact (setSentenceTrue_iff_models _ _).mp (hvp φ)
  · exact (setSentenceTrue_iff_models _ _).mp (hue n)

theorem IsProtoRankBerkeley.externalZFUEVP_consistent {ζ δ : V} (hδ : IsProtoRankBerkeley ζ δ) :
    Entailment.Consistent zfUEVPTheory := by
  obtain ⟨Λ, _, _, _, _, hn, hm⟩ := hδ.externalZFUEVP_model
  let := hn
  exact Theory.consistent_of_satisfiable ⟨(SetDomain (hierarchy Λ))↓[ℒₛₑₜ], hm⟩

end ZFVP
