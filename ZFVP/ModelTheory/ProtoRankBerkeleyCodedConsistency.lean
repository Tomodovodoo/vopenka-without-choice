import ZFVP.ModelTheory.ProtoRankBerkeleyCodedVP
import ZFVP.Syntax.ZFVPOpenAxiomSet

/-! Proto rank-Berkeley excludes every internally finite refutation in the coded ZF+VP calculus. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsProtoRankBerkeley.codedZFVP_consistent {ζ δ : V} (hδ : IsProtoRankBerkeley ζ δ) :
    OpenCodedSequentConsistent (zfVPOpenAxiomCodes : V) := by
  obtain ⟨Λ, _, _, _, _, hzf, hvp⟩ := hδ.exists_internalZF_codedVP
  exact codedZFVP_model_consistent hzf hvp

end ZFVP
