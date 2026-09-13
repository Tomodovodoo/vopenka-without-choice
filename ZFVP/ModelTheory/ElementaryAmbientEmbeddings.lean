import ZFVP.ModelTheory.ElementaryInclusionLaws

/-! Embeddings between elementary substructures preserve ambient truth for every internal code. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCodedMembershipEmbedding.ambient_satisfaction {A B U e n φ b : V}
    (he : IsCodedMembershipEmbedding A B e) (hAU : IsElementaryInclusion A U)
    (hBU : IsElementaryInclusion B U) (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ A ^ n) :
    MembershipSatisfies U n φ b ↔ MembershipSatisfies U n φ (compose b e) :=
  (hAU.satisfaction_iff hφ.context hφ hb).symm.trans
    ((he.satisfies_iff hφ.context hφ.valid (by simpa using hb)).trans
      (hBU.satisfaction_iff hφ.context hφ (compose_function hb he.function)))

theorem IsCodedMembershipEmbedding.ambient_class {A B U e φ M a : V}
    (he : IsCodedMembershipEmbedding A B e) (hAU : IsElementaryInclusion A U)
    (hBU : IsElementaryInclusion B U) (hφ : IsMembershipFormulaCode (2 : V) φ)
    (hM : M ∈ A) (ha : a ∈ A) (hfix : e ‘ a = a) :
    MembershipSatisfies U 2 φ (standardTuple ![M, a]) ↔
      MembershipSatisfies U 2 φ (standardTuple ![e ‘ M, a]) := by
  have hb : standardTuple ![M, a] ∈ A ^ (2 : V) := standardTuple_mem_function _ (by simp [hM, ha])
  have hs := he.ambient_satisfaction hAU hBU hφ hb
  let := IsFunction.of_mem he.function
  rw [compose_standardTuple _ e (by simp [domain_eq_of_mem_function he.function, hM, ha])] at hs
  have hv : (fun i ↦ e ‘ (![M, a] i)) = ![e ‘ M, a] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases hfix (fun t ↦ Fin.elim0 t) j) i
  rw [hv] at hs
  exact hs

end ZFVP
