import ZFVP.ModelTheory.CodedElementaryEmbedding
import ZFVP.Syntax.EndExtensionSatisfaction
import ZFVP.ModelTheory.CodedMembershipEmbedding
import ZFVP.Syntax.EndExtensionMembershipSatisfaction

/-! Arbitrary-language coded elementarity is absolute under ZF membership end extensions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

def transitiveSubtype {V : Type*} [SetStructure V] (U : V) [hU : IsTransitive U] :
    MembershipEndExtension (SetDomain U) V where
  toFun := Subtype.val
  injective := Subtype.val_injective
  mem_iff _ _ := Iff.rfl
  endExtension x y hy := ⟨⟨y, hU.mem_trans hy x.property⟩, hy, rfl⟩

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem codedElementaryEmbedding_iff (j : MembershipEndExtension V W) (L M N f : V) :
    IsCodedElementaryEmbedding (j L) (j M) (j N) (j f) ↔
      IsCodedElementaryEmbedding L M N f := by
  unfold IsCodedElementaryEmbedding
  rw [j.structureCode_iff, j.structureCode_iff]
  apply and_congr_right
  intro hM
  apply and_congr_right
  intro _
  rw [← j.map_structureDomain, ← j.map_structureDomain, j.function_iff]
  apply and_congr_right
  intro _
  rw [← j.map_omega, j.forall_mem_iff]
  apply forall_congr'
  intro n
  apply forall_congr'
  intro hn
  rw [← j.map_empty, ← j.map_formulaSet hM.language, j.forall_mem_iff]
  apply forall_congr'
  intro φ
  apply forall_congr'
  intro _
  rw [← j.map_finiteFunctionSet _ hn, j.forall_mem_iff]
  apply forall_congr'
  intro b
  apply forall_congr'
  intro _
  rw [← j.map_compose, j.satisfies_iff hM.language, j.satisfies_iff hM.language]

theorem codedMembershipEmbedding_iff (j : MembershipEndExtension V W) (A B f : V) :
    IsCodedMembershipEmbedding (j A) (j B) (j f) ↔ IsCodedMembershipEmbedding A B f := by
  unfold IsCodedMembershipEmbedding
  rw [← j.map_membershipLanguageCode, ← j.map_membershipStructureCode,
    ← j.map_membershipStructureCode, j.codedElementaryEmbedding_iff]

end MembershipEndExtension

namespace TransitiveZF

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem codedElementaryEmbedding_iff (U : V) [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (L M N f : SetDomain U) :
    IsCodedElementaryEmbedding L.val M.val N.val f.val ↔
      IsCodedElementaryEmbedding L M N f :=
  (MembershipEndExtension.transitiveSubtype U).codedElementaryEmbedding_iff L M N f

theorem codedMembershipEmbedding_iff (U : V) [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (A B f : SetDomain U) :
    IsCodedMembershipEmbedding A.val B.val f.val ↔ IsCodedMembershipEmbedding A B f :=
  (MembershipEndExtension.transitiveSubtype U).codedMembershipEmbedding_iff A B f

end TransitiveZF

end ZFVP
