import ZFVP.ModelTheory.SymmetricLiftElementary

/-! A language name in a fixed transitive ground set supplies fixed symbols. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SymmetricContext

/-- An external relation recording a representative in a specified ground set. -/
def HasNameIn (S : SymmetricContext V) (B : V) (x : S.Model) : Prop :=
  ∃ σ : S.Name, σ.val ∈ B ∧ x = S.ofName σ

theorem hasNameIn_mem (S : SymmetricContext V) {B : V} [IsTransitive B]
    {x y : S.Model} (hx : S.HasNameIn B x) (hy : y ∈ x) : S.HasNameIn B y := by
  obtain ⟨σ, hσ, rfl⟩ := hx
  obtain ⟨τ, p, _, hp, rfl⟩ := (S.mem_ofName_iff σ y).mp hy
  exact ⟨τ, (kpair_components_mem_transitive
    ((inferInstance : IsTransitive B).mem_trans hp hσ)).1, rfl⟩

theorem hasNameIn_kpair (S : SymmetricContext V) {B : V} [IsTransitive B]
    {x y : S.Model} (h : S.HasNameIn B ⟨x, y⟩ₖ) : S.HasNameIn B x ∧ S.HasNameIn B y := by
  have hx : S.HasNameIn B ({x} : S.Model) := S.hasNameIn_mem h (by simp [kpair])
  have hy : S.HasNameIn B ({x, y} : S.Model) := S.hasNameIn_mem h (by simp [kpair])
  exact ⟨S.hasNameIn_mem hx (by simp), S.hasNameIn_mem hy (by simp)⟩

theorem hasNameIn_languageSymbols (S : SymmetricContext V) {B : V} [IsTransitive B]
    {language : S.Model} (hL : IsLanguageCode language) (h : S.HasNameIn B language) :
    (∀ g ∈ functionSymbols language, S.HasNameIn B g) ∧
      ∀ r ∈ relationSymbols language, S.HasNameIn B r := by
  have hc : S.HasNameIn B (languageCode (functionSymbols language) (relationSymbols language)
      (functionArities language) (relationArities language)) := hL.1 ▸ h
  obtain ⟨hF, hRest⟩ := S.hasNameIn_kpair hc
  obtain ⟨hR, _⟩ := S.hasNameIn_kpair hRest
  exact ⟨fun _ hg ↦ S.hasNameIn_mem hF hg, fun _ hr ↦ S.hasNameIn_mem hR hr⟩

end SymmetricContext

namespace SymmetricLiftData

variable {S : SymmetricContext V} {U W f : V}
variable [IsTransitive U] [IsTransitive W]
variable [Nonempty (SetDomain U)] [Nonempty (SetDomain W)]
variable [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [(SetDomain W)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable (L : SymmetricLiftData S U W f)

theorem graph_fixed_of_nameBound {B : V} (hBU : B ⊆ U) (hfix : ∀ z ∈ B, f ‘ z = z)
    {x : S.Model} (hx : S.HasNameIn B x) : x ∈ domain L.graph ∧ L.graph ‘ x = x := by
  obtain ⟨σ, hσ, rfl⟩ := hx
  have hσU := hBU σ.val hσ
  refine ⟨(L.graph_domain _).mpr ⟨σ, hσU, rfl⟩, ?_⟩
  rw [L.graph_value σ hσU]
  apply congrArg S.ofName
  exact Subtype.ext (hfix σ.val hσ)

theorem structure_restriction_elementary_of_nameBound {B : V} [IsTransitive B]
    (hBU : B ⊆ U) (hfix : ∀ z ∈ B, f ‘ z = z)
    {language M : S.Model} (hM : IsStructureCode language M) (hm : M ∈ domain L.graph)
    (hl : S.HasNameIn B language) :
    IsCodedElementaryEmbedding language M (L.graph ‘ M) (L.graph ↾ (structureDomain M)) := by
  obtain ⟨hld, hlf⟩ := L.graph_fixed_of_nameBound hBU hfix hl
  obtain ⟨hF, hR⟩ := S.hasNameIn_languageSymbols hM.language hl
  have hFs := fun g hg ↦ L.graph_fixed_of_nameBound hBU hfix (hF g hg)
  have hRs := fun g hg ↦ L.graph_fixed_of_nameBound hBU hfix (hR g hg)
  exact L.structure_restriction_elementary hM hm hld hlf
    (fun g hg ↦ (hFs g hg).1) (fun g hg ↦ (hRs g hg).1)
    (fun g hg ↦ (hFs g hg).2) (fun g hg ↦ (hRs g hg).2)

end SymmetricLiftData
end ZFVP
