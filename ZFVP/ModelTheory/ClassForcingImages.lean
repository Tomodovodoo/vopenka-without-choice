import ZFVP.ModelTheory.ClassForcingImageName
import ZFVP.ModelTheory.ClassForcingPretameness

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V) (hT : T.IsPretame) {G : Set V}
    (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)
include hT

theorem classModel_definableImage (τ : T.Name) (A : V → V → V → Prop)
    (hA : ℒₛₑₜ-relation₃ A)
    (hc : ∀ σ ν : T.Name, ∀ p, A σ.val ν.val p → T.Condition p)
    (hd : ∀ σ ν : T.Name, T.ClassDownward (A σ.val ν.val))
    (Q : T.ClassModel hG → T.ClassModel hG → Prop)
    (htruth : ∀ σ ν : T.Name, T.ClassMeets G (A σ.val ν.val) ↔
      T.ofClassName hG σ ∈ T.ofClassName hG τ ∧ Q (T.ofClassName hG σ) (T.ofClassName hG ν))
    (huniq : ∀ x, x ∈ T.ofClassName hG τ → ∀ y z, Q x y → Q x z → y = z) :
    ∃ b : T.ClassModel hG, ∀ y, y ∈ b ↔ ∃ x, x ∈ T.ofClassName hG τ ∧ Q x y := by
  let I := domain τ.val
  have hI : ∀ σ ∈ I, T.IsName σ := by
    intro σ hσ
    obtain ⟨p, hp⟩ := mem_domain_iff.mp hσ
    exact τ.property.pair_subname T hp
  let P := fun σ p ↦ ∃ ν, T.IsName ν ∧ A σ ν p
  have hdP : ℒₛₑₜ-relation P := by unfold P; definability
  have hdP_at (σ : V) : ℒₛₑₜ-predicate (P σ) := by definability
  have hcP (σ : T.Name) : ∀ p, P σ.val p → T.Condition p := by
    rintro p ⟨ν, hν, ha⟩
    exact hc σ ⟨ν, hν⟩ p ha
  have hdownP (σ : T.Name) : T.ClassDownward (P σ.val) := by
    rintro p ⟨ν, hν, ha⟩ q hq hqp
    exact ⟨ν, hν, hd σ ⟨ν, hν⟩ p ha q hq hqp⟩
  let D := fun σ p ↦ P σ p ∨ T.ClassNegation (P σ) p
  have hdD : ℒₛₑₜ-relation D := by unfold D ClassNegation; definability
  have hD : ∀ σ ∈ I, ClassForcingDense T.Condition T.LE (D σ) :=
    fun σ hσ ↦ T.classDecision_dense _ (hcP ⟨σ, hI σ hσ⟩)
  obtain ⟨q, hqG, F, hF⟩ := hT.refinements_in_generic T hG D hdD I hD
  have hpS {σ p : V} (hσ : σ ∈ I) (hp : p ∈ F ‘ σ) : p ∈ ⋃ˢ range F := by
    have := hF.1
    have hi : σ ∈ domain F := hF.2.1.symm ▸ hσ
    exact mem_sUnion_iff.mpr ⟨F ‘ σ, mem_range_of_kpair_mem (kpair_value_mem hi), hp⟩
  obtain ⟨B, hB⟩ := T.classImageWitnessBound I (⋃ˢ range F) A hA
  let β : T.Name := ⟨T.classImageName I F B A hA, T.classImageName_isName I F B A hA⟩
  refine ⟨T.ofClassName hG β, ?_⟩
  intro y
  constructor
  · intro hy
    obtain ⟨ν, p, hpG, hp, rfl⟩ := (T.mem_ofClassName_iff hG β y).mp hy
    obtain ⟨_, _, _, _, σ, hσ, _, ha⟩ := (T.mem_classImageName I F B A hA _ _).mp hp
    exact ⟨T.ofClassName hG ⟨σ, hI σ hσ⟩,
      (htruth ⟨σ, hI σ hσ⟩ ν).mp ⟨p, hpG, ha⟩⟩
  · rintro ⟨x, hx, hQ⟩
    obtain ⟨ξ, rfl⟩ := T.ofClassName_surjective hG y
    obtain ⟨σ, s, hsG, hσs, he⟩ := (T.mem_ofClassName_iff hG τ x).mp hx
    rw [he] at hx hQ
    have hσ : σ.val ∈ I := mem_domain_of_kpair_mem hσs
    obtain ⟨r, hrG, hra⟩ := (htruth σ ξ).mpr ⟨hx, hQ⟩
    have hmeet : T.ClassMeets G (P σ.val) := ⟨r, hrG, ξ.val, ξ.property, hra⟩
    obtain ⟨p, hpF, hpG⟩ := T.classPredense_meets hG (hF.2.2 σ.val hσ).2 hqG
    have hex : P σ.val p := by
      rcases (hF.2.2 σ.val hσ).1 p hpF with hh | hn
      · exact hh
      · exact ((T.classMeets_negation hG (P σ.val) (hdP_at σ.val) (hcP σ) (hdownP σ)).mp
          ⟨p, hpG, hn⟩ hmeet).elim
    obtain ⟨ν, hνB, hν, hνA⟩ := hB σ.val hσ p (hpS hσ hpF) hex
    let ν' : T.Name := ⟨ν, hν⟩
    have hQν := ((htruth σ ν').mp ⟨p, hpG, hνA⟩).2
    have heν := huniq _ hx _ _ hQ hQν
    apply (T.mem_ofClassName_iff hG β _).mpr
    exact ⟨ν', p, hpG, (T.mem_classImageName I F B A hA _ _).mpr
      ⟨hνB, hpS hσ hpF, hν, hG.1.1 p hpG, σ.val, hσ, hpF, hνA⟩, heν⟩

end DefinableForcingTower
end ZFVP
