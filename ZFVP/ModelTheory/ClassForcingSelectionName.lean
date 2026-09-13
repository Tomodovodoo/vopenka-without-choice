import ZFVP.ModelTheory.ClassForcingPretameness
import ZFVP.ModelTheory.ClassForcingTowerNameEvaluation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

noncomputable def classSelectionName (_T : DefinableForcingTower V) (I F : V)
    (A : V → V → Prop) (hA : ℒₛₑₜ-relation A) : V :=
  {z ∈ I ×ˢ (⋃ˢ range F) ; kpair.π₂ z ∈ F ‘ (kpair.π₁ z) ∧ A (kpair.π₁ z) (kpair.π₂ z)}

theorem mem_classSelectionName (I F : V) (A : V → V → Prop) (hA : ℒₛₑₜ-relation A)
    (hF : IsFunction F) (hdom : domain F = I) (σ p : V) :
    ⟨σ, p⟩ₖ ∈ T.classSelectionName I F A hA ↔ σ ∈ I ∧ p ∈ F ‘ σ ∧ A σ p := by
  have := hF
  simp only [classSelectionName, mem_sep_iff, kpair_mem_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  constructor
  · rintro ⟨⟨hσ, _⟩, hp, ha⟩
    exact ⟨hσ, hp, ha⟩
  · rintro ⟨hσ, hp, ha⟩
    have hσd : σ ∈ domain F := hdom.symm ▸ hσ
    exact ⟨⟨hσ, mem_sUnion_iff.mpr
      ⟨F ‘ σ, mem_range_of_kpair_mem (kpair_value_mem hσd), hp⟩⟩, hp, ha⟩

theorem classSelectionName_isName (I F : V) (A : V → V → Prop) (hA : ℒₛₑₜ-relation A)
    (hI : ∀ σ ∈ I, T.IsName σ) (hc : ∀ σ ∈ I, ∀ p, A σ p → T.Condition p) :
    T.IsName (T.classSelectionName I F A hA) := by
  apply (T.isName_iff_local _).mpr
  intro z hz
  obtain ⟨σ, hσ, p, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
  have ha : A σ p := by
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using (mem_sep_iff.mp hz).2.2
  exact ⟨σ, p, hc σ hσ p ha, rfl, hI σ hσ⟩

theorem classSelectionName_value {G : Set V}
    (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)
    (I F : V) (A : V → V → Prop) (hA : ℒₛₑₜ-relation A)
    (hI : ∀ σ ∈ I, T.IsName σ) (hr : ∀ σ ∈ I, T.ClassRegular (A σ))
    {q : V} (hqG : q ∈ G)
    (hF : T.ClassDenseRefinements (fun σ p ↦ A σ p ∨ T.ClassNegation (A σ) p) I q F)
    (x : T.ClassModel hG) :
    x ∈ T.ofClassName hG
      ⟨T.classSelectionName I F A hA, T.classSelectionName_isName I F A hA hI
        (fun σ hσ ↦ (hr σ hσ).1)⟩ ↔
      ∃ σ : T.Name, σ.val ∈ I ∧ x = T.ofClassName hG σ ∧ T.ClassMeets G (A σ.val) := by
  rw [T.mem_ofClassName_iff]
  constructor
  · rintro ⟨σ, p, hpG, hp, he⟩
    obtain ⟨hσ, _, ha⟩ := (T.mem_classSelectionName I F A hA hF.1 hF.2.1 _ _).mp hp
    exact ⟨σ, hσ, he, p, hpG, ha⟩
  · rintro ⟨σ, hσ, he, hm⟩
    obtain ⟨p, hp, hpG⟩ := T.classPredense_meets hG (hF.2.2 σ.val hσ).2 hqG
    have ha : A σ.val p := by
      rcases (hF.2.2 σ.val hσ).1 p hp with ha | hn
      · exact ha
      · exact ((T.classMeets_negation hG (A σ.val) (by definability)
          (hr σ.val hσ).1 (hr σ.val hσ).2.1).mp ⟨p, hpG, hn⟩ hm).elim
    exact ⟨σ, p, hpG, (T.mem_classSelectionName I F A hA hF.1 hF.2.1 _ _).mpr
      ⟨hσ, hp, ha⟩, he⟩

end DefinableForcingTower
end ZFVP
