import ZFVP.ModelTheory.ClassForcingSelectionName
import ZFVP.Syntax.CloseTailParameters

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable V]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V) (hT : T.IsPretame) {G : Set V}
    (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)
include hT

theorem classModel_separation_names {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (w : Fin n → T.Name) (τ : T.Name) : ∃ b : T.ClassModel hG, ∀ x,
      x ∈ b ↔ x ∈ T.ofClassName hG τ ∧ φ.Evalb (x :> T.classAssignment hG w) := by
  let I := domain τ.val
  have hI : ∀ σ ∈ I, T.IsName σ := by
    intro σ hσ
    obtain ⟨p, hp⟩ := mem_domain_iff.mp hσ
    exact τ.property.pair_subname T hp
  let A := fun σ p ↦ T.ForcesMember σ τ.val p ∧
    T.towerFormula φ (assignmentPrepend (n : V) (standardTuple (fun i ↦ (w i).val)) σ) p
  have hdA : ℒₛₑₜ-relation A := by unfold A; definability
  have hrA (σ : T.Name) : T.ClassRegular (A σ.val) :=
    T.classRegular_and (T.forcesMember_regular σ τ) (T.towerFormula_regular φ (σ :> w))
  have hr : ∀ σ ∈ I, T.ClassRegular (A σ) := fun σ hσ ↦ hrA ⟨σ, hI σ hσ⟩
  let D := fun σ p ↦ A σ p ∨ T.ClassNegation (A σ) p
  have hdD : ℒₛₑₜ-relation D := by unfold D ClassNegation; definability
  have hD : ∀ σ ∈ I, ClassForcingDense T.Condition T.LE (D σ) :=
    fun σ hσ ↦ T.classDecision_dense (A σ) (hr σ hσ).1
  obtain ⟨q, hqG, F, hF⟩ := hT.refinements_in_generic T hG D hdD I hD
  let ν : T.Name := ⟨T.classSelectionName I F A hdA,
    T.classSelectionName_isName I F A hdA hI (fun σ hσ ↦ (hr σ hσ).1)⟩
  refine ⟨T.ofClassName hG ν, ?_⟩
  intro x
  rw [T.classSelectionName_value hG I F A hdA hI hr hqG hF]
  have htruth (σ : T.Name) : T.ClassMeets G (A σ.val) ↔
      T.ofClassName hG σ ∈ T.ofClassName hG τ ∧
        φ.Evalb (T.ofClassName hG σ :> T.classAssignment hG w) := by
    change T.ClassMeets G (fun p ↦ T.ForcesMember σ.val τ.val p ∧
      T.towerFormula φ (standardTuple (fun i ↦ ((σ :> w) i).val)) p) ↔ _
    rw [T.classMeets_and hG (T.forcesMember_regular σ τ).2.1
      (T.towerFormula_regular φ (σ :> w)).2.1]
    apply and_congr (T.member_truth hG σ τ).symm
    simpa only [T.classAssignment_cons] using (T.towerFormula_truth hG φ (σ :> w)).symm
  constructor
  · rintro ⟨σ, _, rfl, hm⟩
    exact (htruth σ).mp hm
  · rintro ⟨hx, hφ⟩
    obtain ⟨σ, p, hpG, hσp, he⟩ := (T.mem_ofClassName_iff hG τ x).mp hx
    refine ⟨σ, mem_domain_of_kpair_mem hσp, he, (htruth σ).mpr ?_⟩
    exact he ▸ ⟨hx, hφ⟩

theorem classModel_separation {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (v : Fin n → T.ClassModel hG) (a : T.ClassModel hG) :
    ∃ b : T.ClassModel hG, ∀ x, x ∈ b ↔ x ∈ a ∧ φ.Evalb (x :> v) := by
  obtain ⟨τ, rfl⟩ := T.ofClassName_surjective hG a
  choose w hw using fun i ↦ T.ofClassName_surjective hG (v i)
  have he : T.classAssignment hG w = v := funext hw
  simpa only [he] using T.classModel_separation_names hT hG φ w τ

theorem classModel_models_separation (φ : SetTheorySemiproposition 1) :
    (T.ClassModel hG)↓[ℒₛₑₜ] ⊧ Axiom.separationSchema φ := by
  simp [models_iff, Axiom.separationSchema, Semiformula.eval_univCl]
  intro e a
  obtain ⟨b, hb⟩ := T.classModel_separation hT hG (closeTailParameters φ)
    (fun i : Fin φ.fvSup ↦ e i.val) a
  refine ⟨b, fun x ↦ ?_⟩
  exact (hb x).trans (and_congr Iff.rfl (eval_closeTailParameters φ ![x] e))

end DefinableForcingTower
end ZFVP
