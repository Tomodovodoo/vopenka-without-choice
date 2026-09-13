import ZFVP.ModelTheory.ForcingRealizationEmbedding
import ZFVP.ModelTheory.ForcingCheckedTruth
import ZFVP.SetTheory.ForcingIterationInitial

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem singletonForcing_generic (u : V) :
    IsExternalForcingGeneric ({u} : V) (({u} : V) ×ˢ {u}) {p | p = u} := by
  refine ⟨⟨?_, ⟨u, rfl⟩, ?_, ?_⟩, ?_⟩
  · intro p hp; exact mem_singleton_iff.mpr hp
  · intro p _ q hq _; exact mem_singleton_iff.mp hq
  · intro p hp q hq
    subst p q
    exact ⟨u, rfl, by simp, by simp⟩
  · intro D hD
    obtain ⟨q, hq, _⟩ := hD.2 u (by simp)
    exact ⟨q, mem_singleton_iff.mp (hD.1 q hq), hq⟩

noncomputable def singletonForcingContext (u : V) : ForcingContext V :=
  ⟨{u}, ({u} : V) ×ˢ {u}, u, {p | p = u}, singletonForcing_preorder u,
    singletonForcing_top u, singletonForcing_generic u⟩

theorem singletonForcing_checked_truth (u a : V) (φ : SetTheorySemisentence 1) :
    u ∈ forcingFormula ({u} : V) (({u} : V) ×ˢ {u}) φ (standardTuple ![checkName u a]) ↔
      φ.Evalb (fun _ ↦ a) := by
  let A := singletonForcingContext u
  let L : ForcingRealization A V := {
    ground := ⟨id, Function.injective_id, fun _ _ ↦ Iff.rfl, fun x y hy ↦ ⟨y, hy, rfl⟩⟩
    genericSet := {u}
    generic_subset := subset_refl _
    generic_mem := fun p ↦ mem_singleton_iff }
  have hc (x : V) : L.value (A.check x) = x := L.value_check x
  let e : A.Model ≃ V := Equiv.ofBijective L.value
    ⟨L.value_injective, fun x ↦ ⟨A.check x, hc x⟩⟩
  have ht := eval_membershipIso e L.value_mem_iff φ (fun _ ↦ A.check a) Empty.elim
  have hv : e ∘ (fun _ : Fin 1 ↦ A.check a) = (fun _ ↦ a) := by
    funext i; exact hc a
  have hf : e ∘ (Empty.elim : Empty → A.Model) = Empty.elim := by
    funext x; exact Empty.elim x
  rw [hv, hf] at ht
  have ha := A.checked_unary_truth φ a
  change φ.Evalb (fun _ ↦ A.check a) ↔
    ∃ p, p = u ∧ p ∈ forcingFormula ({u} : V) (({u} : V) ×ˢ {u}) φ
      (standardTuple ![checkName u a]) at ha
  simpa only [exists_eq_left] using ha.symm.trans ht

theorem singletonForcing_checked_parameters_truth (u : V) {n : ℕ}
    (v : Fin n → V) (φ : SetTheorySemisentence n) :
    u ∈ forcingFormula ({u} : V) (({u} : V) ×ˢ {u}) φ
      (standardTuple (fun i ↦ checkName u (v i))) ↔ φ.Evalb v := by
  let A := singletonForcingContext u
  let L : ForcingRealization A V := {
    ground := ⟨id, Function.injective_id, fun _ _ ↦ Iff.rfl, fun x y hy ↦ ⟨y, hy, rfl⟩⟩
    genericSet := {u}
    generic_subset := subset_refl _
    generic_mem := fun p ↦ mem_singleton_iff }
  have hc (x : V) : L.value (A.check x) = x := L.value_check x
  let e : A.Model ≃ V := Equiv.ofBijective L.value
    ⟨L.value_injective, fun x ↦ ⟨A.check x, hc x⟩⟩
  have ht := eval_membershipIso e L.value_mem_iff φ (fun i ↦ A.check (v i)) Empty.elim
  have hv : e ∘ (fun i ↦ A.check (v i)) = v := by
    funext i; exact hc (v i)
  have hf : e ∘ (Empty.elim : Empty → A.Model) = Empty.elim := by
    funext x; exact Empty.elim x
  rw [hv, hf] at ht
  let c : Fin n → ForcingName A.P := fun i ↦
    ⟨checkName u (v i), checkName_isName A.top.1 (v i)⟩
  have ha := A.formula_truth φ c
  change φ.Evalb (fun i ↦ A.check (v i)) ↔
    ∃ p, p = u ∧ p ∈ forcingFormula ({u} : V) (({u} : V) ×ˢ {u}) φ
      (standardTuple (fun i ↦ checkName u (v i))) at ha
  simpa only [exists_eq_left] using ha.symm.trans ht

end ZFVP
