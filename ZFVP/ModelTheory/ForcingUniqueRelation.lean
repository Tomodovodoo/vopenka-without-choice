import ZFVP.ModelTheory.ForcingEntailment
import ZFVP.SetTheory.ForcingRenaming
import ZFVP.ModelTheory.ForcingIsomorphismNames
import ZFVP.SetTheory.SaturatedNameEquality
import ZFVP.ModelTheory.ForcingFormulaNameSpecification

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u
variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingFormula_unique_equality {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (hunique : ∀ (W : Type u) [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
      ∀ v : Fin n → W, ∀ x y : W, φ.Evalb (x :> v) → φ.Evalb (y :> v) → x = y)
    {P R one p : V} (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hp : p ∈ P)
    (v : Fin n → ForcingName P) (x y : ForcingName P)
    (hx : p ∈ forcingFormula P R φ (standardTuple (fun i ↦ ((x :> v) i).val)))
    (hy : p ∈ forcingFormula P R φ (standardTuple (fun i ↦ ((y :> v) i).val))) :
    p ∈ atomicEquality P R x.val y.val := by
  let ix : Fin (n + 1) → Fin (n + 2) := Fin.cases 0 (fun i ↦ i.succ.succ)
  let iy : Fin (n + 1) → Fin (n + 2) := Fin.cases 1 (fun i ↦ i.succ.succ)
  let φx : SetTheorySemisentence (n + 2) := φ.subst (fun i ↦ .bvar (ix i))
  let φy : SetTheorySemisentence (n + 2) := φ.subst (fun i ↦ .bvar (iy i))
  let eqφ : SetTheorySemisentence (n + 2) := .rel Language.Set.Rel.eq ![.bvar 0, .bvar 1]
  let w : Fin (n + 2) → ForcingName P := x :> y :> v
  have hwx : (fun i ↦ (w (ix i)).val) = (fun i ↦ ((x :> v) i).val) := by
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  have hwy : (fun i ↦ (w (iy i)).val) = (fun i ↦ ((y :> v) i).val) := by
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  have hxy : p ∈ forcingFormula P R (.and φx φy) (standardTuple (fun i ↦ (w i).val)) := by
    rw [forcingFormula_and, mem_inter_iff]
    constructor
    · change p ∈ forcingFormula P R (φ.subst (fun i ↦ .bvar (ix i))) _
      rw [forcingFormula_rename, hwx]
      exact hx
    · change p ∈ forcingFormula P R (φ.subst (fun i ↦ .bvar (iy i))) _
      rw [forcingFormula_rename, hwy]
      exact hy
  have hh := forcingFormula_entailment (.and φx φy) eqφ (by
    intro W _ _ _ b hb
    change φx.Evalb b ∧ φy.Evalb b at hb
    change b 0 = b 1
    apply hunique W (fun i ↦ b i.succ.succ) (b 0) (b 1)
    · have he : (fun i ↦ b (ix i)) = (b 0 :> fun i ↦ b i.succ.succ) := by
        funext i
        exact Fin.cases rfl (fun _ ↦ rfl) i
      have hh : φ.Evalb (fun i ↦ b (ix i)) := by
        simpa [φx, Semiformula.eval_substs, Function.comp_def] using hb.1
      exact he ▸ hh
    · have he : (fun i ↦ b (iy i)) = (b 1 :> fun i ↦ b i.succ.succ) := by
        funext i
        exact Fin.cases rfl (fun _ ↦ rfl) i
      have hh : φ.Evalb (fun i ↦ b (iy i)) := by
        simpa [φy, Semiformula.eval_substs, Function.comp_def] using hb.2
      exact he ▸ hh)
    hR ht hp w hxy
  simpa only [eqφ, forcingFormula_rel, forcingAtomic, forcingTermValue, value_standardTuple,
    w, Matrix.cons_val_zero, Matrix.cons_val_one] using hh

theorem IsForcingIsomorphism.saturated_unique_relation {n : ℕ}
    (φ : SetTheorySemisentence (n + 1))
    (hunique : ∀ (W : Type u) [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
      ∀ v : Fin n → W, ∀ x y : W, φ.Evalb (x :> v) → φ.Evalb (y :> v) → x = y)
    {P R Q S f one ζ : V} [IsOrdinal ζ]
    (hf : IsForcingIsomorphism P R Q S f)
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (ht : IsForcingTop Q S one) (v : Fin n → ForcingName P)
    (x : ForcingName P) (y : ForcingName Q)
    (hx : ∀ p ∈ P, p ∈ forcingFormula P R φ
      (standardTuple (fun i ↦ ((x :> v) i).val)))
    (hy : ∀ q ∈ Q, q ∈ forcingFormula Q S φ
      (standardTuple (fun i ↦ ((y :> fun j ↦
        (⟨nameAction f (v j).val, nameAction_isName hf.1 (v j).property⟩ : ForcingName Q)) i).val))) :
    nameAction f (forcingSaturatedName P R (forcingNameHierarchy P ζ) x.val) =
      forcingSaturatedName Q S (forcingNameHierarchy Q ζ) y.val := by
  rw [hf.saturated_name x.property]
  apply forcingSaturatedName_eq_of_forced_equality hS
  intro q hq
  let w : Fin n → ForcingName Q := fun j ↦
    ⟨nameAction f (v j).val, nameAction_isName hf.1 (v j).property⟩
  let x' : ForcingName Q := ⟨nameAction f x.val, nameAction_isName hf.1 x.property⟩
  have hp := function_value_mem hf.inverse_maps hq
  have hh := (forcingFormula_isomorphism_iff hR hS hf φ
    (fun i ↦ ((x :> v) i).val) (fun i ↦ ((x :> v) i).property) hp).mpr
      (hx _ hp)
  rw [hf.value_inverse hq] at hh
  have he : (fun i ↦ nameAction f ((x :> v) i).val) =
      (fun i ↦ ((x' :> w) i).val) := by
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  rw [he] at hh
  exact forcingFormula_unique_equality φ hunique hS ht hq w x' y hh (hy q hq)

theorem IsForcingIsomorphism.saturated_formulaUniqueName {n : ℕ}
    (φ : SetTheorySemisentence (n + 1))
    (hvalid : ∀ (W : Type u) [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
      ∀ v : Fin n → W, ∃! x : W, φ.Evalb (x :> v))
    {P R Q S f one top ζ : V} [IsOrdinal ζ]
    (hf : IsForcingIsomorphism P R Q S f)
    (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (ht : IsForcingTop P R one) (ht' : IsForcingTop Q S top)
    (v : Fin n → ForcingName P) :
    nameAction f (forcingSaturatedName P R (forcingNameHierarchy P ζ)
      (formulaUniqueName P R φ (standardTuple (fun i ↦ (v i).val)))) =
      forcingSaturatedName Q S (forcingNameHierarchy Q ζ)
        (formulaUniqueName Q S φ (standardTuple (fun i ↦ nameAction f (v i).val))) := by
  let w : Fin n → ForcingName Q := fun j ↦
    ⟨nameAction f (v j).val, nameAction_isName hf.1 (v j).property⟩
  apply hf.saturated_unique_relation φ (fun W _ _ _ b x y hx hy ↦
    (hvalid W b).unique hx hy) hR hS ht' v
    ⟨_, formulaUniqueName_isName _ _ _ _⟩ ⟨_, formulaUniqueName_isName _ _ _ _⟩
  · intro p hp
    exact formulaUniqueName_forces φ hvalid hR ht hp v
  · intro q hq
    exact formulaUniqueName_forces φ hvalid hS ht' hq w

end ZFVP
