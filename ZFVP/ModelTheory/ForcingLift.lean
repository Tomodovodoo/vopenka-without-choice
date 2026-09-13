import ZFVP.ModelTheory.ForcingModel
import ZFVP.ModelTheory.FiniteParameterElementarity
import ZFVP.SetTheory.ElementaryForcing

/-! Lifting an elementary ground map whose image filter lies in the target generic. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V W : Type*} [SetStructure V] [SetStructure W]
variable [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

structure LiftData (S : ForcingContext V) (T : ForcingContext W) (j : ElementaryMap V W) where
  poset : j S.P = T.P
  relation : j S.R = T.R
  generic : ∀ p ∈ S.G, j p ∈ T.G

namespace LiftData

variable {S : ForcingContext V} {T : ForcingContext W} {j : ElementaryMap V W}
variable (L : LiftData S T j)

def mapName (τ : ForcingName S.P) : ForcingName T.P :=
  ⟨j τ.val, L.poset ▸ (j.forcingName_iff S.P τ.val).mp τ.property⟩

theorem formula_forward {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → ForcingName S.P)
    (h : φ.Evalb (S.ofName ∘ v)) : φ.Evalb (T.ofName ∘ L.mapName ∘ v) := by
  obtain ⟨p, hpG, hpF⟩ := (forcingFormula_quotient_truth S.P S.R S.G S.order S.generic φ v).mp h
  apply (forcingFormula_quotient_truth T.P T.R T.G T.order T.generic φ (L.mapName ∘ v)).mpr
  refine ⟨j p, L.generic p hpG, ?_⟩
  have hm := (j.forcingFormula_tuple_iff S.P S.R p φ (fun i ↦ (v i).val)).mp hpF
  simpa only [L.poset, L.relation, mapName, Function.comp_def] using hm

theorem ofName_map_eq {σ τ : ForcingName S.P} (h : S.ofName σ = S.ofName τ) :
    T.ofName (L.mapName σ) = T.ofName (L.mapName τ) := by
  have hf := L.formula_forward (.rel Language.Set.Rel.eq ![.bvar 0, .bvar 1]) ![σ, τ]
    (by simpa [Semiformula.Evalb, Structure.rel, Function.comp_def] using h)
  simpa [Semiformula.Evalb, Structure.rel, Function.comp_def] using hf

noncomputable def liftFun : S.Model → T.Model :=
  Quotient.lift (fun τ ↦ T.ofName (L.mapName τ)) (fun _ _ h ↦ L.ofName_map_eq (Quotient.sound h))

theorem liftFun_ofName (τ : ForcingName S.P) :
    L.liftFun (S.ofName τ) = T.ofName (L.mapName τ) := rfl

theorem liftFun_formula_forward {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → S.Model)
    (h : φ.Evalb v) : φ.Evalb (L.liftFun ∘ v) := by
  classical
  let names : Fin n → ForcingName S.P := fun i ↦ (S.ofName_surjective (v i)).choose
  have hv : S.ofName ∘ names = v := funext (fun i ↦ (S.ofName_surjective (v i)).choose_spec)
  have hf := L.formula_forward φ names (hv.symm ▸ h)
  have ht : T.ofName ∘ L.mapName ∘ names = L.liftFun ∘ v := by
    rw [← hv]
    rfl
  exact ht ▸ hf

theorem liftFun_formula_iff {n : ℕ} (φ : SetTheorySemisentence n) (v : Fin n → S.Model) :
    φ.Evalb v ↔ φ.Evalb (L.liftFun ∘ v) := by
  classical
  constructor
  · exact L.liftFun_formula_forward φ v
  · intro h
    by_contra hn
    have hf := L.liftFun_formula_forward (∼φ) v (by simpa using hn)
    have hn' : ¬φ.Evalb (L.liftFun ∘ v) := by simpa using hf
    exact hn' h

noncomputable def elementaryLift : ElementaryMap S.Model T.Model where
  toFun := L.liftFun
  elementary φ v a := elementary_of_semisentences L.liftFun L.liftFun_formula_iff φ v a

theorem elementaryLift_ofName (τ : ForcingName S.P) :
    L.elementaryLift (S.ofName τ) = T.ofName (L.mapName τ) := rfl

theorem elementaryLift_check (hone : j S.one = T.one) (x : V) :
    L.elementaryLift (S.check x) = T.check (j x) := by
  change T.ofName (L.mapName ⟨checkName S.one x, checkName_isName S.top.1 x⟩) =
    T.ofName ⟨checkName T.one (j x), checkName_isName T.top.1 (j x)⟩
  apply congrArg T.ofName
  apply Subtype.ext
  exact (j.map_checkName S.one x).trans (congrArg (fun o ↦ checkName o (j x)) hone)

end LiftData
end ForcingContext
end ZFVP
