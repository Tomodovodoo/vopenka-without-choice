import ZFVP.ModelTheory.InfinitaryGenericUniversal

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace HenkinConstruction.FragmentExtension.GenericConditionChain
open HenkinLanguage FragmentClosure FiniteCondition
variable {L : Language} [L.Eq] [L.Encodable] {Γ : Set (Sentence L)}
  {S : Set (TaggedFormula (limit L))}
  {H : FragmentExtension Γ (FragmentClosure.carrier (SequenceClosure.carrier S))}
  {p₀ : H.FiniteCondition} (C : GenericConditionChain H p₀)

theorem eval_rename_iff {n m} (φ : Formula (limit L) n) (ρ : Fin n → Fin m)
    (ts : Fin m → CoordinateTerm (limit L)) :
    CoordinateTerm.Eval C.point (φ.rename ρ) ts ↔ CoordinateTerm.Eval C.point φ (ts ∘ ρ) := by
  constructor
  · rintro ⟨k, hs, hh⟩
    refine ⟨k, fun i ↦ hs (ρ i), ?_⟩
    intro b hb
    exact (Formula.weakEval_rename _ _ _ _).mp (hh b hb)
  · rintro ⟨k, hk⟩
    obtain ⟨j, hj⟩ := C.coordinate_cofinal (CoordinateTerm.arity ts)
    have hg := (C.refines (Nat.le_max_right k j)).choose
    have h : CoordinateTerm.arity ts ≤ 1 + (C.point (max k j)).1 := by omega
    obtain ⟨ht, hh⟩ := CoordinateTerm.evalAt_persistent (C.refines (Nat.le_max_left k j)) hk
    refine ⟨max k j, fun i ↦ (CoordinateTerm.le_arity ts i).trans h, ?_⟩
    intro b hb
    exact (Formula.weakEval_rename _ _ _ _).mpr (hh b hb)

theorem eval_liftRename_iff {n m} (φ : Formula (limit L) (n + 1))
    (ρ : Fin n → Fin m) (t : CoordinateTerm (limit L)) (ts : Fin m → CoordinateTerm (limit L)) :
    CoordinateTerm.Eval C.point (φ.rename (liftRenaming ρ)) (t :> ts) ↔
      CoordinateTerm.Eval C.point φ (t :> (ts ∘ ρ)) := by
  rw [C.eval_rename_iff, compose_liftRenaming]

def genericFiber {n} (φ : Formula (limit L) (n + 1))
    (ts : Fin n → CoordinateTerm (limit L)) : Set C.ExtensionDomain :=
  {x | CoordinateTerm.Eval C.point φ (x.out :> ts)}

theorem termClass_mem_genericFiber {n} (φ : Formula (limit L) (n + 1))
    (ts : Fin n → CoordinateTerm (limit L)) (t : CoordinateTerm (limit L)) :
    C.termClass t ∈ C.genericFiber φ ts ↔ CoordinateTerm.Eval C.point φ (t :> ts) := by
  apply CoordinateTerm.eval_congr_iff C.point C.refines
  intro i
  cases i using Fin.cases with
  | zero => exact @Quotient.mk_out _ C.coordinateSetoid t
  | succ i => exact CoordinateTerm.rel_refl C.point C.coordinate_cofinal (ts i)

/-- Inclusion of generic fibers controls their Q labels even when the parameter
contexts and their representatives differ. No quantifier on the quotient is used. -/
theorem q_label_of_fiber_subset {n m} {φ : Formula (limit L) (n + 1)}
    {ψ : Formula (limit L) (m + 1)}
    (hφ : ⟨n + 1, φ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    (hψ : ⟨m + 1, ψ⟩ ∈ FragmentClosure.carrier (SequenceClosure.carrier S))
    {ts : Fin n → CoordinateTerm (limit L)} {us : Fin m → CoordinateTerm (limit L)}
    (hsub : C.genericFiber φ ts ⊆ C.genericFiber ψ us)
    (hq : CoordinateTerm.Eval C.point (.q φ) ts) : CoordinateTerm.Eval C.point (.q ψ) us := by
  let v := Fin.append ts us
  let ρ : Fin n → Fin (n + m) := Fin.castAdd m
  let σ : Fin m → Fin (n + m) := Fin.natAdd n
  have hleft : v ∘ ρ = ts := by funext i; exact Fin.append_left ts us i
  have hright : v ∘ σ = us := by funext i; exact Fin.append_right ts us i
  let φ' := φ.rename (liftRenaming ρ)
  let ψ' := ψ.rename (liftRenaming σ)
  have hf := rename_closed hφ (liftRenaming ρ)
  have hg := rename_closed hψ (liftRenaming σ)
  have hall : CoordinateTerm.Eval C.point (φ'.imp ψ').all v := by
    apply (C.eval_all_iff (imp_closed hf hg) v).mpr
    intro t
    apply (C.eval_imp_iff hf hg (t :> v)).mpr
    intro ht
    have hp : CoordinateTerm.Eval C.point φ (t :> ts) := by
      simpa only [hleft] using (C.eval_liftRename_iff φ ρ t v).mp ht
    have hh := hsub ((C.termClass_mem_genericFiber φ ts t).mpr hp)
    have hu := (C.termClass_mem_genericFiber ψ us t).mp hh
    apply (C.eval_liftRename_iff ψ σ t v).mpr
    simpa only [hright] using hu
  have hq' : CoordinateTerm.Eval C.point (.q φ') v := by
    change CoordinateTerm.Eval C.point ((Formula.q φ).rename ρ) v
    apply (C.eval_rename_iff (.q φ) ρ v).mpr
    simpa only [hleft] using hq
  have hq'' := C.eval_q_monotone hall hq'
  change CoordinateTerm.Eval C.point ((Formula.q ψ).rename σ) v at hq''
  simpa only [hright] using (C.eval_rename_iff (.q ψ) σ v).mp hq''

end HenkinConstruction.FragmentExtension.GenericConditionChain
end ZFVP.Infinitary
