import ZFVP.Syntax.CloseTailParameters
import ZFVP.Syntax.BoundedStandardTuples
import ZFVP.SetTheory.UniformNumerals

/-! A finite list of free parameters can be represented by one internal tuple.
This connects ordinary definable classes to the two-variable Vopenka scheme. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def packedParameterEntryFormula (i : ℕ) : SetTheorySemisentence 2 :=
  f“x p. x = !value.dfn p (!(numeralFormula i))”

def packedParameterEntry {n : ℕ} (i : Fin n) : SetTheorySemisentence (2 + n) :=
  boundIndexRew ![i.addCast 2, (1 : Fin 2).addNat n] ▹ packedParameterEntryFormula i.val

def packedParameterBody {n : ℕ} (φ : SetTheorySemisentence (n + 1)) : SetTheorySemisentence (2 + n) :=
  (finiteConjunction (fun i : Fin n ↦ packedParameterEntry i)).and
    (boundIndexRew (Fin.cases ((0 : Fin 2).addNat n) (fun i : Fin n ↦ i.addCast 2)) ▹ φ)

def packFiniteParameters {n : ℕ} (φ : SetTheorySemisentence (n + 1)) : SetTheorySemisentence 2 :=
  ∃¹^[n] packedParameterBody φ

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_packedParameterEntryFormula (i : ℕ) (x p : V) :
    (packedParameterEntryFormula i).Evalb ![x, p] ↔ x = p ‘ (i : V) := by
  simp [packedParameterEntryFormula]

theorem eval_packedParameterEntry {n : ℕ} (i : Fin n) (e : Fin n → V) (x p : V) :
    (packedParameterEntry i).Evalb (Matrix.appendr e ![x, p]) ↔ e i = p ‘ (i.val : V) := by
  rw [packedParameterEntry, eval_boundIndexRew]
  have hv : Matrix.appendr e ![x, p] ∘ ![i.addCast 2, (1 : Fin 2).addNat n] = ![e i, p] := by
    funext j
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ Fin.elim0 k) j) j <;> simp
  rw [hv]
  exact eval_packedParameterEntryFormula _ _ _

theorem eval_packedParameterBody {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (e : Fin n → V) (x p : V) :
    (packedParameterBody φ).Evalb (Matrix.appendr e ![x, p]) ↔
      (∀ i, e i = p ‘ (i.val : V)) ∧ φ.Evalb (x :> e) := by
  change ((finiteConjunction (fun i : Fin n ↦ packedParameterEntry i)).Evalb (Matrix.appendr e ![x, p]) ∧
    (boundIndexRew (Fin.cases ((0 : Fin 2).addNat n) (fun i : Fin n ↦ i.addCast 2)) ▹ φ).Evalb
      (Matrix.appendr e ![x, p])) ↔ _
  rw [eval_finiteConjunction, eval_boundIndexRew]
  have hv : Matrix.appendr e ![x, p] ∘
      Fin.cases ((0 : Fin 2).addNat n) (fun i : Fin n ↦ i.addCast 2) = x :> e := by
    funext j
    refine Fin.cases ?_ (fun i ↦ ?_) j <;> simp
  rw [hv]
  exact and_congr (forall_congr' (fun i ↦ eval_packedParameterEntry i e x p)) Iff.rfl

theorem eval_packFiniteParameters {n : ℕ} (φ : SetTheorySemisentence (n + 1)) (x p : V) :
    (packFiniteParameters φ).Evalb ![x, p] ↔ φ.Evalb (x :> fun i : Fin n ↦ p ‘ (i.val : V)) := by
  change (∃¹^[n] packedParameterBody φ).Eval ![x, p] Empty.elim ↔ _
  rw [Semiformula.eval_exsItr]
  change (∃ e, (packedParameterBody φ).Evalb (Matrix.appendr e ![x, p])) ↔ _
  simp only [eval_packedParameterBody]
  constructor
  · rintro ⟨e, he, hφ⟩
    have heq : e = fun i : Fin n ↦ p ‘ (i.val : V) := funext he
    rwa [heq] at hφ
  · intro hφ
    exact ⟨_, fun _ ↦ rfl, hφ⟩

theorem eval_packFiniteParameters_standardTuple {n : ℕ} (φ : SetTheorySemisentence (n + 1))
    (x : V) (e : Fin n → V) :
    (packFiniteParameters φ).Evalb ![x, standardTuple e] ↔ φ.Evalb (x :> e) := by
  rw [eval_packFiniteParameters]
  have he : (fun i : Fin n ↦ (standardTuple e) ‘ (i.val : V)) = e := funext (value_standardTuple e)
  rw [he]

theorem definable_predicate_one_parameter (P : V → Prop) (hP : ℒₛₑₜ-predicate P) :
    ∃ φ : SetTheorySemisentence 2, ∃ p : V, ∀ x : V, φ.Evalb ![x, p] ↔ P x := by
  classical
  let : Inhabited V := Classical.inhabited_of_nonempty'
  obtain ⟨ψ, hψ⟩ := hP.definable
  let θ : SetTheorySemiproposition 1 := Rew.rewriteMap ψ.idxOfFVar ▹ ψ
  let e : ℕ → V := ψ.enumerateFVar
  refine ⟨packFiniteParameters (closeTailParameters θ), standardTuple (fun i : Fin θ.fvSup ↦ e i.val), ?_⟩
  intro x
  rw [eval_packFiniteParameters_standardTuple]
  have hv : prefixVector ![x] (fun i : Fin θ.fvSup ↦ e i.val) = x :> (fun i : Fin θ.fvSup ↦ e i.val) := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact prefixVector_front ![x] _ (0 : Fin 1)
    · exact prefixVector_tail ![x] _ j
  rw [← hv, eval_closeTailParameters]
  change (Rew.rewriteMap ψ.idxOfFVar ▹ ψ).Eval ![x] ψ.enumerateFVar ↔ P x
  rw [Semiformula.eval_rewriteMap]
  exact (Semiformula.eval_enumerateFVar_idxOfFVar_eq_id ψ ![x]).trans (hψ ![x])

end ZFVP
