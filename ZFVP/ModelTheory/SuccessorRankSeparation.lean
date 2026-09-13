import ZFVP.ModelTheory.SuccessorRankEmbedding

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

private theorem eval_and {W : Type*} [SetStructure W] {n : ℕ}
    (φ ψ : SetTheorySemisentence n) (v : Fin n → W) :
    (φ.and ψ).Evalb v ↔ φ.Evalb v ∧ ψ.Evalb v := Iff.rfl

def separationSpecification {n : ℕ} (φ : SetTheorySemisentence (n + 1)) :
    SetTheorySemisentence (n + 2) :=
  ∀¹ ((Semiformula.rel Language.Set.Rel.mem ![.bvar 0, .bvar 1]) 🡘
    ((Semiformula.rel Language.Set.Rel.mem ![.bvar 0, .bvar 2]).and
      (φ.subst (.bvar 0 :> fun i : Fin n ↦ .bvar i.succ.succ.succ))))

theorem eval_separationSpecification {W : Type*} [SetStructure W] {n : ℕ}
    (φ : SetTheorySemisentence (n + 1)) (S X : W) (v : Fin n → W) :
    (separationSpecification φ).Evalb (S :> X :> v) ↔
      ∀ x : W, x ∈ S ↔ x ∈ X ∧ φ.Evalb (x :> v) := by
  simp [separationSpecification, eval_and, Semiformula.eval_substs, Matrix.comp_vecCons',
    Function.comp_def, Structure.rel]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem successorRankEmbedding_separation {δ ε e S X : V}
    (hδ : Cn 1 δ) (hε : Cn 1 ε)
    (h : IsCodedMembershipEmbedding (hierarchy (succ δ)) (hierarchy (succ ε)) e)
    {n : ℕ} {p : LevyPolarity} {φ : SetTheorySemisentence (n + 1)}
    (hφ : IsLevyFormula p 1 φ) (v : Fin n → V)
    (hv : ∀ i, v i ∈ hierarchy δ) (hS : S ∈ hierarchy δ) (hX : X ∈ hierarchy δ)
    (hsep : ∀ x : V, x ∈ S ↔ x ∈ X ∧ φ.Evalb (x :> v)) :
    ∀ z : V, z ∈ e ‘ S ↔ z ∈ e ‘ X ∧ φ.Evalb (z :> fun i ↦ e ‘ (v i)) := by
  let := hδ.ordinal
  let := hε.ordinal
  let j := successorRankElementaryMap h
  let s : SetDomain (hierarchy δ) := ⟨S, hS⟩
  let x : SetDomain (hierarchy δ) := ⟨X, hX⟩
  let b : Fin n → SetDomain (hierarchy δ) := fun i ↦ ⟨v i, hv i⟩
  have hsource : (separationSpecification φ).Evalb (s :> x :> b) := by
    apply (eval_separationSpecification φ s x b).mpr
    intro a
    have hc := hδ.levy_correct hφ (a :> b)
    have hb : (fun i ↦ ((a :> b) i).val) = (a.val :> v) := by
      funext i
      exact Fin.cases rfl (fun _ ↦ rfl) i
    rw [hb] at hc
    exact (hsep a.val).trans (and_congr Iff.rfl hc.symm)
  have ht : (separationSpecification φ).Evalb (j ∘ (s :> x :> b)) := by
    have hj := j.elementary (separationSpecification φ) (s :> x :> b) Empty.elim
    have hz : j ∘ (Empty.elim : Empty → SetDomain (hierarchy δ)) = Empty.elim := by
      funext i
      exact Empty.elim i
    rw [hz] at hj
    exact hj.mp hsource
  have hjb : j ∘ (s :> x :> b) = (j s :> j x :> j ∘ b) := by
    funext i
    exact Fin.cases rfl (fun k ↦ Fin.cases rfl (fun _ ↦ rfl) k) i
  rw [hjb] at ht
  have hall := (eval_separationSpecification φ (j s) (j x) (j ∘ b)).mp ht
  have hlocal (a : SetDomain (hierarchy ε)) :
      a.val ∈ e ‘ S ↔ a.val ∈ e ‘ X ∧ φ.Evalb (a.val :> fun i ↦ e ‘ (v i)) := by
    have hc := hε.levy_correct hφ (a :> j ∘ b)
    have hb : (fun i ↦ ((a :> j ∘ b) i).val) = (a.val :> fun i ↦ e ‘ (v i)) := by
      funext i
      exact Fin.cases rfl (fun _ ↦ rfl) i
    rw [hb] at hc
    exact (hall a).trans (and_congr Iff.rfl hc)
  intro z
  constructor
  · intro hz
    have hs : e ‘ S ∈ hierarchy ε := (j s).property
    exact (hlocal ⟨z, (hierarchy_transitive ε).mem_trans hz hs⟩).mp hz
  · intro hz
    have hx : e ‘ X ∈ hierarchy ε := (j x).property
    exact (hlocal ⟨z, (hierarchy_transitive ε).mem_trans hz.1 hx⟩).mpr hz

end ZFVP

