import ZFVP.SetTheory.BoundedCodingPrimitives
import ZFVP.SetTheory.DefinableGraph

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def graphAssemblyRow {n : ℕ} (φ : SetTheorySemisentence (n + 2))
    (p x : Fin (n + 6)) : SetTheorySemisentence (n + 6) :=
  (boundedKpairFormula.subst ![.bvar p, .bvar x, .bvar 0]).and
    (φ.subst (Fin.cases (.bvar 0) (Fin.cases (.bvar x) (fun i ↦ .bvar (i.addNat 6)))))

def graphAssemblyFormula {n : ℕ} (φ : SetTheorySemisentence (n + 2)) : SetTheorySemisentence (n + 2) :=
  (boundedSetAll (.bvar 0) (boundedSetExs (.bvar 2) (boundedSetExs (.bvar 1)
    (boundedSetExs (.bvar 0) (graphAssemblyRow φ 3 2))))).and
  (boundedSetAll (.bvar 1) (boundedSetExs (.bvar 1) (boundedSetExs (.bvar 0)
    (boundedSetExs (.bvar 0) (graphAssemblyRow φ 2 3)))))

theorem graphAssemblyRow_levy {n k : ℕ} {pol : LevyPolarity} {φ : SetTheorySemisentence (n + 2)}
    (hφ : IsLevyFormula pol k φ) (p x : Fin (n + 6)) : IsLevyFormula pol k (graphAssemblyRow φ p x) :=
  .and (.bounded (boundedKpairFormula_bounded.subst _)) (hφ.subst _)

theorem graphAssemblyFormula_levy {n k : ℕ} {pol : LevyPolarity} {φ : SetTheorySemisentence (n + 2)}
    (hφ : IsLevyFormula pol k φ) : IsLevyFormula pol k (graphAssemblyFormula φ) :=
  .and (.boundedAll _ (.boundedExs _ (.boundedExs _ (.boundedExs _ (graphAssemblyRow_levy hφ _ _)))))
    (.boundedAll _ (.boundedExs _ (.boundedExs _ (.boundedExs _ (graphAssemblyRow_levy hφ _ _)))))

theorem graphAssemblyFormula_bounded {n : ℕ} {φ : SetTheorySemisentence (n + 2)}
    (hφ : IsBoundedSetFormula φ) : IsBoundedSetFormula (graphAssemblyFormula φ) :=
  (graphAssemblyFormula_levy (IsLevyFormula.bounded (p := .sigma) (k := 0) hφ)).zero_bounded rfl

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_graphAssemblyRow {n : ℕ} (φ : SetTheorySemisentence (n + 2))
    (p x : Fin (n + 6)) (v : Fin (n + 6) → V) :
    (graphAssemblyRow φ p x).Evalb v ↔
      v p = ⟨v x, v 0⟩ₖ ∧ φ.Evalb (v 0 :> v x :> fun i ↦ v (i.addNat 6)) := by
  change ((boundedKpairFormula.subst ![.bvar p, .bvar x, .bvar 0]).Evalb v ∧
    (φ.subst (Fin.cases (.bvar 0) (Fin.cases (.bvar x) (fun i ↦ .bvar (i.addNat 6))))).Evalb v) ↔ _
  simp [Semiformula.subst, Semiformula.eval_substs, Function.comp_def, Semiformula.Evalb]
  intro _
  apply Iff.of_eq
  congr 2
  funext i
  exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun _ ↦ rfl) j) i

theorem eval_graphAssemblyFormula_body {n : ℕ} (φ : SetTheorySemisentence (n + 2))
    (G A : V) (v : Fin n → V) :
    (graphAssemblyFormula φ).Evalb (G :> A :> v) ↔
      (∀ p ∈ G, ∃ x ∈ A, ∃ d ∈ p, ∃ y ∈ d, p = ⟨x, y⟩ₖ ∧ φ.Evalb (y :> x :> v)) ∧
      ∀ x ∈ A, ∃ p ∈ G, ∃ d ∈ p, ∃ y ∈ d, p = ⟨x, y⟩ₖ ∧ φ.Evalb (y :> x :> v) := by
  change ((boundedSetAll (.bvar 0) (boundedSetExs (.bvar 2) (boundedSetExs (.bvar 1)
    (boundedSetExs (.bvar 0) (graphAssemblyRow φ 3 2))))).Evalb (G :> A :> v) ∧
    (boundedSetAll (.bvar 1) (boundedSetExs (.bvar 1) (boundedSetExs (.bvar 0)
    (boundedSetExs (.bvar 0) (graphAssemblyRow φ 2 3))))).Evalb (G :> A :> v)) ↔ _
  simp [eval_boundedSetAll, eval_boundedSetExs, eval_graphAssemblyRow, Fin.addNat]

theorem eval_graphAssemblyFormula {n : ℕ} (φ : SetTheorySemisentence (n + 2))
    (G A : V) (v : Fin n → V) (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (he : ∀ x ∈ A, ∀ y : V, φ.Evalb (y :> x :> v) ↔ y = F x) :
    (graphAssemblyFormula φ).Evalb (G :> A :> v) ↔ G = definableGraph A F hF := by
  rw [eval_graphAssemblyFormula_body]
  constructor
  · rintro ⟨hf, hb⟩
    apply mem_ext
    intro p
    constructor
    · intro hp
      obtain ⟨x, hx, d, _, y, _, hp', hy⟩ := hf p hp
      have hy' := (he x hx y).mp hy
      exact (mem_definableGraph_iff A F hF p).mpr ⟨x, hx, by simpa [hy'] using hp'⟩
    · intro hp
      obtain ⟨x, hx, rfl⟩ := (mem_definableGraph_iff A F hF p).mp hp
      obtain ⟨q, hq, d, _, y, _, rfl, hy⟩ := hb x hx
      rwa [(he x hx y).mp hy] at hq
  · rintro rfl
    constructor
    · intro p hp
      obtain ⟨x, hx, rfl⟩ := (mem_definableGraph_iff A F hF p).mp hp
      exact ⟨x, hx, doubleton x (F x), by simp [kpair, pair_eq_doubleton],
        F x, by simp, rfl, (he x hx (F x)).mpr rfl⟩
    · intro x hx
      exact ⟨⟨x, F x⟩ₖ, (pair_mem_definableGraph_iff A F hF x (F x)).mpr ⟨hx, rfl⟩,
        doubleton x (F x), by simp [kpair, pair_eq_doubleton],
        F x, by simp, rfl, (he x hx (F x)).mpr rfl⟩

end ZFVP
