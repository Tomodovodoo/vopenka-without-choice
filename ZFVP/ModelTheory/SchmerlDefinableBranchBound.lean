import ZFVP.ModelTheory.SchmerlCofinalSpecialization
import Foundation.FirstOrder.Basic.Coding

/-! An aleph-one structure in a countable language has at most aleph-one
definable subsets, including parameters. The proof constructs finite parameter
codes and bounds those codes by finite lists of model elements and one natural
number. This derives the branch bound needed by the specialization construction
from definability of branches.
-/

namespace ZFVP.Schmerl

open Set Cardinal LO LO.FirstOrder

universe u v

variable (L : Language.{0}) (M : Type u)

/-- A first-order definition with a finite tuple of parameters. -/
def DefinableSetCode := Σ k : ℕ, Semisentence L (1 + k) × (Fin k → M)

namespace DefinableSetCode

variable {L M} [Structure L M]

def Interprets (c : DefinableSetCode L M) (x : M) : Prop :=
  c.2.1.Evalb (Fin.append (fun _ : Fin 1 ↦ x) c.2.2)

/-- Move the finitely many free parameters of a Foundation formula to a finite
tuple. This produces actual syntax for the code-counting argument. -/
theorem exists_code [Nonempty M] {P : M → Prop} (hP : L-predicate[M] P) :
    ∃ c : DefinableSetCode L M, ∀ x, c.Interprets x ↔ P x := by
  classical
  let : L-predicate[M] P := hP
  obtain ⟨φ, hφ⟩ := Language.Definable.definable (L := L) (M := M)
    (P := fun v : Fin 1 → M ↦ P (v 0))
  let S := φ.freeVariables
  let k := Fintype.card {x // x ∈ S}
  let e : {x // x ∈ S} ≃ Fin k := Fintype.equivFin _
  let ix : M → Fin (k + 1) := fun x ↦ if h : x ∈ S then (e ⟨x, h⟩).succ else 0
  let ρ : Rew L M 1 Empty (1 + (k + 1)) :=
    Rew.bind (fun i ↦ .bvar (Fin.castAdd (k + 1) i))
      (fun x ↦ .bvar (Fin.natAdd 1 (ix x)))
  let a : Fin (k + 1) → M :=
    Fin.cases (Classical.choice ‹Nonempty M›) (fun i ↦ (e.symm i).val)
  refine ⟨⟨k + 1, ρ ▹ φ, a⟩, ?_⟩
  intro x
  let b : Fin 1 → M := fun _ ↦ x
  let c : Fin (1 + (k + 1)) → M := Fin.append b a
  have hcb (i : Fin 1) : c (Fin.castAdd (k + 1) i) = b i := by simp [c]
  have hca (y : M) (hy : φ.FVar? y) : c (Fin.natAdd 1 (ix y)) = y := by
    have hyS : y ∈ S := hy
    simp [c, a, ix, hyS]
  have hs : (ρ ▹ φ).Evalb c ↔ φ.Eval b id := by
    rw [Semiformula.eval_rew]
    have hb : (Semiterm.val c Empty.elim ∘ ρ ∘ Semiterm.bvar) = b := by
      funext i
      simpa [ρ, Function.comp_def] using hcb i
    rw [hb]
    apply Semiformula.eval_iff_of_funEqOn
    intro y hy
    simpa [ρ, Function.comp_def] using hca y hy
  exact hs.trans (hφ b)

variable [L.Encodable]

/-- A finite tuple plus the natural-number syntax code determines a definition. -/
def encode (c : DefinableSetCode L M) : List M × ℕ :=
  (List.ofFn c.2.2, Encodable.encode c.2.1)

omit [Structure L M] in
theorem encode_injective : Function.Injective (encode (L := L) (M := M)) := by
  rintro ⟨k, φ, a⟩ ⟨l, ψ, b⟩ h
  have hk : k = l := by
    simpa only [encode, List.length_ofFn] using congrArg (fun p : List M × ℕ ↦ p.1.length) h
  subst l
  have ha : a = b := List.ofFn_inj.mp (congrArg Prod.fst h)
  have hφ : φ = ψ := Encodable.encode_injective (congrArg Prod.snd h)
  subst b
  subst ψ
  rfl

omit [Structure L M] in
theorem cardinal_le_aleph_one (hM : Cardinal.mk M ≤ Cardinal.aleph 1) :
    Cardinal.mk (DefinableSetCode L M) ≤ Cardinal.aleph 1 := by
  have hzero : Cardinal.aleph0 ≤ Cardinal.aleph 1 := Cardinal.aleph0_lt_aleph_one.le
  calc
    Cardinal.mk (DefinableSetCode L M) ≤ Cardinal.mk (List M × ℕ) :=
      Cardinal.mk_le_of_injective encode_injective
    _ = Cardinal.mk (List M) * Cardinal.aleph0 := by simp
    _ ≤ max (max (Cardinal.mk (List M)) Cardinal.aleph0) Cardinal.aleph0 :=
      Cardinal.mul_le_max _ _
    _ ≤ Cardinal.aleph 1 :=
      max_le (max_le ((Cardinal.mk_list_le_max M).trans (max_le hzero hM)) hzero) hzero

end DefinableSetCode

variable {L M} [Structure L M] [Nonempty M] [L.Encodable]

/-- Any injectively indexed family of parametrically definable predicates has
cardinality at most aleph-one when the ambient structure does. -/
theorem cardinal_definable_family_le_aleph_one {J : Type u} (P : J → M → Prop)
    (hinj : Function.Injective P) (hdef : ∀ j, L-predicate[M] (P j))
    (hM : Cardinal.mk M ≤ Cardinal.aleph 1) : Cardinal.mk J ≤ Cardinal.aleph 1 := by
  classical
  choose code hcode using fun j ↦ DefinableSetCode.exists_code (hdef j)
  have hcodeinj : Function.Injective code := by
    intro i j hij
    apply hinj
    funext x
    apply propext
    exact (hcode i x).symm.trans (hij ▸ hcode j x)
  exact (Cardinal.mk_le_of_injective hcodeinj).trans
    (DefinableSetCode.cardinal_le_aleph_one hM)

/-- Definable branch images in an ambient structure give the exact branch bound
needed for specialization. The tree carrier need only embed in that structure. -/
theorem cardinal_branches_le_aleph_one {T : Type u} {I : Type v}
    [PartialOrder T] [LinearOrder I] (R : RankedTree T I) (e : T ↪ M)
    (hdef : ∀ B, R.IsBranch B → L-predicate[M] (fun x ↦ x ∈ e '' B))
    (hM : Cardinal.mk M ≤ Cardinal.aleph 1) :
    Cardinal.mk {B : Set T // R.IsBranch B} ≤ Cardinal.aleph 1 := by
  apply cardinal_definable_family_le_aleph_one
    (fun B : {B : Set T // R.IsBranch B} ↦ fun x ↦ x ∈ e '' B.val) _
    (fun B ↦ hdef B.val B.property) hM
  intro A B hab
  apply Subtype.ext
  apply (Set.image_injective.mpr e.injective)
  exact Set.ext (fun x ↦ iff_of_eq (congrFun hab x))

end ZFVP.Schmerl
