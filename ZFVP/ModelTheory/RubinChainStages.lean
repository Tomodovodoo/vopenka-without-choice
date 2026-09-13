import ZFVP.SetTheory.ElementaryMap
import ZFVP.SetTheory.DiamondOmegaOne
import Mathlib.Data.Fintype.Order
import Mathlib.SetTheory.Cardinal.Arithmetic

/-! # Vocabulary for an ω₁-chain of subsets of a fixed model

Enayat's ω₁-length construction (Stage 1 of Theorem A.1) builds its final model as the union of an
increasing ω₁-chain of countable elementary submodels. This file fixes the vocabulary for talking
about such a chain of subsets `A : OmegaOne → Set W` of a fixed structure `W`, and proves the
three utility facts the construction uses. No set theory is proved here.

* A subset of `W` is a structure for the membership language by restricting `∈`. The instance is
  already in Foundation (`LO.FirstOrder.SetTheory.submodel`); `submodelSetStructure` is a name for
  it and `stage_mem_iff` the simp lemma that unfolds membership in a stage.
* `DefinableOver A P` says `P` is defined by a formula all of whose parameters lie in `A`, and
  `DefinableOverRel` is the two-variable form. Both are monotone in `A`, both imply plain
  definability over `W`, and both pull back along an elementary map whose image covers `A`.
* `exists_definableOver_of_definable` puts the parameters of any definable predicate into a single
  stage of an increasing chain that covers `W`: a formula has finitely many free variables and
  finitely many stages have an upper bound in `ω₁`.
* `exists_strictMono_ge` reindexes `ω₁` strictly monotonically above a given stage, by adding a
  fixed ordinal on the left.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u v

variable {W : Type u} [SetStructure W]

/-! ## Stages as structures -/

/-- A subset of a model is a structure for the membership language, with membership restricted
from the ambient model. This is Foundation's `LO.FirstOrder.SetTheory.submodel`; the name is
given here because the chain construction refers to it. -/
abbrev submodelSetStructure (A : Set W) : SetStructure ↥A := inferInstance

/-- Membership inside a stage is membership in the ambient model. -/
@[simp] theorem stage_mem_iff (A : Set W) (x y : ↥A) : x ∈ y ↔ (x : W) ∈ (y : W) := Iff.rfl

/-! ## Definability with parameters from a fixed set -/

/-- `P` is defined by a first-order formula whose parameters all lie in `A`. The parameters are
carried by a separate index type `Fin n` so that the requirement "each parameter is in `A`" is a
statement about the tuple `f`. -/
def DefinableOver (A : Set W) (P : W → Prop) : Prop :=
  ∃ (n : ℕ) (φ : SetTheorySemiformula (Fin n) 1) (f : Fin n → W),
    (∀ i, f i ∈ A) ∧ ∀ x, P x ↔ φ.Eval ![x] f

/-- The two-variable form of `DefinableOver`. -/
def DefinableOverRel (A : Set W) (R : W → W → Prop) : Prop :=
  ∃ (n : ℕ) (φ : SetTheorySemiformula (Fin n) 2) (f : Fin n → W),
    (∀ i, f i ∈ A) ∧ ∀ x y, R x y ↔ φ.Eval ![x, y] f

/-- Enlarging the parameter set keeps a predicate definable over it. -/
theorem DefinableOver.mono {A B : Set W} {P : W → Prop} (h : DefinableOver A P) (hAB : A ⊆ B) :
    DefinableOver B P := by
  obtain ⟨n, φ, f, hf, hP⟩ := h
  exact ⟨n, φ, f, fun i ↦ hAB (hf i), hP⟩

/-- Enlarging the parameter set keeps a relation definable over it. -/
theorem DefinableOverRel.mono {A B : Set W} {R : W → W → Prop} (h : DefinableOverRel A R)
    (hAB : A ⊆ B) : DefinableOverRel B R := by
  obtain ⟨n, φ, f, hf, hR⟩ := h
  exact ⟨n, φ, f, fun i ↦ hAB (hf i), hR⟩

/-- A predicate definable with parameters from a set is definable over the whole model: rewrite
the parameter indices to the parameters themselves. -/
theorem DefinableOver.definable {A : Set W} {P : W → Prop} (h : DefinableOver A P) :
    ℒₛₑₜ-predicate[W] P := by
  obtain ⟨n, φ, f, -, hP⟩ := h
  refine ⟨⟨Rew.rewriteMap f ▹ φ, fun v ↦ ?_⟩⟩
  have hv := hP (v 0)
  rw [← Matrix.fun_eq_vec_one v] at hv
  rw [Semiformula.eval_rewriteMap]
  exact hv.symm

/-- A relation definable with parameters from a set is definable over the whole model. -/
theorem DefinableOverRel.definable {A : Set W} {R : W → W → Prop} (h : DefinableOverRel A R) :
    ℒₛₑₜ-relation[W] R := by
  obtain ⟨n, φ, f, -, hR⟩ := h
  refine ⟨⟨Rew.rewriteMap f ▹ φ, fun v ↦ ?_⟩⟩
  have hv := hR (v 0) (v 1)
  rw [← Matrix.fun_eq_vec_two v] at hv
  rw [Semiformula.eval_rewriteMap]
  exact hv.symm

/-- Pulling a predicate back along an elementary map whose image contains all the parameters. The
preimages of the parameters are the parameters of the pulled back formula, and elementarity of
`j` for formulas with free variables in `Fin n` transfers the evaluation. -/
theorem DefinableOver.pullback {N : Type v} [SetStructure N] (j : ElementaryMap N W)
    (A : Set W) (hA : ∀ x : W, x ∈ A → ∃ y : N, j y = x) {P : W → Prop}
    (h : DefinableOver A P) : ℒₛₑₜ-predicate[N] (fun y ↦ P (j y)) := by
  obtain ⟨n, φ, f, hf, hP⟩ := h
  choose g hg using fun i ↦ hA (f i) (hf i)
  have hfg : (j.toFun ∘ g) = f := funext hg
  have key : ∀ y : N, P (j y) ↔ φ.Eval ![y] g := by
    intro y
    rw [hP (j y)]
    have h1 := j.elementary φ ![y] g
    have hb : (j.toFun ∘ ![y]) = ![j y] := Matrix.fun_eq_vec_one _
    rw [hb, hfg] at h1
    exact h1.symm
  refine ⟨⟨Rew.rewriteMap g ▹ φ, fun v ↦ ?_⟩⟩
  have hv := key (v 0)
  rw [← Matrix.fun_eq_vec_one v] at hv
  rw [Semiformula.eval_rewriteMap]
  exact hv.symm

/-- The two-variable form of `DefinableOver.pullback`. -/
theorem DefinableOverRel.pullback {N : Type v} [SetStructure N] (j : ElementaryMap N W)
    (A : Set W) (hA : ∀ x : W, x ∈ A → ∃ y : N, j y = x) {R : W → W → Prop}
    (h : DefinableOverRel A R) : ℒₛₑₜ-relation[N] (fun y z ↦ R (j y) (j z)) := by
  obtain ⟨n, φ, f, hf, hR⟩ := h
  choose g hg using fun i ↦ hA (f i) (hf i)
  have hfg : (j.toFun ∘ g) = f := funext hg
  have key : ∀ y z : N, R (j y) (j z) ↔ φ.Eval ![y, z] g := by
    intro y z
    rw [hR (j y) (j z)]
    have h1 := j.elementary φ ![y, z] g
    have hb : (j.toFun ∘ ![y, z]) = ![j y, j z] := Matrix.fun_eq_vec_two _
    rw [hb, hfg] at h1
    exact h1.symm
  refine ⟨⟨Rew.rewriteMap g ▹ φ, fun v ↦ ?_⟩⟩
  have hv := key (v 0) (v 1)
  rw [← Matrix.fun_eq_vec_two v] at hv
  rw [Semiformula.eval_rewriteMap]
  exact hv.symm

/-! ## Collecting the parameters of a formula into one stage -/

/-- The free variables of a formula over `W` can be replaced by an explicitly indexed tuple of
parameters lying in a single stage of an increasing chain that covers `W`. The formula has
finitely many free variables, each of them lies in some stage, and finitely many stages have an
upper bound in `ω₁`. -/
theorem exists_params_in_stage {A : OmegaOne → Set W} (hmono : Monotone A)
    (hcover : ∀ x : W, ∃ α, x ∈ A α) {k : ℕ} (φ : SetTheorySemiformula W k) :
    ∃ (α : OmegaOne) (n : ℕ) (ψ : SetTheorySemiformula (Fin n) k) (f : Fin n → W),
      (∀ i, f i ∈ A α) ∧ ∀ v : Fin k → W, φ.Eval v id ↔ ψ.Eval v f := by
  classical
  rcases isEmpty_or_nonempty W with hW | hW
  · refine ⟨Classical.arbitrary OmegaOne, 0,
      Rew.rewriteMap (fun x : W ↦ (isEmptyElim x : Fin 0)) ▹ φ,
      (fun i : Fin 0 ↦ i.elim0 : Fin 0 → W), fun i ↦ i.elim0, ?_⟩
    intro v
    rw [Semiformula.eval_rewriteMap]
    have hid : (fun x : W ↦ ((fun i : Fin 0 ↦ i.elim0 : Fin 0 → W) (isEmptyElim x))) = id := by
      funext x; exact isEmptyElim x
    rw [hid]
  · have : Inhabited W := Classical.inhabited_of_nonempty hW
    set L : List W := φ.fvarList with hLdef
    set n : ℕ := L.length + 1 with hn
    set f : Fin n → W := fun i ↦ L.getD (i : ℕ) default with hf
    set e : W → Fin n := fun x ↦ ⟨min (L.idxOf x) L.length, by omega⟩ with he
    choose c hc using hcover
    obtain ⟨α, hα⟩ := Finite.exists_le (fun i : Fin n ↦ c (f i))
    refine ⟨α, n, Rew.rewriteMap e ▹ φ, f, fun i ↦ hmono (hα i) (hc (f i)), ?_⟩
    intro v
    rw [Semiformula.eval_rewriteMap]
    refine (Semiformula.eval_iff_of_funEqOn φ ?_).symm
    intro x hx
    have hxL : x ∈ L := Semiformula.mem_fvarList_iff_fvar?.mpr hx
    have hlt : L.idxOf x < L.length := List.idxOf_lt_length_of_mem hxL
    have hmin : min (L.idxOf x) L.length = L.idxOf x := min_eq_left hlt.le
    show f (e x) = id x
    simp only [he, hf, hmin, id_eq]
    rw [List.getD_eq_getElem L default hlt]
    exact List.getElem_idxOf hlt

/-- Every predicate definable over `W` has all of its parameters inside a single stage of an
increasing chain that covers `W`. -/
theorem exists_definableOver_of_definable (A : OmegaOne → Set W) (hmono : Monotone A)
    (hcover : ∀ x : W, ∃ α, x ∈ A α) {P : W → Prop} (hP : ℒₛₑₜ-predicate[W] P) :
    ∃ α, DefinableOver (A α) P := by
  obtain ⟨φ, hφ⟩ := hP.definable
  obtain ⟨α, n, ψ, f, hf, hev⟩ := exists_params_in_stage hmono hcover φ
  refine ⟨α, n, ψ, f, hf, fun x ↦ ?_⟩
  rw [← hev ![x]]
  simpa using (hφ ![x]).symm

/-- Every relation definable over `W` has all of its parameters inside a single stage of an
increasing chain that covers `W`. -/
theorem exists_definableOverRel_of_definable (A : OmegaOne → Set W) (hmono : Monotone A)
    (hcover : ∀ x : W, ∃ α, x ∈ A α) {R : W → W → Prop} (hR : ℒₛₑₜ-relation[W] R) :
    ∃ α, DefinableOverRel (A α) R := by
  obtain ⟨φ, hφ⟩ := hR.definable
  obtain ⟨α, n, ψ, f, hf, hev⟩ := exists_params_in_stage hmono hcover φ
  refine ⟨α, n, ψ, f, hf, fun x y ↦ ?_⟩
  rw [← hev ![x, y]]
  simpa using (hφ ![x, y]).symm

/-! ## Reindexing ω₁ above a stage -/

/-- Above any stage `α₀` there is a strictly increasing reindexing of `ω₁`. Adding the ordinal of
`α₀` on the left is strictly monotone and lands above `α₀`, and it stays below `ω₁` because a sum
of two countable ordinals is countable. -/
theorem exists_strictMono_ge (α₀ : OmegaOne) :
    ∃ σ : OmegaOne → OmegaOne, StrictMono σ ∧ ∀ i, α₀ ≤ σ i := by
  have htype : Ordinal.type (α := OmegaOne) (· < ·) = Ordinal.omega.{0} 1 :=
    Ordinal.type_toType _
  set a : Ordinal.{0} := Ordinal.typein (α := OmegaOne) (· < ·) α₀ with hadef
  have hord : Ordinal.omega.{0} 1 = (Cardinal.aleph 1).ord := (Cardinal.ord_aleph 1).symm
  have hcard : ∀ o : Ordinal.{0}, o < Ordinal.omega.{0} 1 → o.card < Cardinal.aleph 1 :=
    fun o ho ↦ Cardinal.lt_ord.mp (lt_of_lt_of_eq ho hord)
  have ha : a < Ordinal.omega.{0} 1 :=
    lt_of_lt_of_eq (Ordinal.typein_lt_type (α := OmegaOne) (· < ·) α₀) htype
  have key : ∀ i : OmegaOne,
      a + Ordinal.typein (α := OmegaOne) (· < ·) i < Ordinal.type (α := OmegaOne) (· < ·) := by
    intro i
    rw [htype]
    have hi : Ordinal.typein (α := OmegaOne) (· < ·) i < Ordinal.omega.{0} 1 :=
      lt_of_lt_of_eq (Ordinal.typein_lt_type (α := OmegaOne) (· < ·) i) htype
    have hsum : (a + Ordinal.typein (α := OmegaOne) (· < ·) i).card < Cardinal.aleph 1 := by
      rw [Ordinal.card_add]
      exact Cardinal.add_lt_of_lt (Cardinal.aleph0_le_aleph 1) (hcard a ha) (hcard _ hi)
    exact lt_of_lt_of_eq (Cardinal.lt_ord.mpr hsum) hord.symm
  refine ⟨fun i ↦ Ordinal.enum (α := OmegaOne) (· < ·)
    ⟨a + Ordinal.typein (α := OmegaOne) (· < ·) i, key i⟩, ?_, ?_⟩
  · intro i j hij
    have h1 : Ordinal.typein (α := OmegaOne) (· < ·) i
        < Ordinal.typein (α := OmegaOne) (· < ·) j := by
      simpa using hij
    exact Ordinal.enum_lt_enum.mpr (Subtype.mk_lt_mk.mpr ((add_lt_add_iff_left a).mpr h1))
  · intro i
    have h0 : α₀ = Ordinal.enum (α := OmegaOne) (· < ·)
        ⟨a, lt_of_lt_of_eq ha htype.symm⟩ := by
      simp [hadef]
    rw [h0]
    exact (Ordinal.enum_le_enum' _).mpr (Subtype.mk_le_mk.mpr
      (le_self_add (a := a) (b := Ordinal.typein (α := OmegaOne) (· < ·) i)))

end ZFVP
