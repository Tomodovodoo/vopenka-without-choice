import ZFVP.SetTheory.CnDeltaTwo
import ZFVP.Syntax.PartialTruthDomains

/-! Closure and fixed-dictionary absoluteness in positive C(n) rank stages. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ordinal_mem_hierarchy_iff {α δ : V} [IsOrdinal α] [IsOrdinal δ] :
    α ∈ hierarchy δ ↔ α ∈ δ := by rw [mem_hierarchy_iff_rank_mem, rank_of_ordinal]

theorem Cn.omega_lt {k : ℕ} {δ : V} (hδ : Cn (k + 1) δ) : (ω : V) ∈ δ := by
  let := hδ.ordinal
  exact ordinal_mem_hierarchy_iff.mp ((cn_successor_iff k δ).mp hδ).2.support.omega_mem

theorem Cn.successor_closed {k : ℕ} {δ : V} (hδ : Cn (k + 1) δ) :
    ∀ α ∈ δ, succ α ∈ δ := by
  let := hδ.ordinal
  intro α hα
  let := IsOrdinal.of_mem hα
  exact ordinal_mem_hierarchy_iff.mp (((cn_successor_iff k δ).mp hδ).2.support.succ_closed α
    (ordinal_mem_hierarchy_iff.mpr hα))

theorem Cn.rank_closed {k : ℕ} {δ x : V} (hδ : Cn (k + 1) δ) (hx : x ∈ hierarchy δ) :
    rank x ∈ hierarchy δ := by
  let := hδ.ordinal
  exact ordinal_mem_hierarchy_iff.mpr ((mem_hierarchy_iff_rank_mem x δ).mp hx)

theorem Cn.hierarchy_closed {k : ℕ} {δ α : V} (hδ : Cn (k + 1) δ)
    (hα : IsOrdinal α) (hαδ : α ∈ hierarchy δ) : hierarchy α ∈ hierarchy δ := by
  let := hδ.ordinal
  let := hα
  exact hierarchy_mem (ordinal_mem_hierarchy_iff.mp hαδ)

theorem Cn.levy_correct {p : LevyPolarity} {k n : ℕ} {δ : V} (hδ : Cn (k + 1) δ)
    {φ : SetTheorySemisentence n} (hφ : IsLevyFormula p (k + 1) φ)
    (v : Fin n → SetDomain (hierarchy δ)) : φ.Evalb v ↔ φ.Evalb (fun i ↦ (v i).val) := by
  cases p
  · exact hδ.sigma_correct hφ v
  · exact hδ.pi_correct hφ v

theorem Cn.defined_correct {p : LevyPolarity} {k n : ℕ} {δ : V} (hδ : Cn (k + 1) δ)
    {φ : SetTheorySemisentence n} (hφ : IsLevyFormula p (k + 1) φ)
    (R : (Fin n → V) → Prop) [Defined R φ] (v : Fin n → SetDomain (hierarchy δ)) :
    φ.Evalb v ↔ R (fun i ↦ (v i).val) :=
  (hδ.levy_correct hφ v).trans (Defined.eval_iff _)

theorem Cn.partialTruth_absolute {p : LevyPolarity} {k m : ℕ} {δ : V}
    (hδ : Cn (m + 1) δ) (hkm : k ≤ m) (n φ b : SetDomain (hierarchy δ)) :
    (domainTruthFormula p k).Evalb ![n, φ, b] ↔ DomainTruth p k n.val φ.val b.val := by
  have he := hδ.levy_correct ((domainTruthFormula_levy p k).mono (Nat.succ_le_succ hkm)) ![n, φ, b]
  have hv : (fun i : Fin 3 ↦ (![n, φ, b] i).val) = ![n.val, φ.val, b.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun l ↦ Fin.cases rfl (fun s ↦ Fin.elim0 s) l) j) i
  rw [hv] at he
  exact he.trans (eval_domainTruthFormula p k n.val φ.val b.val)

theorem Cn.setSatisfaction_absolute {k : ℕ} {δ : V} (hδ : Cn (k + 1) δ)
    (A n φ b : SetDomain (hierarchy δ)) :
    piOneMembershipTruthFormula.Evalb ![A, n, φ, b] ↔ MembershipSatisfies A.val n.val φ.val b.val := by
  have he := hδ.pi_correct (piOneMembershipTruthFormula_piOne.mono (by omega)) ![A, n, φ, b]
  have hv : (fun i : Fin 4 ↦ (![A, n, φ, b] i).val) = ![A.val, n.val, φ.val, b.val] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun l ↦ Fin.cases rfl
      (fun s ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) s) l) j) i
  rw [hv] at he
  exact he.trans (eval_piOneMembershipTruthFormula A.val n.val φ.val b.val)

end ZFVP
