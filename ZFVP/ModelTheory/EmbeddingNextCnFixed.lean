import ZFVP.SetTheory.CnSandwich
import ZFVP.ModelTheory.CriticalPoint

/-! The least correct height above a fixed ordinal is fixed, provided it
lies in the source of the embedding. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def nextCnFormula (n : ℕ) : SetTheorySemisentence 2 :=
  “β δ. !(cnFormula n) δ ∧ β ∈ δ ∧ ∀ ζ ∈ δ, β ∈ ζ → ¬!(cnFormula n) ζ”

theorem eval_nextCn_components {W : Type*} [SetStructure W] (n : ℕ) (β δ : W) :
    (nextCnFormula n).Evalb ![β, δ] ↔ (cnFormula n).Evalb ![δ] ∧ β ∈ δ ∧
      ∀ ζ ∈ δ, β ∈ ζ → ¬(cnFormula n).Evalb ![ζ] := by
  simp [nextCnFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Function.comp_def, Matrix.constant_eq_singleton]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem Cn.nextCn_into_rank {n : ℕ} {θ β δ : V} (hθ : Cn (n + 1) θ)
    (hδ : IsLeastOrdinal (fun ζ ↦ β ∈ ζ ∧ Cn (n + 2) ζ) δ) (hδθ : δ ∈ θ) :
    (nextCnFormula (n + 2)).Evalb (M := SetDomain (hierarchy θ))
      ![⟨β, by
          let := hθ.ordinal
          exact ordinal_subset_hierarchy θ β
            (IsOrdinal.toIsTransitive.mem_trans hδ.2.1.1 hδθ)⟩,
        ⟨δ, by let := hθ.ordinal; exact ordinal_subset_hierarchy θ δ hδθ⟩] := by
  let := hθ.ordinal
  let := hδ.1
  let b : SetDomain (hierarchy θ) := ⟨β, ordinal_subset_hierarchy θ β
    (IsOrdinal.toIsTransitive.mem_trans hδ.2.1.1 hδθ)⟩
  let d : SetDomain (hierarchy θ) := ⟨δ, ordinal_subset_hierarchy θ δ hδθ⟩
  apply (eval_nextCn_components _ b d).mpr
  refine ⟨hδ.2.1.2.into_lower_rank hθ hδθ, hδ.2.1.1, ?_⟩
  intro ζ hζδ hβζ hζ
  have hζC := cn_sandwich hθ hδ.2.1.2 hζδ hδθ hζ
  have hle := hδ.2.2 ζ.val hζC.ordinal ⟨hβζ, hζC⟩
  exact mem_irrefl ζ.val (hle ζ.val hζδ)

theorem rankEmbedding_nextCn_fixed {n : ℕ} {θ η f β δ : V}
    (hθ : Cn (n + 2) θ) (hη : Cn (n + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f)
    (hδ : IsLeastOrdinal (fun ζ ↦ β ∈ ζ ∧ Cn (n + 2) ζ) δ)
    (hδθ : δ ∈ θ) (hfix : f ‘ β = β) : f ‘ δ = δ := by
  let := hθ.ordinal
  let := hη.ordinal
  let := hδ.1
  let : IsOrdinal β := IsOrdinal.of_mem hδ.2.1.1
  let := hierarchy_transitive θ
  let := hierarchy_transitive η
  have hδV := ordinal_subset_hierarchy θ δ hδθ
  have hβV := (hierarchy_transitive θ).mem_trans hδ.2.1.1 hδV
  have himg := function_value_mem hf.function hδV
  let := hf.value_ordinal hδ.1 hδV
  have hδη : δ ∈ η := ordinal_mem_of_subset_mem (hf.ordinal_subset_value hδ.1 hδV)
    (ordinal_mem_hierarchy_iff.mp himg)
  let b : SetDomain (hierarchy θ) := ⟨β, hβV⟩
  let d : SetDomain (hierarchy θ) := ⟨δ, hδV⟩
  let b' : SetDomain (hierarchy η) := ⟨β, hfix ▸ function_value_mem hf.function hβV⟩
  let d' : SetDomain (hierarchy η) := ⟨δ, ordinal_subset_hierarchy η δ hδη⟩
  have hs := (hθ.of_le (by omega : n + 1 ≤ n + 2)).nextCn_into_rank hδ hδθ
  have ht := (hf.eval_semisentence (nextCnFormula (n + 2)) ![b, d]).mp hs
  have hv : hf.toFunction ∘ ![b, d] = ![b', hf.toFunction d] := by
    funext i
    refine Fin.cases ?_ (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    exact Subtype.ext hfix
  rw [hv, eval_nextCn_components] at ht
  have hu := (eval_nextCn_components _ b' d').mp (hη.nextCn_into_rank hδ hδη)
  rcases IsOrdinal.mem_trichotomy (f ‘ δ) δ with hl | he | hg
  · exact False.elim (hu.2.2 (hf.toFunction d) hl ht.2.1 ht.1)
  · exact he
  · exact False.elim (ht.2.2 d' hg hu.2.1 hu.1)

end ZFVP
