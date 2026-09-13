import ZFVP.SetTheory.UltrapowerStage
import ZFVP.SetTheory.UniformCollapse
import ZFVP.SetTheory.MostowskiCollapse
import ZFVP.SetTheory.InternalWellFounded

/-! The Mostowski collapse of the a.e. membership relation of an internal ultrapower.

The relation `ultraMemRelation P U A` is internally well founded but it is not extensional: two
distinct functions that agree almost everywhere have the same a.e. members. So the collapse map is
not injective, and the general Mostowski machinery does not hand us a transitive collapse. What it
does hand us is enough: the collapse map identifies two functions exactly when they are a.e. equal,
and it turns a.e. membership into real membership. The quotient by a.e. equality therefore never has
to be built as a set; the range of the collapse map is already the transitive set the ultrapower
lands in. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The collapse map of the a.e. membership relation on the functions from `P` into `A`. -/
noncomputable def ultraCollapse (P U A : V) : V :=
  mostowskiMap (ultraMemRelation P U A) (A ^ P)

/-- The transitive set the ultrapower collapses onto. -/
noncomputable def ultraTarget (P U A : V) : V := range (ultraCollapse P U A)

instance ultraCollapse_definable : ℒₛₑₜ-function₃[V] ultraCollapse := by
  unfold ultraCollapse
  definability

instance ultraTarget_definable : ℒₛₑₜ-function₃[V] ultraTarget := by
  unfold ultraTarget ultraCollapse
  definability

variable {P U A : V}

/-- On a well founded relation the uniform collapse map is the recursive collapse graph. -/
theorem ultraCollapse_eq_collapseGraph
    (hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P)) :
    ultraCollapse P U A = collapseGraph hwf :=
  mostowskiMap_of_wellFounded hwf

/-! ### Structural facts -/

theorem ultraCollapse_isFunction
    (hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P)) :
    IsFunction (ultraCollapse P U A) := by
  rw [ultraCollapse_eq_collapseGraph hwf]
  exact collapseGraph_isFunction hwf

theorem domain_ultraCollapse
    (hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P)) :
    domain (ultraCollapse P U A) = A ^ P := by
  rw [ultraCollapse_eq_collapseGraph hwf]
  exact domain_collapseGraph hwf

theorem ultraTarget_transitive
    (hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P)) :
    IsTransitive (ultraTarget P U A) := by
  unfold ultraTarget
  rw [ultraCollapse_eq_collapseGraph hwf]
  exact collapseGraph_range_transitive hwf

theorem ultraCollapse_mem_function
    (hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P)) :
    ultraCollapse P U A ∈ (ultraTarget P U A) ^ (A ^ P) := by
  have hfun : IsFunction (ultraCollapse P U A) := ultraCollapse_isFunction hwf
  exact function_mem_of_isFunction' (domain_ultraCollapse hwf) rfl

theorem ultraCollapse_value_mem
    (hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P)) {f : V} (hf : f ∈ A ^ P) :
    (ultraCollapse P U A) ‘ f ∈ ultraTarget P U A := by
  have hfun : IsFunction (ultraCollapse P U A) := ultraCollapse_isFunction hwf
  have hd : f ∈ domain (ultraCollapse P U A) := by rw [domain_ultraCollapse hwf]; exact hf
  exact mem_range_of_kpair_mem (kpair_value_mem hd)

theorem ultraTarget_nonempty
    (hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P)) (hA : IsNonempty A) :
    IsNonempty (ultraTarget P U A) := by
  obtain ⟨a, ha⟩ := hA.nonempty
  exact ⟨⟨(ultraCollapse P U A) ‘ (constantGraph P a),
    ultraCollapse_value_mem hwf (constantGraph_mem_ultraFunctions ha)⟩⟩

/-! ### Members of a collapsed value -/

/-- Every member of a collapsed value is the collapse of an a.e. member. -/
theorem mem_ultraCollapse_value
    (hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P)) {g z : V} (hg : g ∈ A ^ P) :
    z ∈ (ultraCollapse P U A) ‘ g ↔
      ∃ f ∈ A ^ P, UltraMem P U f g ∧ (ultraCollapse P U A) ‘ f = z := by
  rw [ultraCollapse_eq_collapseGraph hwf, mem_collapseGraph_value hwf hg]
  constructor
  · rintro ⟨y, hy, hpair, hval⟩
    exact ⟨y, hy, ((pair_mem_ultraMemRelation_iff P U A y g).mp hpair).2.2, hval⟩
  · rintro ⟨y, hy, hmem, hval⟩
    exact ⟨y, hy, (pair_mem_ultraMemRelation_iff P U A y g).mpr ⟨hy, hg, hmem⟩, hval⟩

/-! ### The collapse identifies exactly the a.e. equal functions -/

/-- A.e. equal functions have the same collapse value. No induction is needed here: the members of
a collapse value are read off from the a.e. members, and a.e. membership only sees the a.e. class. -/
theorem ultraCollapse_eq_of_ultraEq
    (hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P))
    (hU : IsSetUltrafilter P U) {f g : V} (hf : f ∈ A ^ P) (hg : g ∈ A ^ P)
    (h : UltraEq P U f g) :
    (ultraCollapse P U A) ‘ f = (ultraCollapse P U A) ‘ g := by
  apply mem_ext
  intro z
  rw [mem_ultraCollapse_value hwf hf, mem_ultraCollapse_value hwf hg]
  constructor
  · rintro ⟨k, hk, hkf, hval⟩
    exact ⟨k, hk, UltraMem.congr hU (ultraEq_refl hU) h hkf, hval⟩
  · rintro ⟨k, hk, hkg, hval⟩
    exact ⟨k, hk, UltraMem.congr hU (ultraEq_refl hU) (h.symm hU) hkg, hval⟩

/-- Functions with the same collapse value are a.e. equal. The proof is one well founded induction
on the a.e. membership relation, using extensionality modulo a.e. equality at each step. -/
theorem ultraEq_of_ultraCollapse_eq (hAC : InternalChoice V) {κ : V} [IsOrdinal κ] [IsTransitive A]
    (hU : IsSetUltrafilter P U) (hcomp : IsOrdinalCompleteOn P κ U) (hω : (ω : V) ∈ κ)
    (hA : IsNonempty A) {f g : V} (hf : f ∈ A ^ P) (hg : g ∈ A ^ P)
    (h : (ultraCollapse P U A) ‘ f = (ultraCollapse P U A) ‘ g) :
    UltraEq P U f g := by
  have hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P) :=
    ultraMemRelation_wellFounded hAC hU hcomp hω
  have hΦ : ℒₛₑₜ-predicate[V] (fun y ↦ ∀ x, x ∈ A ^ P →
      ((ultraCollapse P U A) ‘ x = (ultraCollapse P U A) ‘ y → UltraEq P U x y)) := by
    definability
  refine internalWellFounded_induction hwf _ hΦ ?_ g hg f hf h
  clear h hf hg f g
  intro g hg ih f hf hval
  refine ultraEq_of_ultraMem_iff hAC hU hA hf hg ?_
  intro k hk
  constructor
  · intro hkf
    -- `collapse k` is a member of `collapse f = collapse g`, so it is the collapse of an
    -- a.e. member `k'` of `g`; the induction hypothesis at `k'` makes `k` and `k'` a.e. equal.
    have hmem : (ultraCollapse P U A) ‘ k ∈ (ultraCollapse P U A) ‘ g := by
      rw [← hval]
      exact (mem_ultraCollapse_value hwf hf).mpr ⟨k, hk, hkf, rfl⟩
    obtain ⟨k', hk', hk'g, hk'val⟩ := (mem_ultraCollapse_value hwf hg).mp hmem
    have hpred : ⟨k', g⟩ₖ ∈ ultraMemRelation P U A :=
      (pair_mem_ultraMemRelation_iff P U A k' g).mpr ⟨hk', hg, hk'g⟩
    have heq : UltraEq P U k k' := ih k' hk' hpred k hk hk'val.symm
    exact UltraMem.congr hU (heq.symm hU) (ultraEq_refl hU) hk'g
  · intro hkg
    -- Here `k` itself is an a.e. member of `g`, so the induction hypothesis applies to `k`.
    have hmem : (ultraCollapse P U A) ‘ k ∈ (ultraCollapse P U A) ‘ f := by
      rw [hval]
      exact (mem_ultraCollapse_value hwf hg).mpr ⟨k, hk, hkg, rfl⟩
    obtain ⟨k', hk', hk'f, hk'val⟩ := (mem_ultraCollapse_value hwf hf).mp hmem
    have hpred : ⟨k, g⟩ₖ ∈ ultraMemRelation P U A :=
      (pair_mem_ultraMemRelation_iff P U A k g).mpr ⟨hk, hg, hkg⟩
    have heq : UltraEq P U k' k := ih k hk hpred k' hk' hk'val
    exact UltraMem.congr hU heq (ultraEq_refl hU) hk'f

/-- The collapse identifies exactly the a.e. equal functions. -/
theorem ultraCollapse_eq_iff (hAC : InternalChoice V) {P U A κ : V} [IsOrdinal κ] [IsTransitive A]
    (hU : IsSetUltrafilter P U) (hcomp : IsOrdinalCompleteOn P κ U) (hω : (ω : V) ∈ κ)
    (hA : IsNonempty A) {f g : V} (hf : f ∈ A ^ P) (hg : g ∈ A ^ P) :
    (ultraCollapse P U A) ‘ f = (ultraCollapse P U A) ‘ g ↔ UltraEq P U f g := by
  constructor
  · exact ultraEq_of_ultraCollapse_eq hAC hU hcomp hω hA hf hg
  · exact ultraCollapse_eq_of_ultraEq (ultraMemRelation_wellFounded hAC hU hcomp hω) hU hf hg

/-- The collapse turns a.e. membership into membership. -/
theorem ultraCollapse_mem_iff (hAC : InternalChoice V) {P U A κ : V} [IsOrdinal κ] [IsTransitive A]
    (hU : IsSetUltrafilter P U) (hcomp : IsOrdinalCompleteOn P κ U) (hω : (ω : V) ∈ κ)
    (hA : IsNonempty A) {f g : V} (hf : f ∈ A ^ P) (hg : g ∈ A ^ P) :
    (ultraCollapse P U A) ‘ f ∈ (ultraCollapse P U A) ‘ g ↔ UltraMem P U f g := by
  have hwf : IsInternallyWellFounded (ultraMemRelation P U A) (A ^ P) :=
    ultraMemRelation_wellFounded hAC hU hcomp hω
  constructor
  · intro hmem
    obtain ⟨k, hk, hkg, hkval⟩ := (mem_ultraCollapse_value hwf hg).mp hmem
    have heq : UltraEq P U f k :=
      (ultraCollapse_eq_iff hAC hU hcomp hω hA hf hk).mp hkval.symm
    exact UltraMem.congr hU (heq.symm hU) (ultraEq_refl hU) hkg
  · intro hmem
    exact (mem_ultraCollapse_value hwf hg).mpr ⟨f, hf, hmem, rfl⟩

end ZFVP
