import ZFVP.ModelTheory.SparseOrderIdentification
import ZFVP.SetTheory.CanonicalAtomicTruthTable
import ZFVP.SetTheory.CodingUniverse

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def sparseCarrierCutFamily (S a : V) : V :=
  definableGraph a (sparseCarrierCut S) (by definability)

instance sparseCarrierCutFamily_definable : ℒₛₑₜ-function₂[V] sparseCarrierCutFamily := by
  have hd : ℒₛₑₜ-relation₃[V] (fun H S a ↦ ∀ z, z ∈ H ↔
      ∃ b ∈ a, z = ⟨b, sparseCarrierCut S b⟩ₖ) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = sparseCarrierCutFamily (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [sparseCarrierCutFamily, mem_definableGraph_iff]

instance sparseCarrierCutFamily_function (S a : V) : IsFunction (sparseCarrierCutFamily S a) := by
  unfold sparseCarrierCutFamily
  infer_instance

theorem sparseCarrierCutFamily_domain (S a : V) : domain (sparseCarrierCutFamily S a) = a :=
  domain_definableGraph _ _ _

theorem sparseCarrierCutFamily_value {S a b : V} (hb : b ∈ a) :
    (sparseCarrierCutFamily S a) ‘ b = sparseCarrierCut S b := value_definableGraph _ _ _ hb

theorem sparseCarrierOrderTable_domain (S a : V) : domain (sparseCarrierOrderTable S a) = a :=
  domain_definableGraph _ _ _

theorem sparseCarrierOrderTable_value {S a b : V} (hb : b ∈ a) :
    (sparseCarrierOrderTable S a) ‘ b = sparseCarrierOrder S b := value_definableGraph _ _ _ hb

instance sparseCarrierOrderTable_definable : ℒₛₑₜ-function₂[V] sparseCarrierOrderTable := by
  have hd : ℒₛₑₜ-relation₃[V] (fun H S a ↦ ∀ z, z ∈ H ↔
      ∃ b ∈ a, z = ⟨b, sparseCarrierOrder S b⟩ₖ) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = sparseCarrierOrderTable (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [sparseCarrierOrderTable, mem_definableGraph_iff]

noncomputable def sparseCarrierAtomicTable (S U b : V) : V :=
  canonicalAtomicTruthTable (sparseCarrierCut S b) (sparseCarrierOrder S b) U

instance sparseCarrierAtomicTable_definable : ℒₛₑₜ-function₃[V] sparseCarrierAtomicTable := by
  unfold sparseCarrierAtomicTable
  definability

noncomputable def sparseCarrierAtomicFamily (S U a : V) : V :=
  definableGraph a (sparseCarrierAtomicTable S U) (by definability)

instance sparseCarrierAtomicFamily_definable : ℒₛₑₜ-function₃[V] sparseCarrierAtomicFamily := by
  have hd : ℒₛₑₜ-relation₄[V] (fun H S U a ↦ ∀ z, z ∈ H ↔
      ∃ b ∈ a, z = ⟨b, sparseCarrierAtomicTable S U b⟩ₖ) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = sparseCarrierAtomicFamily (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [sparseCarrierAtomicFamily, mem_definableGraph_iff]

instance sparseCarrierAtomicFamily_function (S U a : V) : IsFunction (sparseCarrierAtomicFamily S U a) := by
  unfold sparseCarrierAtomicFamily
  infer_instance

theorem sparseCarrierAtomicFamily_domain (S U a : V) : domain (sparseCarrierAtomicFamily S U a) = a :=
  domain_definableGraph _ _ _

theorem sparseCarrierAtomicFamily_value {S U a b : V} (hb : b ∈ a) :
    (sparseCarrierAtomicFamily S U a) ‘ b = sparseCarrierAtomicTable S U b :=
  value_definableGraph _ _ _ hb

theorem sparseCarrierAtomicFamily_spec {S U a b : V} [IsTransitive U] (hb : b ∈ a) :
    IsAtomicTruthTable (sparseCarrierCut S b) (sparseCarrierOrder S b) U
      ((sparseCarrierAtomicFamily S U a) ‘ b) := by
  rw [sparseCarrierAtomicFamily_value hb]
  exact canonicalAtomicTruthTable_spec _ _ _ (transitive_subnameClosed inferInstance)

theorem sparseCarrierOrder_subset_hierarchy {S η b : V} [IsOrdinal η] [IsOrdinal b]
    (hη : ∀ β ∈ η, succ β ∈ η) (hS : S ⊆ hierarchy η) :
    sparseCarrierOrder S b ⊆ hierarchy η := by
  intro z hz
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp (sparseCarrierOrder_subset z hz)
  exact kpair_mem_hierarchy_limit hη (hS p (mem_sparseCarrierCut_iff.mp hp).1)
    (hS q (mem_sparseCarrierCut_iff.mp hq).1)

theorem sparseCarrierOrder_mem_successor {S η b : V} [IsOrdinal η] [IsOrdinal b]
    (hη : ∀ β ∈ η, succ β ∈ η) (hS : S ⊆ hierarchy η) :
    sparseCarrierOrder S b ∈ hierarchy (succ η) := by
  rw [hierarchy_succ, mem_power_iff]
  exact sparseCarrierOrder_subset_hierarchy hη hS

theorem sparseCarrierAtomicTable_subset_hierarchy {S η b : V} [IsOrdinal η]
    (hη : ∀ β ∈ η, succ β ∈ η) (hS : S ⊆ hierarchy η) :
    sparseCarrierAtomicTable S (hierarchy η) b ⊆ hierarchy η :=
  canonicalAtomicTruthTable_subset_hierarchy hη (fun _ hp ↦ hS _ (mem_sparseCarrierCut_iff.mp hp).1)

theorem sparseCarrierAtomicTable_mem_successor {S η b : V} [IsOrdinal η]
    (hη : ∀ β ∈ η, succ β ∈ η) (hS : S ⊆ hierarchy η) :
    sparseCarrierAtomicTable S (hierarchy η) b ∈ hierarchy (succ η) := by
  rw [hierarchy_succ, mem_power_iff]
  exact sparseCarrierAtomicTable_subset_hierarchy hη hS

theorem sparseCarrierOrderTable_mem_four_successors {S η a : V} [IsOrdinal η]
    (hη : ∀ β ∈ η, succ β ∈ η) (hS : S ⊆ hierarchy η) (ha : a ⊆ succ η) :
    sparseCarrierOrderTable S a ∈ hierarchy (succ (succ (succ (succ η)))) := by
  rw [hierarchy_succ, mem_power_iff]
  intro z hz
  obtain ⟨b, hb, rfl⟩ := (mem_definableGraph_iff _ _ _ _).mp hz
  let := IsOrdinal.of_mem (ha b hb)
  exact kpair_mem_hierarchy_succ_succ
    (ordinal_subset_hierarchy (succ η) b (ha b hb)) (sparseCarrierOrder_mem_successor hη hS)

theorem sparseCarrierAtomicFamily_mem_four_successors {S η a : V} [IsOrdinal η]
    (hη : ∀ β ∈ η, succ β ∈ η) (hS : S ⊆ hierarchy η) (ha : a ⊆ succ η) :
    sparseCarrierAtomicFamily S (hierarchy η) a ∈ hierarchy (succ (succ (succ (succ η)))) := by
  rw [hierarchy_succ, mem_power_iff]
  intro z hz
  obtain ⟨b, hb, rfl⟩ := (mem_definableGraph_iff _ _ _ _).mp hz
  exact kpair_mem_hierarchy_succ_succ
    (ordinal_subset_hierarchy (succ η) b (ha b hb)) (sparseCarrierAtomicTable_mem_successor hη hS)

theorem sparseCarrierOrderTable_finiteRank {S η a : V} [IsOrdinal η]
    (hη : ∀ β ∈ η, succ β ∈ η) (hS : S ⊆ hierarchy η) (ha : a ⊆ succ η) :
    sparseCarrierOrderTable S a ∈ hierarchy (ordinalAdd η (ω : V)) := by
  have h := ordinalAdd_omega_gt η
  have hs : ∀ {β : V}, β ∈ ordinalAdd η (ω : V) → succ β ∈ ordinalAdd η (ω : V) :=
    fun h ↦ ordinalAdd_omega_succ_closed η h
  exact mem_hierarchy_of_mem_stage (hs (hs (hs (hs h))))
    (sparseCarrierOrderTable_mem_four_successors hη hS ha)

theorem sparseCarrierAtomicFamily_finiteRank {S η a : V} [IsOrdinal η]
    (hη : ∀ β ∈ η, succ β ∈ η) (hS : S ⊆ hierarchy η) (ha : a ⊆ succ η) :
    sparseCarrierAtomicFamily S (hierarchy η) a ∈ hierarchy (ordinalAdd η (ω : V)) := by
  have h := ordinalAdd_omega_gt η
  have hs : ∀ {β : V}, β ∈ ordinalAdd η (ω : V) → succ β ∈ ordinalAdd η (ω : V) :=
    fun h ↦ ordinalAdd_omega_succ_closed η h
  exact mem_hierarchy_of_mem_stage (hs (hs (hs (hs h))))
    (sparseCarrierAtomicFamily_mem_four_successors hη hS ha)

theorem graph_mem_five_successors {η a : V} [IsOrdinal η] (ha : a ⊆ succ (succ η))
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) (hv : ∀ b ∈ a, F b ∈ hierarchy (succ η)) :
    definableGraph a F hF ∈ hierarchy (succ (succ (succ (succ (succ η))))) := by
  rw [hierarchy_succ, mem_power_iff]
  intro z hz
  obtain ⟨b, hb, rfl⟩ := (mem_definableGraph_iff _ _ _ _).mp hz
  exact kpair_mem_hierarchy_succ_succ
    (ordinal_subset_hierarchy (succ (succ η)) b (ha b hb))
    (hierarchy_mono (mem_subset_refl _) _ (hv b hb))

theorem sparseCarrierCutFamily_mem_five_successors {S η a : V} [IsOrdinal η]
    (hS : S ⊆ hierarchy η) (ha : a ⊆ succ (succ η)) :
    sparseCarrierCutFamily S a ∈ hierarchy (succ (succ (succ (succ (succ η))))) := by
  apply graph_mem_five_successors ha
  intro b _
  rw [hierarchy_succ, mem_power_iff]
  exact fun p hp ↦ hS p (mem_sparseCarrierCut_iff.mp hp).1

theorem sparseCarrierOrderTable_mem_five_successors {S η a : V} [IsOrdinal η]
    (hη : ∀ β ∈ η, succ β ∈ η) (hS : S ⊆ hierarchy η) (ha : a ⊆ succ (succ η)) :
    sparseCarrierOrderTable S a ∈ hierarchy (succ (succ (succ (succ (succ η))))) := by
  apply graph_mem_five_successors ha
  intro b hb
  let := IsOrdinal.of_mem (ha b hb)
  exact sparseCarrierOrder_mem_successor hη hS

theorem sparseCarrierAtomicFamily_mem_five_successors {S η a : V} [IsOrdinal η]
    (hη : ∀ β ∈ η, succ β ∈ η) (hS : S ⊆ hierarchy η) (ha : a ⊆ succ (succ η)) :
    sparseCarrierAtomicFamily S (hierarchy η) a ∈ hierarchy (succ (succ (succ (succ (succ η))))) := by
  apply graph_mem_five_successors ha
  exact fun _ _ ↦ sparseCarrierAtomicTable_mem_successor hη hS

theorem sparseRecoveryTables_finiteRank {S η a : V} [IsOrdinal η]
    (hη : ∀ β ∈ η, succ β ∈ η) (hS : S ⊆ hierarchy η) (ha : a ⊆ succ (succ η)) :
    sparseCarrierCutFamily S a ∈ hierarchy (ordinalAdd η (ω : V)) ∧
      sparseCarrierOrderTable S a ∈ hierarchy (ordinalAdd η (ω : V)) ∧
      sparseCarrierAtomicFamily S (hierarchy η) a ∈ hierarchy (ordinalAdd η (ω : V)) := by
  have hs : ∀ {β : V}, β ∈ ordinalAdd η (ω : V) → succ β ∈ ordinalAdd η (ω : V) :=
    fun h ↦ ordinalAdd_omega_succ_closed η h
  have hb := hs (hs (hs (hs (hs (ordinalAdd_omega_gt η)))))
  exact ⟨mem_hierarchy_of_mem_stage hb (sparseCarrierCutFamily_mem_five_successors hS ha),
    mem_hierarchy_of_mem_stage hb (sparseCarrierOrderTable_mem_five_successors hη hS ha),
    mem_hierarchy_of_mem_stage hb (sparseCarrierAtomicFamily_mem_five_successors hη hS ha)⟩

end ZFVP
