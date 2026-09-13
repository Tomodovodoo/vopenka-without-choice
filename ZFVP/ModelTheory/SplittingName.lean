import ZFVP.SetTheory.PerfectSetCore
import ZFVP.SetTheory.BaireCore
import ZFVP.ModelTheory.ForcingSmallUltrafilter
import ZFVP.ModelTheory.GenericFilterName
import ZFVP.ModelTheory.CohenGenericReals
import ZFVP.ModelTheory.SubposetRealization

/-! Splitting for names of new reals. Over a countable ground model, a name `τ` forced below `p₀`
to be a real not in the ground model has decided segments `decidedSegment τ p` (finite binary
sequences) below `p₀` which are monotone and split below every condition; and the conditions
deciding the first `n` bits are dense below `p₀`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- `x` is a real that does not belong to `C`. -/
def newRealFormula : SetTheorySemisentence 2 := f“x C. x ∈ !cantorSpaceFormula ∧ ¬ x ∈ C”

theorem eval_newRealFormula (v : Fin 2 → V) :
    newRealFormula.Evalb v ↔ v 0 ∈ cantorSpace V ∧ v 0 ∉ v 1 := by
  simp [newRealFormula]

theorem cantorSpace_eq_check (S : ForcingContext V) :
    cantorSpace S.Model = S.check ((2 : ℕ) : V) ^ S.check (ω : V) := by
  have h2 := S.checkEmbedding.map_numeral 2
  change S.check ((2 : ℕ) : V) = ((2 : ℕ) : S.Model) at h2
  rw [S.check_omega_eq, h2]
  rfl

/-- `z = ⟨m, i⟩` is a bit decided by `p`, together with all earlier bits. -/
def IsDecided (P R one τ p z : V) : Prop :=
  ∃ m ∈ (ω : V), ∃ i ∈ ((2 : ℕ) : V), z = ⟨m, i⟩ₖ ∧ ForcesCheckedMember P R one τ p ⟨m, i⟩ₖ ∧
    ∀ m' ∈ m, ∃ i' ∈ ((2 : ℕ) : V), ForcesCheckedMember P R one τ p ⟨m', i'⟩ₖ

instance isDecided_definable (P R one τ : V) : ℒₛₑₜ-relation[V] (IsDecided P R one τ) := by
  unfold IsDecided
  definability

/-- The segment of the real named by `τ` decided by `p`. -/
noncomputable def decidedSegment (P R one τ p : V) : V :=
  {z ∈ (ω : V) ×ˢ ((2 : ℕ) : V) ; IsDecided P R one τ p z}

theorem mem_decidedSegment_iff (P R one τ p z : V) :
    z ∈ decidedSegment P R one τ p ↔ z ∈ (ω : V) ×ˢ ((2 : ℕ) : V) ∧ IsDecided P R one τ p z :=
  mem_sep_iff

/-- `p` decides every bit `m ≤ n`. -/
def DecidesBelow (P R one τ n p : V) : Prop :=
  ∀ m ∈ succ n, ∃ i ∈ ((2 : ℕ) : V), ForcesCheckedMember P R one τ p ⟨m, i⟩ₖ

instance decidesBelow_definable (P R one τ : V) : ℒₛₑₜ-relation[V] (DecidesBelow P R one τ) := by
  unfold DecidesBelow
  definability

/-- Conditions deciding the first `n + 1` bits. -/
noncomputable def deciderSet (P R one τ n : V) : V := {p ∈ P ; DecidesBelow P R one τ n p}

theorem mem_deciderSet_iff (P R one τ n p : V) :
    p ∈ deciderSet P R one τ n ↔ p ∈ P ∧ DecidesBelow P R one τ n p :=
  mem_sep_iff

/-- The conditions below `p₀`. -/
noncomputable def cone (P R p₀ : V) : V := {p ∈ P ; ⟨p, p₀⟩ₖ ∈ R}

theorem mem_cone_iff (P R p₀ p : V) : p ∈ cone P R p₀ ↔ p ∈ P ∧ ⟨p, p₀⟩ₖ ∈ R := mem_sep_iff

theorem cone_subset (P R p₀ : V) : cone P R p₀ ⊆ P := sep_subset

theorem cone_preorder {P R : V} (hR : IsForcingPreorder P R) (p₀ : V) :
    IsForcingPreorder (cone P R p₀) (restrictedOrder R (cone P R p₀)) :=
  restrictedOrder_preorder hR (cone_subset P R p₀)

theorem cone_top {P R p₀ : V} (hR : IsForcingPreorder P R) (hp₀ : p₀ ∈ P) :
    IsForcingTop (cone P R p₀) (restrictedOrder R (cone P R p₀)) p₀ := by
  have hp₀c : p₀ ∈ cone P R p₀ := (mem_cone_iff _ _ _ _).mpr ⟨hp₀, hR.2.1 p₀ hp₀⟩
  refine ⟨hp₀c, fun p hp ↦ ?_⟩
  exact (kpair_mem_restrictedOrder_iff _ _ _ _).mpr ⟨((mem_cone_iff _ _ _ _).mp hp).2, hp, hp₀c⟩

theorem cone_dense_of_below {P R p₀ D : V} (hR : IsForcingPreorder P R) (hp₀ : p₀ ∈ P) (hD : D ⊆ P)
    (hdense : ∀ q ∈ P, ⟨q, p₀⟩ₖ ∈ R → ∃ r ∈ D, ⟨r, q⟩ₖ ∈ R) :
    ForcingDense (cone P R p₀) (restrictedOrder R (cone P R p₀)) (D ∩ cone P R p₀) := by
  refine ⟨fun z hz ↦ (mem_inter_iff.mp hz).2, fun p hp ↦ ?_⟩
  obtain ⟨hpP, hpp₀⟩ := (mem_cone_iff _ _ _ _).mp hp
  obtain ⟨r, hrD, hrp⟩ := hdense p hpP hpp₀
  have hrP : r ∈ P := hD r hrD
  have hrc : r ∈ cone P R p₀ := (mem_cone_iff _ _ _ _).mpr ⟨hrP, hR.2.2 r hrP p hpP p₀ hp₀ hrp hpp₀⟩
  exact ⟨r, mem_inter_iff.mpr ⟨hrD, hrc⟩, (kpair_mem_restrictedOrder_iff _ _ _ _).mpr ⟨hrp, hrc, hp⟩⟩

theorem cone_dense {P R p₀ D : V} (hR : IsForcingPreorder P R) (hp₀ : p₀ ∈ P) (hD : ForcingDense P R D) :
    ForcingDense (cone P R p₀) (restrictedOrder R (cone P R p₀)) (D ∩ cone P R p₀) :=
  cone_dense_of_below hR hp₀ hD.1 (fun q hq _ ↦ hD.2 q hq)

theorem forcesCheckedMember_mono {P R one τ p q z : V} (hR : IsForcingPreorder P R)
    (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R) (h : ForcesCheckedMember P R one τ p z) :
    ForcesCheckedMember P R one τ q z :=
  (forcingFormula_regular hR memberFormula _).2.1 p h q hq hqp

theorem forcesCheckedMember_mem {P R one τ p z : V} (hR : IsForcingPreorder P R)
    (h : ForcesCheckedMember P R one τ p z) : p ∈ P :=
  (forcingFormula_regular hR memberFormula _).1 p h

theorem decidedSegment_mono {P R one τ p q : V} (hR : IsForcingPreorder P R) (hq : q ∈ P)
    (hqp : ⟨q, p⟩ₖ ∈ R) : decidedSegment P R one τ p ⊆ decidedSegment P R one τ q := by
  intro z hz
  obtain ⟨hzprod, m, hm, i, hi, rfl, hf, hall⟩ := (mem_decidedSegment_iff _ _ _ _ _ _).mp hz
  refine (mem_decidedSegment_iff _ _ _ _ _ _).mpr ⟨hzprod, m, hm, i, hi, rfl,
    forcesCheckedMember_mono hR hq hqp hf, fun m' hm' ↦ ?_⟩
  obtain ⟨i', hi', hf'⟩ := hall m' hm'
  exact ⟨i', hi', forcesCheckedMember_mono hR hq hqp hf'⟩

theorem deciderDensePredicate_definable (P R one τ p₀ : V) :
    ℒₛₑₜ-predicate (fun n : V ↦ ∀ q ∈ P, ⟨q, p₀⟩ₖ ∈ R →
      ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ DecidesBelow P R one τ n r) := by
  definability

theorem unionPredicate_definable (P R one τ p : V) :
    ℒₛₑₜ-predicate (fun z : V ↦ ∃ q ∈ P, ⟨q, p⟩ₖ ∈ R ∧ IsDecided P R one τ q z) := by
  definability

section

variable [Countable V] {P R one : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
  {τ : V} (hτ : IsForcingName P τ) {p₀ : V} (hp₀ : p₀ ∈ P)
  (hnew : p₀ ∈ forcingFormula P R newRealFormula (standardTuple ![τ, checkName one (cantorSpace V)]))

include hR htop

/-- The extension by an external generic. -/
noncomputable def genericContext {G : Set V} (hG : IsExternalForcingGeneric P R G) : ForcingContext V :=
  ⟨P, R, one, G, hR, htop, hG⟩

include hτ hp₀ hnew in
/-- In an extension through `p₀`, `τ` names a real not in the ground model. -/
theorem newReal_of_generic {G : Set V} (hG : IsExternalForcingGeneric P R G) (hp₀G : p₀ ∈ G) :
    (genericContext hR htop hG).ofName ⟨τ, hτ⟩ ∈ cantorSpace (genericContext hR htop hG).Model ∧
      (genericContext hR htop hG).ofName ⟨τ, hτ⟩ ∉ (genericContext hR htop hG).check (cantorSpace V) := by
  let S := genericContext hR htop hG
  let v : Fin 2 → ForcingName S.P := ![⟨τ, hτ⟩, ⟨checkName one (cantorSpace V), checkName_isName htop.1 _⟩]
  have h := S.formula_truth newRealFormula v
  have hv : (fun i ↦ (v i).val) = ![τ, checkName one (cantorSpace V)] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ k.elim0) j) i
  rw [hv, eval_newRealFormula] at h
  have hmeets : GenericMeets S.G (forcingFormula P R newRealFormula (standardTuple ![τ, checkName one (cantorSpace V)])) :=
    ⟨p₀, hp₀G, hnew⟩
  have := h.mpr hmeets
  simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at this
  exact this

include hτ hp₀ hnew in
theorem single_decision_dense (m : V) (hm : m ∈ (ω : V)) (q : V) (hq : q ∈ P) (hqp₀ : ⟨q, p₀⟩ₖ ∈ R) :
    ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ ∃ i ∈ ((2 : ℕ) : V), ForcesCheckedMember P R one τ r ⟨m, i⟩ₖ := by
  obtain ⟨G, hG, hqG⟩ := exists_externalForcingGeneric hR hq
  let S := genericContext hR htop hG
  have hp₀G : p₀ ∈ G := hG.1.2.2.1 q hqG p₀ hp₀ hqp₀
  obtain ⟨hreal, _⟩ := newReal_of_generic hR htop hτ hp₀ hnew hG hp₀G
  have hcs := cantorSpace_eq_check S
  rw [hcs] at hreal
  have hmS : S.check m ∈ S.check (ω : V) := (S.check_mem_iff _ _).mpr hm
  have hval : (S.ofName ⟨τ, hτ⟩) ‘ (S.check m) ∈ S.check ((2 : ℕ) : V) := function_value_mem hreal hmS
  obtain ⟨i, hi, hiv⟩ := (S.mem_check_iff _ _).mp hval
  have : IsFunction (S.ofName ⟨τ, hτ⟩) := IsFunction.of_mem hreal
  have hpair : S.check ⟨m, i⟩ₖ ∈ S.ofName ⟨τ, hτ⟩ := by
    rw [S.check_kpair, ← hiv]
    exact kpair_value_mem (by rw [domain_eq_of_mem_function hreal]; exact hmS)
  obtain ⟨r', hr'G, hr'⟩ := (S.checkedMember_truth ⟨τ, hτ⟩ ⟨m, i⟩ₖ).mp hpair
  obtain ⟨r, hrG, hrr', hrq⟩ := hG.1.2.2.2 r' hr'G q hqG
  have hrP : r ∈ P := hG.1.1 r hrG
  exact ⟨r, hrP, hrq, i, hi, forcesCheckedMember_mono hR hrP hrr' hr'⟩

include hτ hp₀ hnew in
/-- The deciders of the first `n + 1` bits are dense below `p₀`. -/
theorem decider_dense (n : V) (hn : n ∈ (ω : V)) :
    ∀ q ∈ P, ⟨q, p₀⟩ₖ ∈ R → ∃ r ∈ deciderSet P R one τ n, ⟨r, q⟩ₖ ∈ R := by
  have key : ∀ n ∈ (ω : V), ∀ q ∈ P, ⟨q, p₀⟩ₖ ∈ R →
      ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ DecidesBelow P R one τ n r := by
    refine naturalNumber_induction (fun n : V ↦ ∀ q ∈ P, ⟨q, p₀⟩ₖ ∈ R →
      ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ DecidesBelow P R one τ n r) (deciderDensePredicate_definable P R one τ p₀) ?_ ?_
    · intro q hq hqp₀
      obtain ⟨r, hrP, hrq, i, hi, hf⟩ := single_decision_dense hR htop hτ hp₀ hnew 0 (zero_mem_ω) q hq hqp₀
      refine ⟨r, hrP, hrq, fun m hm ↦ ?_⟩
      rcases mem_succ_iff.mp hm with rfl | hm
      · exact ⟨i, hi, hf⟩
      · exact absurd hm not_mem_empty
    · intro n hn ih q hq hqp₀
      obtain ⟨r₁, hr₁P, hr₁q, hdec₁⟩ := ih q hq hqp₀
      have hr₁p₀ : ⟨r₁, p₀⟩ₖ ∈ R := hR.2.2 r₁ hr₁P q hq p₀ hp₀ hr₁q hqp₀
      obtain ⟨r, hrP, hrr₁, i, hi, hf⟩ :=
        single_decision_dense hR htop hτ hp₀ hnew (succ n) (ω_succ_closed hn) r₁ hr₁P hr₁p₀
      refine ⟨r, hrP, hR.2.2 r hrP r₁ hr₁P q hq hrr₁ hr₁q, fun m hm ↦ ?_⟩
      rcases mem_succ_iff.mp hm with rfl | hm
      · exact ⟨i, hi, hf⟩
      · obtain ⟨i', hi', hf'⟩ := hdec₁ m hm
        exact ⟨i', hi', forcesCheckedMember_mono hR hrP hrr₁ hf'⟩
  intro q hq hqp₀
  obtain ⟨r, hrP, hrq, hdec⟩ := key n hn q hq hqp₀
  exact ⟨r, (mem_deciderSet_iff _ _ _ _ _ _).mpr ⟨hrP, hdec⟩, hrq⟩

include hτ hp₀ hnew in
/-- Below `p₀`, no condition decides two different values of a bit. -/
theorem decided_unique {p m i i' : V} (hp : p ∈ P) (hpp₀ : ⟨p, p₀⟩ₖ ∈ R)
    (hf : ForcesCheckedMember P R one τ p ⟨m, i⟩ₖ) (hf' : ForcesCheckedMember P R one τ p ⟨m, i'⟩ₖ) :
    i = i' := by
  obtain ⟨G, hG, hpG⟩ := exists_externalForcingGeneric hR hp
  let S := genericContext hR htop hG
  have hp₀G : p₀ ∈ G := hG.1.2.2.1 p hpG p₀ hp₀ hpp₀
  obtain ⟨hreal, _⟩ := newReal_of_generic hR htop hτ hp₀ hnew hG hp₀G
  have : IsFunction (S.ofName ⟨τ, hτ⟩) := IsFunction.of_mem hreal
  have h1 : S.check ⟨m, i⟩ₖ ∈ S.ofName ⟨τ, hτ⟩ := (S.checkedMember_truth ⟨τ, hτ⟩ _).mpr ⟨p, hpG, hf⟩
  have h2 : S.check ⟨m, i'⟩ₖ ∈ S.ofName ⟨τ, hτ⟩ := (S.checkedMember_truth ⟨τ, hτ⟩ _).mpr ⟨p, hpG, hf'⟩
  rw [S.check_kpair] at h1 h2
  have := (value_eq_of_kpair_mem h1).symm.trans (value_eq_of_kpair_mem h2)
  exact (S.check_eq_iff _ _).mp this

include hτ hp₀ hnew in
/-- Below `p₀`, no condition decides all bits of the new real. -/
theorem not_decides_all {p : V} (hp : p ∈ P) (hpp₀ : ⟨p, p₀⟩ₖ ∈ R) {D : V}
    (hD : D ∈ cantorSpace V) (hforce : ∀ z ∈ D, ForcesCheckedMember P R one τ p z) : False := by
  obtain ⟨G, hG, hpG⟩ := exists_externalForcingGeneric hR hp
  let S := genericContext hR htop hG
  have hp₀G : p₀ ∈ G := hG.1.2.2.1 p hpG p₀ hp₀ hpp₀
  obtain ⟨hreal, hnot⟩ := newReal_of_generic hR htop hτ hp₀ hnew hG hp₀G
  have hcs := cantorSpace_eq_check S
  have hDS : S.check D ∈ S.check ((2 : ℕ) : V) ^ S.check (ω : V) :=
    (S.checkEmbedding.function_iff D (ω : V) ((2 : ℕ) : V)).mpr hD
  have hsub : S.check D ⊆ S.ofName ⟨τ, hτ⟩ := by
    intro z hz
    obtain ⟨z', hz', rfl⟩ := (S.mem_check_iff _ _).mp hz
    exact (S.checkedMember_truth ⟨τ, hτ⟩ _).mpr ⟨p, hpG, hforce z' hz'⟩
  rw [hcs] at hreal
  have heq : S.check D = S.ofName ⟨τ, hτ⟩ := sequence_eq_of_subset_of_domain_eq hDS hreal hsub
  apply hnot
  rw [← heq, S.check_mem_iff]
  exact hD

include hτ hp₀ hnew in
/-- Decided segments below `p₀` are finite binary sequences. -/
theorem decidedSegment_mem_binarySequences {p : V} (hp : p ∈ P) (hpp₀ : ⟨p, p₀⟩ₖ ∈ R) :
    decidedSegment P R one τ p ∈ binarySequences V := by
  obtain ⟨D, hD⟩ : ∃ D, D = decidedSegment P R one τ p := ⟨_, rfl⟩
  have hDprod : D ⊆ (ω : V) ×ˢ ((2 : ℕ) : V) := by rw [hD]; exact sep_subset
  have hDmem : ∀ z, z ∈ D ↔ z ∈ (ω : V) ×ˢ ((2 : ℕ) : V) ∧ IsDecided P R one τ p z := by
    intro z
    rw [hD]
    exact mem_decidedSegment_iff _ _ _ _ _ _
  have hfun : D ∈ ((2 : ℕ) : V) ^ domain D := by
    rw [mem_function_iff]
    refine ⟨fun z hz ↦ ?_, fun x hx ↦ ?_⟩
    · obtain ⟨m, hm, i, hi, rfl⟩ := mem_prod_iff.mp (hDprod z hz)
      exact mem_prod_iff.mpr ⟨m, mem_domain_iff.mpr ⟨i, hz⟩, i, hi, rfl⟩
    · obtain ⟨y, hy⟩ := mem_domain_iff.mp hx
      refine ⟨y, hy, fun y' hy' ↦ ?_⟩
      obtain ⟨_, m, hm, i, hi, hz, hf, _⟩ := (hDmem _).mp hy
      obtain ⟨_, m', hm', i', hi', hz', hf', _⟩ := (hDmem _).mp hy'
      obtain ⟨rfl, rfl⟩ := kpair_inj hz
      obtain ⟨rfl, rfl⟩ := kpair_inj hz'
      exact (decided_unique hR htop hτ hp₀ hnew hp hpp₀ hf' hf)
  have hdomω : domain D ⊆ (ω : V) := by
    intro x hx
    obtain ⟨y, hy⟩ := mem_domain_iff.mp hx
    obtain ⟨m, hm, i, hi, hz⟩ := mem_prod_iff.mp (hDprod _ hy)
    obtain ⟨rfl, rfl⟩ := kpair_inj hz
    exact hm
  have htrans : IsTransitive (domain D) := by
    refine ⟨fun m hm ↦ ?_⟩
    intro m' hm'
    obtain ⟨y, hy⟩ := mem_domain_iff.mp hm
    obtain ⟨_, m₁, hm₁, i, hi, hz, hf, hall⟩ := (hDmem _).mp hy
    obtain ⟨rfl, rfl⟩ := kpair_inj hz
    obtain ⟨i', hi', hf'⟩ := hall m' hm'
    have hm'ω : m' ∈ (ω : V) := IsTransitive.ω.transitive m hm₁ m' hm'
    refine mem_domain_iff.mpr ⟨i', (hDmem _).mpr ⟨mem_prod_iff.mpr ⟨m', hm'ω, i', hi', rfl⟩,
      m', hm'ω, i', hi', rfl, hf', fun m'' hm'' ↦ hall m'' ((IsTransitive.nat hm₁).transitive m' hm' m'' hm'')⟩⟩
  have : IsOrdinal (domain D) :=
    IsOrdinal.of_transitive_of_isOrdinal htrans (fun β hβ ↦ IsOrdinal.nat (hdomω β hβ))
  rcases (IsOrdinal.subset_iff).mp hdomω with heq | hlt
  · exfalso
    refine not_decides_all hR htop hτ hp₀ hnew hp hpp₀ (D := D) (by unfold cantorSpace; rw [← heq]; exact hfun) ?_
    intro z hz
    obtain ⟨_, m, hm, i, hi, rfl, hf, _⟩ := (hDmem _).mp hz
    exact hf
  · rw [← hD, mem_binarySequences_iff]
    exact ⟨domain D, hlt, hfun⟩

include hτ hp₀ hnew in
/-- Below every condition below `p₀`, the decided segments split. -/
theorem decidedSegment_split {p : V} (hp : p ∈ P) (hpp₀ : ⟨p, p₀⟩ₖ ∈ R) :
    ∃ q ∈ P, ∃ q' ∈ P, ⟨q, p⟩ₖ ∈ R ∧ ⟨q', p⟩ₖ ∈ R ∧
      Incompatible (decidedSegment P R one τ q) (decidedSegment P R one τ q') := by
  by_contra hcon
  have hnot : ∀ q ∈ P, ∀ q' ∈ P, ⟨q, p⟩ₖ ∈ R → ⟨q', p⟩ₖ ∈ R →
      ¬ Incompatible (decidedSegment P R one τ q) (decidedSegment P R one τ q') :=
    fun q hq q' hq' h1 h2 hinc ↦ hcon ⟨q, hq, q', hq', h1, h2, hinc⟩
  -- the union of all decided segments below `p` is a ground real
  obtain ⟨r, hr⟩ : ∃ r, r = {z ∈ (ω : V) ×ˢ ((2 : ℕ) : V) ; ∃ q ∈ P, ⟨q, p⟩ₖ ∈ R ∧ IsDecided P R one τ q z} :=
    ⟨_, rfl⟩
  have hrmem : ∀ z, z ∈ r ↔ z ∈ (ω : V) ×ˢ ((2 : ℕ) : V) ∧ ∃ q ∈ P, ⟨q, p⟩ₖ ∈ R ∧ IsDecided P R one τ q z := by
    intro z
    rw [hr]
    exact mem_sep_iff
  have hsegfun : ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → IsFunction (decidedSegment P R one τ q) := fun q hq hqp ↦
    binarySequence_isFunction (decidedSegment_mem_binarySequences hR htop hτ hp₀ hnew hq
      (hR.2.2 q hq p hp p₀ hp₀ hqp hpp₀))
  have hdecmem : ∀ q m i, IsDecided P R one τ q ⟨m, i⟩ₖ → ⟨m, i⟩ₖ ∈ decidedSegment P R one τ q := by
    intro q m i h
    obtain ⟨m', hm', i', hi', hz, -, -⟩ := id h
    obtain ⟨rfl, rfl⟩ := kpair_inj hz
    exact (mem_decidedSegment_iff _ _ _ _ _ _).mpr ⟨mem_prod_iff.mpr ⟨m, hm', i, hi', rfl⟩, h⟩
  have hreal : r ∈ cantorSpace V := by
    unfold cantorSpace
    rw [mem_function_iff]
    refine ⟨fun z hz ↦ ((hrmem z).mp hz).1, fun m hm ↦ ?_⟩
    obtain ⟨q, hqD, hqp⟩ := decider_dense hR htop hτ hp₀ hnew m hm p hp hpp₀
    obtain ⟨hqP, hdec⟩ := (mem_deciderSet_iff _ _ _ _ _ _).mp hqD
    obtain ⟨i, hi, hf⟩ := hdec m (mem_succ_iff.mpr (Or.inl rfl))
    have hdecided : IsDecided P R one τ q ⟨m, i⟩ₖ :=
      ⟨m, hm, i, hi, rfl, hf, fun m' hm' ↦ hdec m' (mem_succ_iff.mpr (Or.inr hm'))⟩
    refine ⟨i, (hrmem _).mpr ⟨mem_prod_iff.mpr ⟨m, hm, i, hi, rfl⟩, q, hqP, hqp, hdecided⟩, ?_⟩
    intro i' hi'
    obtain ⟨hprod', q', hq'P, hq'p, hdecided'⟩ := (hrmem _).mp hi'
    obtain ⟨m₁, -, i₁, -, hz, -, -⟩ := id hdecided'
    obtain ⟨rfl, rfl⟩ := kpair_inj hz
    by_contra hne
    apply hnot q' hq'P q hqP hq'p hqp
    have := hsegfun q' hq'P hq'p
    have := hsegfun q hqP hqp
    have h1 : ⟨m, i'⟩ₖ ∈ decidedSegment P R one τ q' := hdecmem q' m i' hdecided'
    have h2 : ⟨m, i⟩ₖ ∈ decidedSegment P R one τ q := hdecmem q m i hdecided
    refine ⟨m, mem_domain_iff.mpr ⟨_, h1⟩, mem_domain_iff.mpr ⟨_, h2⟩, ?_⟩
    rw [value_eq_of_kpair_mem h1, value_eq_of_kpair_mem h2]
    exact hne
  -- in an extension through `p`, the new real equals `r`
  obtain ⟨G, hG, hpG⟩ := exists_externalForcingGeneric hR hp
  let S := genericContext hR htop hG
  have hp₀G : p₀ ∈ G := hG.1.2.2.1 p hpG p₀ hp₀ hpp₀
  obtain ⟨hτreal, hnot⟩ := newReal_of_generic hR htop hτ hp₀ hnew hG hp₀G
  have hcs := cantorSpace_eq_check S
  have hrS : S.check r ∈ S.check ((2 : ℕ) : V) ^ S.check (ω : V) :=
    (S.checkEmbedding.function_iff r (ω : V) ((2 : ℕ) : V)).mpr hreal
  rw [hcs] at hτreal
  have hsub : S.ofName ⟨τ, hτ⟩ ⊆ S.check r := by
    intro z hz
    have hzprod := (mem_function_iff.mp hτreal).1 z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hzprod
    obtain ⟨m, hm, rfl⟩ := (S.mem_check_iff _ _).mp ha
    obtain ⟨i, hi, rfl⟩ := (S.mem_check_iff _ _).mp hb
    rw [← S.check_kpair] at hz ⊢
    obtain ⟨q₁, hq₁G, hf₁⟩ := (S.checkedMember_truth ⟨τ, hτ⟩ _).mp hz
    obtain ⟨q₂, hq₂G, hq₂q₁, hq₂p⟩ := hG.1.2.2.2 q₁ hq₁G p hpG
    have hq₂P : q₂ ∈ P := hG.1.1 q₂ hq₂G
    obtain ⟨q₃, hq₃D, hq₃q₂⟩ := decider_dense hR htop hτ hp₀ hnew m hm q₂ hq₂P
      (hR.2.2 q₂ hq₂P p hp p₀ hp₀ hq₂p hpp₀)
    obtain ⟨hq₃P, hdec₃⟩ := (mem_deciderSet_iff _ _ _ _ _ _).mp hq₃D
    have hf₃ : ForcesCheckedMember P R one τ q₃ ⟨m, i⟩ₖ :=
      forcesCheckedMember_mono hR hq₃P (hR.2.2 q₃ hq₃P q₂ hq₂P q₁ (hG.1.1 q₁ hq₁G) hq₃q₂ hq₂q₁) hf₁
    have hq₃p : ⟨q₃, p⟩ₖ ∈ R := hR.2.2 q₃ hq₃P q₂ hq₂P p hp hq₃q₂ hq₂p
    rw [S.check_mem_iff]
    exact (hrmem _).mpr ⟨mem_prod_iff.mpr ⟨m, hm, i, hi, rfl⟩, q₃, hq₃P, hq₃p,
      m, hm, i, hi, rfl, hf₃, fun m' hm' ↦ hdec₃ m' (mem_succ_iff.mpr (Or.inr hm'))⟩
  have heq : S.ofName ⟨τ, hτ⟩ = S.check r := sequence_eq_of_subset_of_domain_eq hτreal hrS hsub
  apply hnot
  rw [heq, S.check_mem_iff]
  exact hreal

end

end ZFVP
