import ZFVP.ModelTheory.RankInternalCollapseName
import ZFVP.ModelTheory.RankForcingNameHierarchy
import ZFVP.ModelTheory.TransitiveZFSaturatedName
import ZFVP.ModelTheory.SaturatedNameGenericEquality
import ZFVP.ModelTheory.SaturatedWoodinPrefix

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable V]
variable {ξ : V} [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
  [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_saturatedWoodinPrefixPosetName_val_countable (hξ : IsChoicelessInaccessible ξ)
    (P R one κ γ : SetDomain (hierarchy ξ)) (hR : IsForcingPreorder P R)
    (ht : IsForcingTop P R one) (hγ : IsOrdinal γ) :
    (saturatedWoodinPrefixPosetName P R one κ γ).val =
      saturatedWoodinPrefixPosetName P.val R.val one.val κ.val γ.val := by
  let := hierarchy_transitive ξ
  let := (TransitiveZF.ordinal_iff (hierarchy ξ) γ).mp hγ
  have hR' := (TransitiveZF.forcingPreorder_iff (hierarchy ξ) P R).mp hR
  have ht' := (TransitiveZF.forcingTop_iff (hierarchy ξ) P R one).mp ht
  let Q : ForcingName P.val := ⟨(woodinPrefixPosetName P R one κ γ).val,
    (TransitiveZF.forcingName_iff (hierarchy ξ) P _).mp (woodinCollapseName_isName _ _ _ _)⟩
  let Q' : ForcingName P.val := ⟨woodinPrefixPosetName P.val R.val one.val κ.val γ.val,
    woodinCollapseName_isName _ _ _ _⟩
  unfold saturatedWoodinPrefixPosetName
  rw [TransitiveZF.forcingSaturatedName_val,
    rank_forcingNameHierarchy_val (fun _ hb ↦ regularCardinal_succ_closed hξ.regular hb) P γ hγ]
  apply forcingSaturatedName_eq_of_all_values hR' ht' _ Q Q'
  intro G hG
  let A : ForcingContext V := ⟨P.val, R.val, one.val, G, hR', ht', hG⟩
  have hi : A.ofName Q = woodinCollapse (A.check κ.val) (A.check γ.val) :=
    A.rankInternalCollapse_value hξ P R one κ γ rfl rfl rfl hγ
  let cκ : ForcingName P.val := ⟨checkName one.val κ.val, checkName_isName ht'.1 κ.val⟩
  let cγ : ForcingName P.val := ⟨checkName one.val γ.val, checkName_isName ht'.1 γ.val⟩
  let : IsOrdinal (A.ofName cγ) := by change IsOrdinal (A.check γ.val); infer_instance
  have ho : A.ofName Q' = woodinCollapse (A.check κ.val) (A.check γ.val) :=
    A.collapseName_value_of_ordinal cκ cγ
  exact hi.trans ho.symm

end ZFVP
