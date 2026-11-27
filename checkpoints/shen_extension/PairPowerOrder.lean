import checkpoints.shen_extension.JointBankOrderReplay

/-! An integer form of the power-graph argument in Theorem 4 of Korándi and
Sudakov, "Domination in 3-tournaments", attributed there to Lubetzky, Shapira
and Sudakov. Apply it to the pair coverage on the two-label shared-parent band. -/

namespace LeanCH.BR.PairPowerOrder
open Finset BRq2 BRq3 BR45 BypassRepair BypassBankReplay JointShortcutReplay

/-- In an oriented relation, a common predecessor for every set of at most
t vertices requires at least 2^(t+1)-1 vertices. -/
theorem common_set_order {D : CH.Digraph} {V : Finset ℕ} (t : ℕ)
    (asym : ∀ p∈V, ∀ r∈V, D p r=true → D r p≠true)
    (cover : ∀ S ⊆ V, S.card ≤ t → ∃ r∈V, ∀ p∈S, D r p=true) :
    2^(t+1) ≤ V.card+1 := by
  classical
  induction t generalizing V with
  | zero =>
    obtain ⟨r,rv,_⟩ := cover ∅ (empty_subset _) (by simp)
    have pos := card_pos.mpr (show V.Nonempty from ⟨r,rv⟩)
    omega
  | succ t ih =>
    obtain ⟨r,rv,_⟩ := cover ∅ (empty_subset _) (by simp)
    have live : V.Nonempty := ⟨r,rv⟩
    have low (p) (pv : p∈V) : 2^(t+1) ≤ (inN D V p).card+1 := by
      have sub : inN D V p ⊆ V := fun h hm => (mem_inN.mp hm).1
      apply ih (V:=inN D V p) (fun l lm m mm => asym l (sub lm) m (sub mm))
      intro S sp sc
      obtain ⟨m,mv,hits⟩ := cover (insert p S) (insert_subset pv (sp.trans sub))
        ((card_insert_le ..).trans (Nat.add_le_add_right sc 1))
      exact ⟨m,mem_inN.mpr ⟨mv,hits p (mem_insert_self ..)⟩,fun h hm => hits h (mem_insert_of_mem hm)⟩
    have balanced : ∃ p∈V, (inN D V p).card ≤ (outN D V p).card := by
      by_contra! bad
      have strict := sum_lt_sum_of_nonempty live bad
      exact (ne_of_lt strict) (Compose.ThinRigid.sum_out_eq_sum_in D V)
    obtain ⟨p,pv,size⟩ := balanced
    have noLoop : D p p ≠ true := fun ed => asym p pv p pv ed ed
    have dis : Disjoint (inN D V p) (outN D V p) :=
      disjoint_left.mpr (fun h hm om => asym p pv h (mem_inN.mp hm).1 (mem_outN.mp om).2 (mem_inN.mp hm).2)
    have sub : inN D V p ∪ outN D V p ⊆ V.erase p := by
      intro h hm
      rcases mem_union.mp hm with im | om
      · obtain ⟨hv,hp⟩ := mem_inN.mp im
        exact mem_erase.mpr ⟨fun eq => noLoop (eq ▸ hp),hv⟩
      · obtain ⟨hv,ph⟩ := mem_outN.mp om
        exact mem_erase.mpr ⟨fun eq => noLoop (eq ▸ ph),hv⟩
    have both := card_le_card sub
    rw [card_union_of_disjoint dis,card_erase_of_mem pv] at both
    have bound := low p pv
    rw [pow_succ]
    have pos := card_pos.mpr live
    omega

/-- At any positive radius k with 2k ≤ q, the exact-k walk relation on
a pair-covered carrier is oriented and has the common-ancestor property
for sets of size at most 2^k. -/
theorem power_order {D : CH.Digraph} {V : Finset ℕ} {q k : ℕ}
    (free : QFree D V q) (live : V.Nonempty) (hk : 0 < k) (room : k+k ≤ q)
    (pair : ∀ u∈V, ∀ v∈V, ∃ w∈V, D w u=true ∧ D w v=true) :
    2^(2^k+1) ≤ V.card+1 := by
  classical
  let H : CH.Digraph := fun a b => decide (Walk D V a b k)
  apply common_set_order (D:=H) (2^k)
  · intro u _ v _ uv vu
    have go : Walk D V u v k := of_decide_eq_true uv
    have back : Walk D V v u k := of_decide_eq_true vu
    exact free u (k+k) (by omega) room (go.append back)
  · intro S sv size
    obtain ⟨w,wv,walk⟩ := binary_ancestor live pair k sv size
    exact ⟨w,wv,fun a am => decide_eq_true (walk a am)⟩

theorem at_two {q s} (X : ShenMinimumOrder.Source q s) (reg : OutEq s X.D X.V)
    (hq : 2 ≤ q) (hs : 2 ≤ s) (order : X.V.card=q*(s-1)+2) (none : NoHost q (s-1)) :
    2^(2^(q/2)+1) ≤ q*(s-1)+3 := by
  have ep : DotDegreeSeven.Endpoint q (s-1) :=
    fun D V free live size deg => none D V live size.le free deg
  have cover := DotDegreeEight.pair_cover_of_endpoint ep (by omega) (by omega) X.free order
    (by simpa only [show s-1+1=s by omega] using reg)
  have pair (u) (uv : u∈X.V) (v) (vv : v∈X.V) : ∃ w∈X.V, X.D w u=true ∧ X.D w v=true := by
    by_cases eq : u=v
    · subst v
      obtain ⟨w,wv,ed,_⟩ := ShenCycleSuccessor.fixed_parent X hq (by omega) uv
      exact ⟨w,wv,ed,ed⟩
    · exact cover _ uv _ vv eq
  have bound := power_order X.free X.nonempty (show 0<q/2 by omega) (by omega) pair
  omega

/-- A restriction on the same marked source as the root shared-parent leaf. -/
@[aesop safe forward (immediate := [certificate,common,reg,hq,hs,none]) (rule_sets := [CHGraphFamilies])]
theorem selected_shared_order {q s} {X : ShenMinimumOrder.Source q s} {m : BypassBankReplay.Cell}
    (certificate : SelectedParentOrder X m) (common : SharedParent X.D (X.V \ m.bank) (s-1) m.parent)
    (reg : OutEq s X.D X.V) (hq : 3 ≤ q) (hs : 8 ≤ s) (none : NoHost q (s-1)) :
    2^(2^(q/2)+1) ≤ q*(s-1)+3 :=
  at_two X reg (by omega) (by omega) (certificate.shared.mp common) none

#print axioms common_set_order
#print axioms power_order
#print axioms at_two
#print axioms selected_shared_order
end LeanCH.BR.PairPowerOrder
