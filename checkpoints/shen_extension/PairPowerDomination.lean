import checkpoints.shen_extension.PairPowerOrder

/-! The common-predecessor lower bound of E. and G. Szekeres, "On a problem
of Schütte and Erdős". The argument below works directly for an oriented
relation, as in Proposition 14 of Reid et al., "Domination and irredundance
in tournaments". -/
namespace LeanCH.BR.PairPowerDomination
open Finset BRq2 BRq3 BR45 BypassRepair BypassBankReplay JointShortcutReplay

private theorem double_low {D : CH.Digraph} {V : Finset ℕ} {a : ℕ} (live : V.Nonempty)
    (asym : ∀ p∈V, ∀ r∈V, D p r=true → D r p≠true)
    (low : ∀ p∈V, a ≤ (inN D V p).card+1) : 2*a ≤ V.card+1 := by
  classical
  obtain ⟨p,pv,high⟩ : ∃ p∈V, (inN D V p).card ≤ (outN D V p).card := by
    by_contra! bad
    exact (ne_of_lt (sum_lt_sum_of_nonempty live bad)) (Compose.ThinRigid.sum_out_eq_sum_in D V)
  have noLoop : D p p ≠ true := fun e => asym p pv p pv e e
  have dis : Disjoint (inN D V p) (outN D V p) :=
    disjoint_left.mpr (fun h hm om => asym p pv h (mem_inN.mp hm).1 (mem_outN.mp om).2 (mem_inN.mp hm).2)
  have sub : inN D V p ∪ outN D V p ⊆ V.erase p := by
    intro h hm
    rcases mem_union.mp hm with im | om
    · obtain ⟨hv,hp⟩ := mem_inN.mp im
      exact mem_erase.mpr ⟨fun eq => noLoop (eq ▸ hp),hv⟩
    · obtain ⟨hv,ph⟩ := mem_outN.mp om
      exact mem_erase.mpr ⟨fun eq => noLoop (eq ▸ ph),hv⟩
  have cnt := card_le_card sub
  rw [card_union_of_disjoint dis,card_erase_of_mem pv] at cnt
  have bound := low p pv
  have := card_pos.mpr live
  omega

theorem domination_order {D : CH.Digraph} {V : Finset ℕ} (t : ℕ) (positive : 0<t)
    (asym : ∀ p∈V, ∀ r∈V, D p r=true → D r p≠true)
    (cover : ∀ S ⊆ V, S.card ≤ t → ∃ r∈V, ∀ p∈S, D r p=true) :
    (t+2)*2^(t-1) ≤ V.card+1 := by
  classical
  let C (S : Finset ℕ) := V.filter (fun r => ∀ p∈S, D r p=true)
  have sub (S) : C S ⊆ V := filter_subset _ _
  have base (S) (sv : S⊆V) (room : S.card<t) : t < (C S).card := by
    by_contra! small
    obtain ⟨r,rv,all⟩ := cover (C S) (sub _) small
    obtain ⟨w,wv,both⟩ := cover (insert r S) (insert_subset rv sv)
      (show (insert r S).card ≤ t by have := card_insert_le r S; omega)
    have wc : w∈C S := mem_filter.mpr ⟨wv,fun p hp => both p (mem_insert_of_mem hp)⟩
    exact asym w wv r rv (both r (mem_insert_self ..)) (all w wc)
  have expand (i : ℕ) : ∀ S ⊆ V, S.card+i<t → (t+2)*2^i ≤ (C S).card+1 := by
    induction i with
    | zero =>
      intro S sv size
      simpa only [pow_zero,Nat.mul_one] using
        (show t+2 ≤ (C S).card+1 by have := base S sv (by omega); omega)
    | succ i ih =>
      intro S sv size
      have live := card_pos.mp (show 0<(C S).card by have := base S sv (by omega); omega)
      have grow := double_low (D:=D) (V:=C S) (a:=(t+2)*2^i) live
        (fun p pv r rv => asym p (sub S pv) r (sub S rv)) (by
          intro p hp
          have n := card_insert_le p S
          have bound := ih (insert p S) (insert_subset (sub S hp) sv) (by omega)
          have eq : C (insert p S) = inN D (C S) p := by
            ext x
            simp only [C,mem_filter,mem_inN,forall_mem_insert]
            tauto
          rwa [eq] at bound)
      simpa only [pow_succ] using (show (t+2)*(2^i*2) ≤ (C S).card+1 by
        rwa [show (t+2)*(2^i*2) = 2*((t+2)*2^i) by ring])
  have n := expand (t-1) ∅ (empty_subset V) (by simp; omega)
  simpa only [C,notMem_empty,IsEmpty.forall_iff,implies_true,filter_true_of_mem] using n

theorem power_domination {D : CH.Digraph} {V : Finset ℕ} {q k : ℕ}
    (free : QFree D V q) (live : V.Nonempty) (hk : 0<k) (room : k+k≤q)
    (pair : ∀ u∈V, ∀ v∈V, ∃ w∈V, D w u=true ∧ D w v=true) :
    (2^k+2)*2^(2^k-1) ≤ V.card+1 := by
  classical
  let H : CH.Digraph := fun a b => decide (Walk D V a b k)
  apply domination_order (D:=H) (2^k) (by positivity)
  · intro a _ b _ e f
    have ab : Walk D V a b k := of_decide_eq_true e
    have ba : Walk D V b a k := of_decide_eq_true f
    exact free a (k+k) (by omega) room (ab.append ba)
  · intro S sv small
    obtain ⟨w,wv,hits⟩ := binary_ancestor live pair k sv small
    exact ⟨w,wv,fun u hu => decide_eq_true (hits u hu)⟩

@[aesop safe forward (immediate := [certificate,common,reg,hq,hs,none]) (rule_sets := [CHGraphFamilies])]
theorem selected_shared_domination {q s} {X : ShenMinimumOrder.Source q s} {m : Cell}
    (certificate : SelectedParentOrder X m) (common : SharedParent X.D (X.V \ m.bank) (s-1) m.parent)
    (reg : OutEq s X.D X.V) (hq : 3≤q) (hs : 8≤s) (none : NoHost q (s-1)) :
    (2^(q/2)+2)*2^(2^(q/2)-1) ≤ q*(s-1)+3 := by
  have order := certificate.shared.mp common
  have ep : DotDegreeSeven.Endpoint q (s-1) :=
    fun D V free live size deg => none D V live size.le free deg
  have cover := DotDegreeEight.pair_cover_of_endpoint ep (by omega) (by omega) X.free order
    (by simpa only [show s-1+1=s by omega] using reg)
  have pair (u) (uv : u∈X.V) (v) (vv : v∈X.V) : ∃ w∈X.V, X.D w u=true ∧ X.D w v=true := by
    by_cases eq : u=v
    · subst v
      obtain ⟨w,wv,ed,_⟩ := ShenCycleSuccessor.fixed_parent X (by omega) (by omega) uv
      exact ⟨w,wv,ed,ed⟩
    · exact cover _ uv _ vv eq
  have bound := power_domination X.free X.nonempty (show 0<q/2 by omega) (by omega) pair
  omega

#print axioms domination_order
#print axioms power_domination
#print axioms selected_shared_domination
end LeanCH.BR.PairPowerDomination
