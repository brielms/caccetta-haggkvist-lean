import checkpoints.shen_extension.PairPowerOrder
import checkpoints.shen_extension.ReachLedger

namespace LeanCH.BR.PairPowerGrowth
open Finset BRq2 BRq3 BR45 BypassRepair BypassBankReplay PairPowerOrder

/-- At odd cutoffs a native forward growth step still avoids the entire
exact-k predecessor set. Both sets start with exponentially many labels. -/
theorem odd_growth {D : CH.Digraph} {V : Finset ℕ} {q s k L : ℕ}
    (free : QFree D V q) (live : V.Nonempty) (hk : 0<k) (room : k+k+1≤q)
    (pair : ∀ u∈V, ∀ v∈V, ∃ w∈V, D w u=true ∧ D w v=true)
    (hs : 1≤s) (deg : ∀ p∈V, s ≤ (outN D V p).card)
    (lower : ∀ t<s, NoHost q t) (order : V.card=q*(s-1)+2)
    (power : L+1=2^(2^k)) :
    (2*q-1)*L+q*(s+1)+1 ≤ q*V.card := by
  classical
  let H : CH.Digraph := fun a b => decide (Walk D V a b k)
  have low (p) (pv : p∈V) : L ≤ (inN H V p).card := by
    have base : 1 ≤ 2^k := Nat.one_le_two_pow
    have est : 2^((2^k-1)+1) ≤ (inN H V p).card+1 := by
      apply common_set_order (D:=H)
      · intro a _ b _ e f
        have ab : Walk D V a b k := of_decide_eq_true e
        have ba : Walk D V b a k := of_decide_eq_true f
        exact free a (k+k) (by omega) (by omega) (ab.append ba)
      · intro S sp sc
        have sv : S⊆V := fun h hm => (mem_inN.mp (sp hm)).1
        have bound := card_insert_le p S
        obtain ⟨w,wv,path⟩ := binary_ancestor live pair k (insert_subset pv sv)
          (show (insert p S).card ≤ 2^k by omega)
        exact ⟨w,mem_inN.mpr ⟨wv,decide_eq_true (path p (mem_insert_self ..))⟩,
          fun a ha => decide_eq_true (path a (mem_insert_of_mem ha))⟩
    rw [show 2^k-1+1=2^k by omega,←power] at est
    omega
  obtain ⟨v,vv,out⟩ : ∃ v∈V, (inN H V v).card ≤ (outN H V v).card := by
    by_contra! bad
    exact (ne_of_lt (sum_lt_sum_of_nonempty live bad)) (Compose.ThinRigid.sum_out_eq_sum_in H V)
  have incoming := low v vv
  have lo : L+1 ≤ (ball D V v k).card := by
    have sub : insert v (outN H V v) ⊆ ball D V v k := by
      intro a ha
      rcases mem_insert.mp ha with rfl | ha
      · exact mem_ball.mpr ⟨vv,0,by omega,.refl _⟩
      · obtain ⟨av,path⟩ := mem_outN.mp ha
        exact mem_ball.mpr ⟨av,k,le_rfl,of_decide_eq_true path⟩
    have noLoop : v ∉ outN H V v := fun h =>
      free v k hk (by omega) (of_decide_eq_true (mem_outN.mp h).2)
    have number := card_le_card sub
    rw [card_insert_of_notMem noLoop] at number
    omega
  have dis : Disjoint (inN H V v) (ball D V v (k+1)) := by
    apply disjoint_left.mpr
    intro a ia ba
    have av : Walk D V a v k := of_decide_eq_true (mem_inN.mp ia).2
    obtain ⟨_,j,jle,va⟩ := mem_ball.mp ba
    exact free a (k+j) (by omega) (by omega) (av.append va)
  have sub : inN H V v ∪ ball D V v (k+1) ⊆ V := by
    intro a ha
    rcases mem_union.mp ha with hl | hr
    · exact (mem_inN.mp hl).1
    · exact (mem_ball.mp hr).1
  have budget := card_le_card sub
  rw [card_union_of_disjoint dis] at budget
  have mono : (ball D V v k).card ≤ (ball D V v (k+1)).card :=
    card_le_card (ball_mono_radius (by omega))
  let e := (ball D V v k).card-1
  have eSize : (ball D V v k).card=e+1 := by dsimp [e]; omega
  have positive : 1≤L := by
    have one : 1≤2^k := Nat.one_le_two_pow
    have two := Nat.pow_le_pow_right (show 1≤2 by decide) one
    omega
  have qpos : 0<q := by omega
  let t := (e+q-1)/q
  have top : t*q ≤ e+q-1 := Nat.div_mul_le_self ..
  have bot : e ≤ t*q := by
    have ll := Nat.lt_div_mul_add (a:=e+q-1) qpos
    change e ≤ (e+q-1)/q*q
    omega
  have ts : t<s := by
    have es : e ≤ q*(s-1) := by omega
    have : e+q-1 < s*q := by
      calc
        e+q-1 < q*(s-1)+q := by omega
        _ = s*q := by rw [←Nat.mul_succ,show (s-1).succ=s by omega,Nat.mul_comm]
    exact (Nat.div_lt_iff_lt_mul qpos).mpr this
  have grow := ReachLedger.ball_growth (lower t ts) free deg hs vv hk (by omega : k+1≤q)
    (show (ball D V v k).card ≤ q*t+1 by rw [Nat.mul_comm q t]; omega)
  have eL : L≤e := by omega
  have a : e+s+2+L ≤ V.card+t := by omega
  have scale := Nat.mul_le_mul_left q a
  have e_scale := Nat.mul_le_mul_left (q-1) eL
  have qpred : (q-1).succ=q := by omega
  have doub : 2*q-1=(q-1)+q := by omega
  rw [doub, Nat.add_mul]
  rw [Nat.mul_comm t q] at top
  have tops : q*t+1 ≤ e+q := by omega
  nlinarith only [scale,e_scale,tops,show (q-1)*e+e=q*e by rw [←Nat.succ_mul,qpred],
    show (q-1)*L+L=q*L by rw [←Nat.succ_mul,qpred]]

/-- Apply the extra growth step to the selected two-label source itself. -/
theorem selected_shared_growth {q s k L : ℕ} {X : ShenMinimumOrder.Source q s}
    {m : BypassBankReplay.Cell} (certificate : BypassBankReplay.SelectedParentOrder X m)
    (common : JointShortcutReplay.SharedParent X.D (X.V \ m.bank) (s-1) m.parent)
    (reg : OutEq s X.D X.V) (hs : 2≤s) (hk : 0<k) (room : k+k+1≤q)
    (lower : ∀ t<s, NoHost q t) (power : L+1=2^(2^k)) :
    (2*q-1)*L+q*(s+1)+1 ≤ q*(q*(s-1)+2) := by
  have order := certificate.shared.mp common
  have ep : DotDegreeSeven.Endpoint q (s-1) :=
    fun D V free live size deg => lower _ (by omega) D V live size.le free deg
  have cover := DotDegreeEight.pair_cover_of_endpoint ep (by omega) (by omega) X.free order
    (by simpa only [show s-1+1=s by omega] using reg)
  have pair (u) (uv : u∈X.V) (v) (vv : v∈X.V) : ∃ w∈X.V, X.D w u=true ∧ X.D w v=true := by
    by_cases eq : u=v
    · subst v
      obtain ⟨w,wv,ed,_⟩ := ShenCycleSuccessor.fixed_parent X (by omega) (by omega) uv
      exact ⟨w,wv,ed,ed⟩
    · exact cover _ uv _ vv eq
  simpa only [order] using odd_growth X.free X.nonempty hk room pair (by omega) X.degree lower order power

#print axioms odd_growth
#print axioms selected_shared_growth
end LeanCH.BR.PairPowerGrowth
