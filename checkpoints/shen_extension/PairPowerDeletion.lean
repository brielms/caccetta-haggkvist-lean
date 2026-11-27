import checkpoints.shen_extension.PairPowerTransfer

namespace LeanCH.BR.PairPowerDeletion
open Finset BRq2 BRq3 BR45 BypassBankReplay BypassRepair PairPowerDomination CHRuleCatalog

/-- A physical two-vertex deletion valid at any order passing either
test. Thinning accommodates rows with spare heads in the original graph. -/
theorem delete_two {D : CH.Digraph} {V : Finset ℕ} {q s : ℕ}
    (hq : 2≤q) (hs : 2≤s) (live : V.Nonempty) (free : QFree D V q)
    (deg : ∀ v∈V, s≤(outN D V v).card)
    (gap : s≤2^(q-1) ∨ V.card+1 < (2^(q/2)+2)*2^(2^(q/2)-1)) :
    ∃ a∈V, ∃ b∈V, a≠b ∧
      ((V.erase a).erase b).Nonempty ∧ ((V.erase a).erase b).card+2=V.card ∧
      ∀ w∈(V.erase a).erase b, s-1 ≤ (outN D ((V.erase a).erase b) w).card := by
  classical
  obtain ⟨E,sub,reg⟩ := exists_outEq deg
  have safe := qfree_sub sub free
  have large : 2<V.card := by
    obtain ⟨v,vv⟩ := live
    have inc : outN E V v ⊆ V.erase v := by
      intro z hz
      exact mem_erase.mpr ⟨fun eq => loopfree safe (by omega) vv (eq ▸ (mem_outN.mp hz).2),outN_subset hz⟩
    have count := card_le_card inc
    rw [reg v vv,card_erase_of_mem vv] at count
    omega
  by_cases paired : ∀ u∈V, ∀ v∈V, u≠v → ∃ w∈V, E w u=true ∧ E w v=true
  · exfalso
    have both (u) (uv : u∈V) (v) (vv : v∈V) : ∃ w∈V, E w u=true ∧ E w v=true := by
      by_cases eq : u=v
      · subst v
        have non : (V.erase u).Nonempty := card_pos.mp (by rw [card_erase_of_mem uv]; omega)
        obtain ⟨z,hz⟩ := non
        obtain ⟨w,wv,wu,_⟩ := paired u uv z (mem_erase.mp hz).2 (mem_erase.mp hz).1.symm
        exact ⟨w,wv,wu,wu⟩
      · exact paired _ uv _ vv eq
    rcases gap with small | small
    · have high (p) (pv : p∈V) : (outN E V p).card < (inN E V p).card := by
        have := indegree_of_binary_return safe live (by omega) both pv
        rw [reg p pv]
        omega
      exact (ne_of_lt (sum_lt_sum_of_nonempty live high)) (Compose.ThinRigid.sum_out_eq_sum_in E V)
    · exact (not_lt_of_ge (power_domination safe live (show 0<q/2 by omega) (by omega) both)) small
  · push Not at paired
    obtain ⟨a,av,b,bv,ab,no⟩ := paired
    have cnt : ((V.erase a).erase b).card+2=V.card := by
      rw [card_erase_of_mem (mem_erase.mpr ⟨ab.symm,bv⟩),card_erase_of_mem av]
      omega
    refine ⟨a,av,b,bv,ab,card_pos.mp (by omega),cnt,?_⟩
    intro w hw
    have wv := mem_of_mem_erase (mem_of_mem_erase hw)
    have row : outN E ((V.erase a).erase b) w = ((outN E V w).erase a).erase b := by
      ext z
      simp only [mem_outN,mem_erase]
      tauto
    have size := reg w wv
    have survivor : s-1≤(outN E ((V.erase a).erase b) w).card := by
      rw [row]
      by_cases wa : a∈outN E V w
      · have wb : b∉(outN E V w).erase a := fun z =>
          no w wv (mem_outN.mp wa).2 (mem_outN.mp (mem_of_mem_erase z)).2
        rw [erase_eq_of_notMem wb,card_erase_of_mem wa,size]
      · rw [erase_eq_of_notMem wa]
        by_cases wb : b∈outN E V w
        · rw [card_erase_of_mem wb,size]
        · rw [erase_eq_of_notMem wb,size]
          omega
    exact survivor.trans (card_le_card (fun z hz => mem_outN.mpr
      ⟨(mem_outN.mp hz).1,sub w z (mem_outN.mp hz).2⟩))

/-- Iterate on the original induced digraph. A known base quota d supports
two additional vertices per additional unit of minimum outdegree. -/
theorem iterated_window {q d : ℕ} (hq : 2≤q) (hd : 0<d) (base : NoHost q d) (e : ℕ)
    {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V q) (live : V.Nonempty)
    (deg : ∀ v∈V, d+e ≤ (outN D V v).card) (cap : V.card≤q*d+2*e)
    (gap : d+e≤2^(q-1) ∨ V.card+1 < (2^(q/2)+2)*2^(2^(q/2)-1)) : False := by
  induction e generalizing V with
  | zero =>
    exact base D V live (by simpa using cap) free (by simpa using deg)
  | succ e ih =>
    obtain ⟨a,_,b,_,_,live',count,cost⟩ := delete_two hq (by omega) live free deg gap
    have sub : (V.erase a).erase b ⊆ V := (erase_subset ..).trans (erase_subset ..)
    apply ih (free.mono_set sub) live' (by simpa using cost) (by omega)
    rcases gap with g | g
    · left; omega
    · right; omega

/-- Uniform public window with the project's global degree-nine theorem as
a base case. The input order, degree and cutoff are all symbolic. -/
theorem from_degree_nine {n s : ℕ} (D : CH.Digraph) (hn : 0<n) (hs : 9≤s)
    (hq : 2≤CH.ceilDiv n s)
    (cap : n≤CH.ceilDiv n s*9+2*(s-9))
    (gap : s≤2^(CH.ceilDiv n s-1) ∨
      n+1 < (2^(CH.ceilDiv n s/2)+2)*2^(2^(CH.ceilDiv n s/2)-1))
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n s) := by
  classical
  by_contra fail
  let p : Input := ⟨n,s,D⟩
  have bad : Bad p := ⟨hn,by exact (by omega : 0<s),loopless,degree,fail⟩
  have base : NoHost (cutoff p) 9 := by
    intro E U live size free min
    obtain ⟨c,_,edge,nine,_,_⟩ := BypassDegreeDescent.host_child p (by decide : 0<9)
      (by exact (by omega : 1≤CH.ceilDiv n s)) live size free min
    have cb := bad_child bad edge
    apply cb.missing
    change CH.HasDirectedCycleAtMost c.D c.n (CH.ceilDiv c.n c.s)
    rw [nine]
    exact LeanCH.Results.degree_nine _ cb.order cb.loopless (nine ▸ cb.degree)
  have exact_s : 9+(s-9)=s := by omega
  exact iterated_window (q:=CH.ceilDiv n s) hq (by decide : 0<9) base (s-9)
    (qfree_of_noShort loopless fail) ⟨0,mem_range.mpr hn⟩
    (fun v hv => by rw [exact_s]; exact Compose.FloorSix.out_card degree (mem_range.mp hv))
    (by simpa only [card_range] using cap) (by simpa only [card_range,exact_s] using gap)

#print axioms from_degree_nine
#print axioms delete_two
#print axioms iterated_window
end LeanCH.BR.PairPowerDeletion
