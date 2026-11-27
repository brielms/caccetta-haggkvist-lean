import checkpoints.shen_extension.PairPowerDomination
import checkpoints.shen_extension.PublicResults

namespace LeanCH.BR.PairPowerTransfer
open Finset BRq2 BRq3 BR45 BypassRepair BypassBankReplay PairPowerDomination CHRuleCatalog

/-- A previous-degree endpoint forces either both numerical bounds or
an improvement on the two-label order floor, without a marked source. -/
theorem two_label_floor {D : CH.Digraph} {V : Finset ℕ} {q s : ℕ}
    (hq : 2≤q) (hs : 2≤s) (free : QFree D V q) (live : V.Nonempty)
    (deg : ∀ p∈V, s≤(outN D V p).card) (none : NoHost q (s-1))
    (cap : V.card≤q*(s-1)+2) :
    2^(q-1)<s ∧ (2^(q/2)+2)*2^(2^(q/2)-1) ≤ q*(s-1)+3 := by
  classical
  have order := le_antisymm cap (order_floor none hs free live deg)
  obtain ⟨E,sub,reg⟩ := exists_outEq deg
  have safe := qfree_sub sub free
  have ep : DotDegreeSeven.Endpoint q (s-1) :=
    fun F W safe live size min => none F W live size.le safe min
  have cover := DotDegreeEight.pair_cover_of_endpoint ep (by omega) (by omega) safe order
    (by simpa only [show s-1+1=s by omega] using reg)
  have pair (u) (uv : u∈V) (v) (vv : v∈V) : ∃ w∈V, E w u=true ∧ E w v=true := by
    by_cases eq : u=v
    · subst v
      have high := (deg u uv).trans (card_le_card (outN_subset : outN D V u⊆V))
      have many : (V.erase u).Nonempty := card_pos.mp (by rw [card_erase_of_mem uv]; omega)
      obtain ⟨x,hx⟩ := many
      obtain ⟨w,wv,wu,_⟩ := cover u uv x (mem_erase.mp hx).2 (mem_erase.mp hx).1.symm
      exact ⟨w,wv,wu,wu⟩
    · exact cover _ uv _ vv eq
  have dbl := power_domination safe live (show 0<q/2 by omega) (by omega) pair
  refine ⟨?_,by omega⟩
  by_contra! small
  have high (p) (pv : p∈V) : (outN E V p).card < (inN E V p).card := by
    have := indegree_of_binary_return safe live (by omega) pair pv
    rw [reg p pv]
    omega
  exact (ne_of_lt (sum_lt_sum_of_nonempty live high)) (Compose.ThinRigid.sum_out_eq_sum_in E V)

/-- A public degree transfer on the first two labels above the previous
quota. Its only graph-theoretic input is the previous degree's CH theorem. -/
theorem cycle_of_previous {n s q : ℕ} (D : CH.Digraph) (hn : 0<n) (hs : 2≤s)
    (cut : CH.ceilDiv n s=q) (hq : 2≤q) (cap : n≤q*(s-1)+2)
    (gap : s≤2^(q-1) ∨ q*(s-1)+3 < (2^(q/2)+2)*2^(2^(q/2)-1))
    (previous : ∀ m (E : CH.Digraph), 0<m → CH.Loopless E m →
      CH.MinOutdegreeAtLeast E m (s-1) → CH.HasDirectedCycleAtMost E m (CH.ceilDiv m (s-1)))
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n s) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n s) := by
  classical
  by_contra fail
  let p : Input := ⟨n,s,D⟩
  have pc : cutoff p=q := cut
  have bad : Bad p := ⟨hn,by exact (by omega : 0<s),loopless,degree,fail⟩
  have none : NoHost q (s-1) := by
    intro E U live size free deg
    rw [←pc] at size free
    obtain ⟨c,_,edge,low,_,_⟩ := BypassDegreeDescent.host_child p (by omega : 0<s-1)
      (by omega) live size free deg
    have cb := bad_child bad edge
    apply cb.missing
    change CH.HasDirectedCycleAtMost c.D c.n (CH.ceilDiv c.n c.s)
    rw [low]
    exact previous _ _ cb.order cb.loopless (low ▸ cb.degree)
  have free : QFree D (range n) q := cut ▸ qfree_of_noShort loopless fail
  have min (v) (vv : v∈range n) := Compose.FloorSix.out_card degree (mem_range.mp vv)
  obtain ⟨ex,pw⟩ := two_label_floor hq hs free ⟨0,mem_range.mpr hn⟩ min none (by simpa using cap)
  rcases gap with small | small <;> omega

/-- An unconditional degree-ten consequence at all cutoffs ≥4, using the
project's previously checked degree-nine theorem as the induction input. -/
theorem degree_ten_window {n : ℕ} (D : CH.Digraph) (hn : 0<n)
    (hq : 4≤CH.ceilDiv n 10) (window : n≤9*(CH.ceilDiv n 10)+2)
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n 10) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n 10) := by
  apply cycle_of_previous D hn (by decide : 2≤10) rfl (by omega) (by simpa [Nat.mul_comm] using window)
    _ (fun m E h l d => LeanCH.Results.degree_nine E h l d) loopless degree
  by_cases four : CH.ceilDiv n 10=4
  · right
    rw [four]
    decide
  · left
    have exp := Nat.pow_le_pow_right (show 1≤2 by decide) (show 4≤CH.ceilDiv n 10-1 by omega)
    omega

#print axioms two_label_floor
#print axioms cycle_of_previous
#print axioms degree_ten_window
end LeanCH.BR.PairPowerTransfer
