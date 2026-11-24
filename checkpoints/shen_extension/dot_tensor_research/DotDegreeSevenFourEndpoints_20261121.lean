import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5Order33_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ6Growth_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7Mixed_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ8_20261121
import checkpoints.shen_extension.CHRuleCatalog
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSeven_20261121
import LeanCH.BR.Triangle24

namespace LeanCH.BR.DotDegreeSeven
open Finset BRq2 BRq3 CHRuleCatalog

structure FourOpenEndpoints : Prop where
  four : Endpoint 4 7
  five : Endpoint 5 7
  six : Endpoint 6 7
  seven : Endpoint 7 7


/-- Replay the two verified child-order closures at any catalog descendant. -/
theorem degree_seven_closed_strips_at_descendant {p c : Input} (b : Bad p)
    (path : Relation.ReflTransGen Child p c) (r : c.s = 7)
    (low : (cutoff c = 4 ∧ c.n ≤ 26) ∨ (cutoff c = 5 ∧ c.n ≤ 33) ∨ (cutoff c = 6 ∧ c.n ≤ 40) ∨ (cutoff c = 7 ∧ c.n ≤ 47) ∨ (cutoff c = 8 ∧ c.n ≤ 56)) : False := by
  have d := bad_descendant b path
  have hf := qfree_of_noShort d.loopless d.missing
  have hm : ∀ v ∈ range c.n, 7 ≤ (outN c.D (range c.n) v).card := by
    intro v hv
    rw [←r]
    exact Compose.FloorSix.out_card d.degree (mem_range.mp hv)
  have ne : (range c.n).Nonempty := nonempty_range_iff.mpr (by have := d.order; omega)
  rcases low with h | h | h | h | h
  · have e := DotDegreeSevenLow.four_free_ge27 (by simpa only [h.1] using hf) hm ne
    rw [card_range] at e
    omega
  · have e := DotDegreeSevenLow.five_free_ge34 (by simpa only [h.1] using hf) hm ne
    rw [card_range] at e
    omega
  · have e := DotDegreeSevenQ6.six_free_min_seven_ge41
      (by simpa only [h.1] using hf) hm ne
    rw [card_range] at e
    omega
  · have e := DotDegreeSevenQ7.seven_free_min_seven_ge48
      (by simpa only [h.1] using hf) hm ne
    rw [card_range] at e
    omega

  · exact DotDegreeSevenQ8.eight_free_seven_order (by simpa only [h.1] using hf) ne
      (by simpa only [card_range] using h.2) hm

/-- Literal r=7 capstone: the four endpoint obligations remain explicit. -/
theorem ch_seven_of_four_endpoints (E : FourOpenEndpoints) (n : ℕ) (D : CH.Digraph)
    (hn : 0<n) (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n 7) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n 7) := by
  by_contra no
  let q := CH.ceilDiv n 7
  have cover : n ≤ q*7 := by
    have mod := Nat.mod_lt (n+7-1) (by decide : 0<7)
    have div := Nat.mod_add_div (n+7-1) 7
    rw [Nat.mul_comm 7] at div
    dsimp [q,CH.ceilDiv]
    omega
  have h := remaining_from_run ⟨n,7,D⟩ ⟨hn,(by change 0 < (7:ℕ); decide),loop,degree,no⟩
  change 3≤q ∧ 6≤(7:ℕ) ∧
    ((q=2*7-6 ∧ 7≤(7:ℕ) ∧ (7:ℕ)≤11 ∧ (n=q*7 ∨ (7:ℕ)=7 ∧ n+1=q*7)) ∨
      (q≤2*7-7 ∧ (59≤(7:ℕ) → q≤2*7-8) ∧ (8192≤(7:ℕ) → q≤2*7-9))) at h
  change ¬CH.HasDirectedCycleAtMost D n q at no
  rcases (by omega : q=3 ∨ q=4 ∨ q=5 ∨ q=6 ∨ q=7 ∨ q=8) with h3|h4|h5|h6|h7|h8
  · rw [h3] at no cover
    exact no (Triangle24.triangle_le_24 n 7 hn (by omega) cover D loop degree)
  · rw [h4] at no cover
    exact no (from_endpoint E.four hn cover loop degree)
  · rw [h5] at no cover
    exact no (from_endpoint E.five hn cover loop degree)
  · rw [h6] at no cover
    exact no (from_endpoint E.six hn cover loop degree)
  · rw [h7] at no cover
    exact no (from_endpoint E.seven hn cover loop degree)
  · rw [h8] at no cover
    exact no (DotDegreeSevenQ8.eight_seven_literal hn (by omega) loop degree)

#print axioms degree_seven_closed_strips_at_descendant
#print axioms ch_seven_of_four_endpoints
end LeanCH.BR.DotDegreeSeven
