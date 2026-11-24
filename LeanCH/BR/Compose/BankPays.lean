import LeanCH.BR.CH.Side.ScInducedSubgraphTransport
import LeanCH.BR.CH.Side.ScFinsetEnumeration
import LeanCH.BR.CH.Research.FixedDegreeCH

/-!
`bank_pays`: if every vertex of a nonempty bank `K` has at least `k ≥ 1` out-neighbours inside `K`
and `|K| ≤ 3k`, then degree-`k` CH gives a directed cycle of length at most three in the ambient graph.
This is the generic "PaidCarrier" consumer at the triangle cutoff, stated with `Finset` degrees.
-/

namespace Compose.BankPays

open CH

theorem ceilDiv_le_three {m k : Nat} (hk : 0 < k) (hm : m ≤ 3 * k) : CH.ceilDiv m k ≤ 3 := by
  unfold CH.ceilDiv
  have h : m + k - 1 < (3 + 1) * k := by rw [Nat.add_mul, Nat.one_mul]; omega
  have := (Nat.div_lt_iff_lt_mul hk).mpr h
  omega

theorem bank_pays
    {G : CH.Digraph} {n k : Nat} {K : Finset Nat}
    (hsub : K ⊆ Finset.range n) (hne : 0 < K.card) (hk : 0 < k) (hsize : K.card ≤ 3 * k)
    (loopless : CH.Loopless G n)
    (hdeg : ∀ x ∈ K, k ≤ (K.filter (fun w => G x w = true)).card)
    (ih : CH.Research.FixedDegreeCH k) :
    CH.HasDirectedCycleAtMost G n 3 := by
  classical
  obtain ⟨e, eBounded, eInj, eMem, eSurj⟩ := CH.Side.sc_finset_enumeration hsub
  set m := K.card with hm
  let H : CH.Digraph := fun a b => if a < m then (if b < m then G (e a) (e b) else false) else false
  have hloop : CH.Loopless H m := by
    intro v hv
    show (if v < m then (if v < m then G (e v) (e v) else false) else false) = false
    rw [if_pos hv, if_pos hv]
    exact loopless (e v) (eBounded v hv)
  have hmin : CH.MinOutdegreeAtLeast H m k := by
    intro a ha
    let T : Finset Nat := (Finset.range m).filter (fun i => G (e a) (e i) = true)
    have himage : T.image e = K.filter (fun w => G (e a) w = true) := by
      ext w
      simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨i, ⟨hi, hG⟩, rfl⟩
        exact ⟨eMem i hi, hG⟩
      · rintro ⟨hwK, hG⟩
        obtain ⟨i, hi, rfl⟩ := eSurj w hwK
        exact ⟨i, ⟨hi, hG⟩, rfl⟩
    have hinj : Set.InjOn e T := by
      intro i hi j hj hij
      simp only [T, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi hj
      exact eInj i j hi.1 hj.1 hij
    have hTcard : k ≤ T.card := by
      have := Finset.card_image_of_injOn hinj
      rw [himage] at this
      rw [← this]
      exact hdeg (e a) (eMem a ha)
    refine ⟨(T.sort (· ≤ ·)).take k, ?_, ?_, ?_⟩
    · rw [List.length_take, Finset.length_sort]; omega
    · exact (Finset.sort_nodup _ _).sublist (List.take_sublist _ _)
    · intro w hw
      have hwT : w ∈ T := (Finset.mem_sort _).mp ((List.take_sublist _ _).subset hw)
      simp only [T, Finset.mem_filter, Finset.mem_range] at hwT
      refine ⟨hwT.1, ?_⟩
      show (if a < m then (if w < m then G (e a) (e w) else false) else false) = true
      rw [if_pos ha, if_pos hwT.1]
      exact hwT.2
  obtain ⟨vs, cyc, len⟩ := ih m H hne hk hloop hmin
  exact CH.Side.sc_induced_subgraph_transport eBounded eInj
    ⟨vs, cyc, len.trans (ceilDiv_le_three hk hsize)⟩

end Compose.BankPays
