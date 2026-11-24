import checkpoints.shen_extension.PhysicalCycleStockReplay

namespace LeanCH.BR.PhysicalCycleStock
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking

/-- Two full cyclic layers give strong stock on every physical first-layer
row. The selected cycle's exterior is exactly the actual second layer. -/
theorem full_cyclic_layers {D V q r u} (free : QFree D V q) (hq : 4 ≤ q)
    (hr : 3 ≤ r) (room : r-1 ≤ 2*q) (reg : OutEq r D V) (hu : u ∈ V)
    (second : (N2 D V u).card = r) (third : (N3 D V u).card ≤ r-1)
    (firstRooted : ∀ x ∈ outN D V u, Rooted D V x (outN D V u))
    (secondRooted : ∀ y ∈ N2 D V u, Rooted D V y (N2 D V u)) :
    (N3 D V u).card = r-1 ∧ exterior D V (outN D V u) = N2 D V u ∧
      ∀ x ∈ outN D V u, 3*r+2 ≤ (ball D V x 3).card := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  let E := exterior D V Z
  have xv : X ⊆ V := outN_subset
  have yv : Y ⊆ V := fun _ h => N2_subV h
  have zv : Z ⊆ V := fun _ h => N3_subV h
  have xy : Disjoint X Y := disjXY
  have yz : Disjoint Y Z := disjoint_left.mpr (fun _ hm hn => (mem_N3.mp hn).2 (mem_N2.mp hm).1)
  have xz : Disjoint X Z := disjoint_left.mpr
    (fun _ hm hn => (mem_N3.mp hn).2 (ball_mono_radius (by decide : 1≤2) (X_B1 hm)))
  have xcard : X.card=r := reg u hu
  have ycard : Y.card=r := second
  have zcap : Z.card≤r-1 := third
  have paidX x (hx : x∈X) : (outN D Y x).card=r-1 := by
    have deg := reg x (xv hx)
    rw [outN_X_eq (free.mono_bound hq) hu hx, card_outN_union xy,
      (firstRooted x hx).one x hx] at deg
    omega
  have pred y (hy : y∈Y) : ∃ p∈Y, D p y = true := by
    have cap : 0 < (Y.erase y).card := by rw [card_erase_of_mem hy]; omega
    obtain ⟨b, hb⟩ := card_pos.mp cap
    obtain ⟨n, road⟩ := (secondRooted b (mem_of_mem_erase hb)).reaches y hy
    have positive : 0<n := by
      by_contra! zero
      obtain rfl : n=0 := by omega
      cases road
      exact (mem_erase.mp hb).1 rfl
    have shifted : Walk D Y b y (n-1+1) := by
      rw [Nat.sub_add_cancel (by omega : 1≤n)]
      exact road
    obtain ⟨p, wp, _, py⟩ := shifted.unsnoc
    have py' : p∈Y := by
      rcases wp.end_mem_or with eq | pm
      · exact eq.symm ▸ mem_of_mem_erase hb
      · exact pm
    exact ⟨p, py', py⟩
  have blocked y (hy : y ∈ Y) x (hx : x ∈ X) : D y x ≠ true := by
    intro yx
    let R : CH.Digraph := fun a b => D b a
    let B := ball R Y y (q-2)
    have minR a (ha : a∈Y) : 1 ≤ (outN R Y a).card := by
      obtain ⟨p, hp, edge⟩ := pred a ha
      exact card_pos.mpr ⟨p, mem_outN.mpr ⟨hp, edge⟩⟩
    have count := ball_one_growth (free.reverse.mono_set yv) minR hy (q-2) (by omega)
    change (q-2)+1 ≤ B.card at count
    have notB : Disjoint (outN D Y x) B := by
      refine disjoint_left.mpr (fun a xa hit => ?_)
      obtain ⟨_, n, fit, road⟩ := mem_ball.mp hit
      have back := (road.reverse_of_mem hy).mono yv
      exact free x _ (by omega) (by omega)
        (.step (yv (outN_subset xa)) (mem_outN.mp xa).2 (back.snoc (xv hx) yx))
    have sum := card_le_card (union_subset (outN_subset : outN D Y x ⊆ Y) (ball_subset : B ⊆ Y))
    rw [card_union_of_disjoint notB, paidX x hx, ycard] at sum
    omega
  have yfull y (hy : y∈Y) : outN D Z y = Z ∧ Z.card=r-1 := by
    have inc : outN D V y ⊆ outN D (Y ∪ Z) y := by
      intro z hz
      obtain ⟨zv', yz'⟩ := mem_outN.mp hz
      refine mem_outN.mpr ⟨?_, yz'⟩
      rcases headY (free.mono_bound hq) hu hy zv' yz' with old | new
      · rcases mem_union.mp old with xx | yy
        · exact (blocked y hy z xx yz').elim
        · exact mem_union_left _ yy
      · exact mem_union_right _ new
    have bill := card_le_card inc
    rw [reg y (yv hy), card_outN_union yz, (secondRooted y hy).one y hy] at bill
    have cap : (outN D Z y).card≤Z.card := card_le_card outN_subset
    exact ⟨eq_of_subset_of_card_le outN_subset (by omega), by omega⟩
  obtain ⟨y₀, hy₀⟩ := card_pos.mp (by omega : 0<Y.card)
  have zcard := (yfull y₀ hy₀).2
  have hitY x (hx : x∈X) : Y ⊆ ball D V x 2 := by
    intro y hy
    by_cases arc : D x y = true
    · exact ball_mono_radius (by decide : 1 ≤ 2) (ball_of_adj (yv hy) arc)
    have row : outN D Y x = Y.erase y :=
      eq_of_subset_of_card_le (fun _ hw => mem_erase.mpr
        ⟨fun e => arc (e ▸ (mem_outN.mp hw).2), outN_subset hw⟩)
        (by rw [card_erase_of_mem hy, ycard, paidX x hx])
    obtain ⟨a, ha, ay⟩ := pred y hy
    have ne : a ≠ y := fun e => loopfree free (by omega) (yv hy) (e ▸ ay)
    have xh : a ∈ outN D Y x := row.symm ▸ mem_erase.mpr ⟨ne, ha⟩
    exact ball_step (ball_of_adj (yv ha) (mem_outN.mp xh).2) (yv hy) ay
  have hitZ x (hx : x∈X) : Z ⊆ ball D V x 2 := by
    obtain ⟨a, ha⟩ := card_pos.mp (show 0 < (outN D Y x).card by rw [paidX x hx]; omega)
    intro z hz
    have az : z ∈ outN D Z a := (yfull a (outN_subset ha)).1.symm ▸ hz
    exact ball_step (ball_of_adj (yv (outN_subset ha)) (mem_outN.mp ha).2) (zv hz) (mem_outN.mp az).2
  have exY : Disjoint Y E := by
    refine disjoint_left.mpr (fun y hy he => ?_)
    obtain ⟨z, hz, zy⟩ := mem_biUnion.mp (mem_sdiff.mp he).1
    have head : z ∈ outN D Z y := (yfull y hy).1.symm ▸ hz
    exact digonfree free (by omega) (yv hy) (zv hz) (mem_outN.mp head).2 (mem_outN.mp zy).2
  have exX : Disjoint X E := by
    refine disjoint_left.mpr (fun x hx he => ?_)
    obtain ⟨z, hz, zx⟩ := mem_biUnion.mp (mem_sdiff.mp he).1
    obtain ⟨_, m, fit, road⟩ := mem_ball.mp (hitZ x hx hz)
    exact free x _ (by omega) (by omega) (road.snoc (xv hx) (mem_outN.mp zx).2)
  have exZ : Disjoint Z E := disjoint_left.mpr (fun _ hz he => (mem_sdiff.mp he).2 hz)
  have exSize : r-1 ≤ E.card := by
    by_contra! small
    have minZ z (hz : z∈Z) : 2 ≤ (outN D Z z).card := by
      have inc : outN D V z ⊆ outN D Z z ∪ E := by
        intro w hw
        by_cases inside : w∈Z
        · exact mem_union_left _ (mem_outN.mpr ⟨inside, (mem_outN.mp hw).2⟩)
        · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨z, hz, hw⟩, inside⟩)
      have bound := (card_le_card inc).trans (card_union_le _ _)
      rw [reg z (zv hz)] at bound
      omega
    have contradiction := corB (by omega : 1≤q) (free.mono_set zv) minZ (card_pos.mp (by omega))
    omega
  refine ⟨zcard, ShellCycleSupply.head_exterior free (by omega) hu, fun x hx => ?_⟩
  let H := ball D X x 3
  have hsize := ball_one_growth (free.mono_set xv)
    (fun a ha => ((firstRooted a ha).one a ha).ge) hx 3 (by omega)
  have pieces : H ∪ Y ∪ Z ∪ E ⊆ ball D V x 3 := by
    refine union_subset (union_subset (union_subset (ShellCycleSupply.lift_ball xv)
      (fun _ hy => ball_mono_radius (by decide : 2≤3) (hitY x hx hy)))
      (fun _ hz => ball_mono_radius (by decide : 2≤3) (hitZ x hx hz))) ?_
    intro z hz
    obtain ⟨a, ha, az⟩ := mem_biUnion.mp (mem_sdiff.mp hz).1
    exact ball_step (hitZ x hx ha) (outN_subset az) (mem_outN.mp az).2
  have bill := card_le_card pieces
  rw [card_union_of_disjoint (disjoint_union_left.mpr
        ⟨disjoint_union_left.mpr ⟨exX.mono_left ball_subset, exY⟩, exZ⟩),
    card_union_of_disjoint (disjoint_union_left.mpr ⟨xz.mono_left ball_subset, yz⟩),
    card_union_of_disjoint (xy.mono_left ball_subset)] at bill
  change H.card+Y.card+Z.card+E.card ≤ (ball D V x 3).card at bill
  change 4 ≤ H.card at hsize
  omega

#print axioms full_cyclic_layers
end LeanCH.BR.PhysicalCycleStock
