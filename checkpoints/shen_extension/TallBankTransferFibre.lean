import checkpoints.shen_extension.TallBankTransfer

namespace LeanCH.BR.TallBankTransfer

open Finset BRq2 BRq3

namespace SinkBank

/-- A full sink path leaves each of its labels at most one head inside
the parent's actual first layer. -/
theorem at_most_one_internal {D V u a r q} (bank : SinkBank D V u a r)
    (free : QFree D V q) (diag : r ≤ q) (reg : OutEq r D V)
    (hu : u ∈ V) {x : ℕ} (hx : x ∈ outN D V u) :
    (outN D (outN D V u) x).card ≤ 1 := by
  let X := outN D V u
  let p := bank.path
  have off : X ⊆ V := outN_subset
  have fit : X.card ≤ q := (reg u hu).le.trans diag
  have ix : x ∈ (range (p.len + 1)).image p.vertex := bank.support.symm ▸ hx
  obtain ⟨i,hi,rfl⟩ := mem_image.mp ix
  have ik : i ≤ p.len := by have := mem_range.mp hi; omega
  have cap : outN D X (p.vertex i) ⊆ {p.vertex (i + 1)} := by
    intro y hy
    obtain ⟨yx, e⟩ := mem_outN.mp hy
    have yv : y ∈ (range (p.len + 1)).image p.vertex :=
      bank.support.symm ▸ (show y ∈ outN D V u from yx)
    obtain ⟨j,hj,rfl⟩ := mem_image.mp yv
    have jk : j ≤ p.len := by have := mem_range.mp hj; omega
    exact mem_singleton.mpr (congrArg p.vertex (p.no_chord (free.mono_set off) fit ik jk e))
  exact (card_le_card cap).trans_eq (card_singleton _)

theorem second_layer_heads {D V u a r q} (bank : SinkBank D V u a r)
    (free : QFree D V q) (diag : r ≤ q) (room : 2 ≤ r)
    (reg : OutEq r D V) (hu : u ∈ V) {x : ℕ} (hx : x ∈ outN D V u) :
    r - 1 ≤ (outN D (ball D V u 2 \ ball D V u 1) x).card := by
  let X := outN D V u
  let Y := ball D V u 2 \ ball D V u 1
  have x1 := (mem_ball_one hu).mpr (Or.inr hx)
  have arc : outN D V x = outN D X x ∪ outN D Y x := by
    ext z
    constructor
    · intro hz
      obtain ⟨zv,xz⟩ := mem_outN.mp hz
      have z2 := ball_step x1 zv xz
      by_cases z1 : z ∈ ball D V u 1
      · rcases (mem_ball_one hu).mp z1 with rfl | hh
        · exact (no_back_arc free hu x1 (by omega : 1+1≤q) xz).elim
        · exact mem_union_left _ (mem_outN.mpr ⟨hh, xz⟩)
      · exact mem_union_right _ (mem_outN.mpr ⟨mem_sdiff.mpr ⟨z2,z1⟩, xz⟩)
    · intro hz
      rcases mem_union.mp hz with hh | hh
      · exact mem_outN.mpr ⟨outN_subset (mem_outN.mp hh).1, (mem_outN.mp hh).2⟩
      · exact mem_outN.mpr ⟨ball_subset (mem_sdiff.mp (mem_outN.mp hh).1).1, (mem_outN.mp hh).2⟩
  have cap := card_union_le (outN D X x) (outN D Y x)
  rw [← arc, reg x (outN_subset hx)] at cap
  have one := bank.at_most_one_internal free diag reg hu hx
  change (outN D X x).card ≤ 1 at one
  change r - 1 ≤ (outN D Y x).card
  omega

/-- Consecutive labels on a full first-layer path have many common heads
in the very same second layer. -/
theorem consecutive_overlap {D V u a r q} (bank : SinkBank D V u a r)
    (free : QFree D V q) (diag : r ≤ q) (room : 2 ≤ r)
    (reg : OutEq r D V) (hu : u ∈ V)
    (size : (ball D V u 2 \ ball D V u 1).card = r + 1)
    {i : ℕ} (hi : i < bank.path.len) :
    r - 3 ≤ (outN D (outN D V (bank.path.vertex i)) (bank.path.vertex (i + 1))).card := by
  let Y := ball D V u 2 \ ball D V u 1
  let x := bank.path.vertex i
  let y := bank.path.vertex (i + 1)
  let A := outN D Y x
  let B := outN D Y y
  have yv : Y ⊆ V := sdiff_subset.trans ball_subset
  have cx : r - 1 ≤ A.card :=
    bank.second_layer_heads free diag room reg hu (bank.path.mem i (by omega))
  have cy : r - 1 ≤ B.card :=
    bank.second_layer_heads free diag room reg hu (bank.path.mem (i + 1) (by omega))
  have count := card_union_add_card_inter A B
  have cap : (A ∪ B).card ≤ Y.card := card_le_card (union_subset outN_subset outN_subset)
  have sz : Y.card = r + 1 := size
  have inc : A ∩ B ⊆ outN D (outN D V x) y := by
    intro z hz
    obtain ⟨az,bz⟩ := mem_inter.mp hz
    have ah := mem_outN.mp az
    exact mem_outN.mpr ⟨mem_outN.mpr ⟨yv ah.1,ah.2⟩,(mem_outN.mp bz).2⟩
  have enough := card_le_card inc
  change r - 3 ≤ (outN D (outN D V x) y).card
  omega

/-- All physical second-, third- and fourth-layer labels transfer to the
child at radius three. -/
theorem transfer_four {D V u a r} (bank : SinkBank D V u a r)
    (hu : u ∈ V) :
    ball D V u 4 \ ball D V u 1 ⊆ ball D V a 3 := by
  have small : ball D V u 3 \ ball D V u 1 ⊆ ball D V a 2 := by
    intro z hz
    obtain ⟨z3,z1⟩ := mem_sdiff.mp hz
    rw [bank.child_ball]
    apply mem_insert_of_mem
    apply mem_insert_of_mem
    by_cases z2 : z ∈ ball D V u 2
    · exact mem_union_left _ (mem_sdiff.mpr ⟨z2,z1⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨z3,z2⟩)
  intro z hz
  obtain ⟨z4,z1⟩ := mem_sdiff.mp hz
  by_cases z3 : z ∈ ball D V u 3
  · exact ball_mono_radius (by decide : 2 ≤ 3) (small (mem_sdiff.mpr ⟨z3,z1⟩))
  · obtain ⟨p,p3,pz⟩ := ball_succ_pred hu z4 z3
    have p1 : p ∉ ball D V u 1 := fun h => z3
      (ball_mono_radius (by decide : 2 ≤ 3) (ball_step h (ball_subset z4) pz))
    exact ball_step (small (mem_sdiff.mpr ⟨p3,p1⟩)) (ball_subset z4) pz

/-- The start is a literal second-layer label of the child and uses all
but at most two of its available first-layer slots in the child's bank. -/
theorem start_heads {D V u a r q} (bank : SinkBank D V u a r)
    (free : QFree D V q) (diag : r ≤ q) (room : 2 ≤ r)
    (reg : OutEq r D V) (hu : u ∈ V)
    (size : (ball D V u 2 \ ball D V u 1).card = r + 1) :
    bank.start ∈ ball D V a 2 \ ball D V a 1 ∧
    r - 2 ≤ (outN D (outN D V a) bank.start).card := by
  let X := outN D V u
  let Y := ball D V u 2 \ ball D V u 1
  let P := outN D V a
  let p := bank.path
  have length : p.len + 1 = r := bank.length
  have hlast : p.vertex p.len = a := bank.last
  have hx : bank.start ∈ X := p.start ▸ p.mem 0 (Nat.zero_le _)
  have ax : a ∈ X := hlast ▸ p.mem _ le_rfl
  have xv : X ⊆ V := outN_subset
  have av := xv ax
  have b1 (x) (hx : x ∈ X) : x ∈ ball D V u 1 := (mem_ball_one hu).mpr (Or.inr hx)
  have pin : P ⊆ Y := by
    intro z hz
    obtain ⟨zv, az⟩ := mem_outN.mp hz
    refine mem_sdiff.mpr ⟨ball_step (b1 a ax) zv az, ?_⟩
    intro h
    rcases (mem_ball_one hu).mp h with rfl | zx
    · exact no_back_arc free hu (b1 a ax) (by omega : 1 + 1 ≤ q) az
    · exact p.sink z zx (hlast.symm ▸ az)
  have xa : bank.start ≠ a := by
    intro eq
    have vEq := p.start.trans (eq.trans hlast.symm)
    have ni := p.injective (free.mono_set xv) ((reg u hu).le.trans diag)
    have zero := ni (mem_range.mpr (by omega : 0 < p.len + 1))
      (mem_range.mpr (by omega : p.len < p.len + 1)) vEq
    omega
  have start : bank.start ∈ ball D V a 2 \ ball D V a 1 := by
    refine mem_sdiff.mpr ⟨by rw [bank.child_ball]; exact mem_insert_of_mem (mem_insert_self _ _), ?_⟩
    intro h
    rcases (mem_ball_one av).mp h with same | hp
    · exact xa same
    · exact (mem_sdiff.mp (pin hp)).2 (b1 _ hx)
  have rest : outN D V bank.start \ P ⊆ insert (p.vertex 1) (Y \ P) := by
    intro z hz
    obtain ⟨head, off⟩ := mem_sdiff.mp hz
    obtain ⟨zv, xz⟩ := mem_outN.mp head
    have z2 := ball_step (b1 _ hx) zv xz
    by_cases z1 : z ∈ ball D V u 1
    · rcases (mem_ball_one hu).mp z1 with rfl | zx
      · exact (no_back_arc free hu (b1 _ hx) (by omega : 1 + 1 ≤ q) xz).elim
      · have zm : z ∈ (range (p.len + 1)).image p.vertex := bank.support.symm ▸ (show z ∈ outN D V u from zx)
        obtain ⟨j, hj, rfl⟩ := mem_image.mp zm
        have jl : j ≤ p.len := by have := mem_range.mp hj; omega
        have h := p.no_chord (free.mono_set xv) ((reg u hu).le.trans diag) (Nat.zero_le _) jl
          (p.start.symm ▸ xz)
        exact mem_insert.mpr (Or.inl (congrArg p.vertex h))
    · exact mem_insert_of_mem (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨z2,z1⟩,off⟩)
  have roomP := card_sdiff_add_card_eq_card pin
  have pc : P.card = r := reg a av
  have yc : Y.card = r + 1 := size
  have cap := (card_le_card rest).trans (card_insert_le _ _)
  have total := card_sdiff_add_card_inter (outN D V bank.start) P
  have head : outN D V bank.start ∩ P = outN D P bank.start := by
    ext z
    simp only [mem_inter,mem_outN]
    exact ⟨fun ⟨a,b⟩ => ⟨b,a.2⟩, fun ⟨b,e⟩ => ⟨⟨outN_subset b,e⟩,b⟩⟩
  rw [head,reg _ (xv hx)] at total
  exact ⟨start, by change r - 2 ≤ (outN D P bank.start).card; omega⟩

/-- At a common tall child, the two physical first-layer path banks must
coincide. The cardinal hypotheses give at least two shared entry heads
inside the child's actual first layer. -/
theorem same_heads {D V u v a r q} (one : SinkBank D V u a r) (two : SinkBank D V v a r)
    (free : QFree D V q) (diag : r ≤ q) (room : 6 ≤ r) (reg : OutEq r D V)
    (hu : u ∈ V) (hv : v ∈ V)
    (sizeU : (ball D V u 2 \ ball D V u 1).card = r + 1)
    (sizeV : (ball D V v 2 \ ball D V v 1).card = r + 1)
    (sizeA : (ball D V a 2 \ ball D V a 1).card = r + 1) :
    outN D V u = outN D V v := by
  let P := outN D V a
  have av : a ∈ V := outN_subset (one.last ▸ one.path.mem _ le_rfl)
  have pc : P.card = r := reg a av
  obtain ⟨sq, hd⟩ := one.start_heads free diag (by omega) reg hu sizeU
  obtain ⟨tq, he⟩ := two.start_heads free diag (by omega) reg hv sizeV
  let A := outN D P one.start
  let B := outN D P two.start
  have union := card_le_card (union_subset (outN_subset : A ⊆ P) (outN_subset : B ⊆ P))
  have budget := card_union_add_card_inter A B
  change (A ∪ B).card ≤ P.card at union
  change r - 2 ≤ A.card at hd
  change r - 2 ≤ B.card at he
  have common : 2 ≤ (A ∩ B).card := by omega
  have first := unique_start_of_two_common_heads free (outN_subset : P ⊆ V)
    (by omega : P.card ≤ q)
    (fun s hs stop => sink_row_omission free (by omega) reg av hs stop sizeA) sq tq common
  have len : one.path.len = two.path.len := by
    have h := one.length
    have j := two.length
    omega
  have eqPath := same_path_of_unique_successor (D:=D) (V:=V) (E:=(ball D V a 2).erase a)
    (p:=one.path.vertex) (t:=two.path.vertex) (len:=one.path.len)
    (one.path.start.trans (first.trans two.path.start.symm))
    (fun i hi => (one.successor_outside free diag reg hu hi).symm ▸ mem_singleton_self _)
    (fun i hi => (two.successor_outside free diag reg hv (len ▸ hi)).symm ▸ mem_singleton_self _)
    (fun i hi => by rw [one.successor_outside free diag reg hu hi]; simp)
  rw [← one.support, ← two.support, ← len]
  apply image_congr
  intro i hi
  exact eqPath i (by have := mem_range.mp hi; omega)

end SinkBank

/-- The actual first layer determines the actual second layer at vertices
with the same outgoing row in a digon-free graph. -/
theorem same_second_of_same_heads {D V q u v}
    (free : QFree D V q) (fit : 2 ≤ q) (hu : u ∈ V) (hv : v ∈ V)
    (same : outN D V u = outN D V v) :
    ball D V u 2 \ ball D V u 1 = ball D V v 2 \ ball D V v 1 := by
  have step {a b : ℕ} (ha : a ∈ V) (hb : b ∈ V) (eq : outN D V a = outN D V b) :
      ball D V a 2 \ ball D V a 1 ⊆ ball D V b 2 \ ball D V b 1 := by
    intro z hz
    obtain ⟨z2, z1⟩ := mem_sdiff.mp hz
    obtain ⟨w,w1,wz⟩ := ball_succ_pred ha z2 z1
    have row : w ∈ outN D V a := by
      rcases (mem_ball_one ha).mp w1 with rfl | h
      · exact (z1 (ball_of_adj (ball_subset z2) wz)).elim
      · exact h
    have e : w ∈ outN D V b := eq ▸ row
    refine mem_sdiff.mpr ⟨ball_step (ball_of_adj (mem_outN.mp e).1 (mem_outN.mp e).2)
      (ball_subset z2) wz, ?_⟩
    intro done
    rcases (mem_ball_one hb).mp done with rfl | h
    · exact digonfree free fit hb (mem_outN.mp e).1 (mem_outN.mp e).2 wz
    · exact z1 ((mem_ball_one ha).mpr (Or.inr (eq.symm ▸ h)))
  exact Subset.antisymm (step hu hv same) (step hv hu same.symm)

#print axioms SinkBank.start_heads
#print axioms SinkBank.same_heads
#print axioms SinkBank.at_most_one_internal
#print axioms SinkBank.consecutive_overlap
#print axioms SinkBank.transfer_four
#print axioms same_second_of_same_heads
end LeanCH.BR.TallBankTransfer
