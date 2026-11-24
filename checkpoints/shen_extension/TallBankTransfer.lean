import LeanCH.BR.BRFiniteWalk
import LeanCH.BR.BRq3Util

namespace LeanCH.BR.TallBankTransfer

open Finset BRq2 BRq3

/-- The even-cutoff return only uses actual arcs, the actual child of each
root, and coverage in the specified root class. -/
theorem no_child_return {D : CH.Digraph} {V S : Finset ℕ} {q k : ℕ}
    (free : QFree D V q) (fit : k + k ≤ q)
    (child : ℕ → ℕ) (edge : ∀ u ∈ S, child u ∈ outN D V u)
    (cover : ∀ u ∈ S, ∀ w ∈ S, u ≠ w →
      w ∈ ball D V u k ∨ u ∈ ball D V w k)
    (gain : ∀ u ∈ S, ∀ w ∈ S, u ≠ w →
      w ∈ ball D V u k → w ∈ ball D V (child u) (k - 1))
    {u w : ℕ} (hu : u ∈ S) (hw : w ∈ S)
    (different : child u ≠ child w) (head : child w ∈ outN D V u) :
    child u ∉ ball D V (child w) k := by
  intro walk
  have une : u ≠ w := fun h => different (congrArg child h)
  have pos : 0 < k := by
    by_contra! h
    have zero : k = 0 := by omega
    rw [zero] at walk
    exact different (eq_of_mem_ball_zero walk)
  have forbid {a b : ℕ} (ab : b ∈ ball D V a k) (ba : a ∈ ball D V b k)
      (hne : a ≠ b) : False := by
    obtain ⟨_, i, hi, wi⟩ := mem_ball.mp ab
    obtain ⟨_, j, hj, wj⟩ := mem_ball.mp ba
    have nz : i ≠ 0 := fun h => hne (walk_zero (h ▸ wi))
    exact free a (i + j) (by omega) (by omega) (wi.append wj)
  rcases cover u hu w hw une with uw | wu
  · have cw1 := ball_of_adj (mem_outN.mp (edge w hw)).1 (mem_outN.mp (edge w hw)).2
    have fromChild := ball_trans (gain u hu w hw une uw) cw1
    exact forbid (ball_mono_radius (by omega : k - 1 + 1 ≤ k) fromChild) walk different
  · have cw := gain w hw u hu une.symm wu
    exact no_back_arc free (mem_outN.mp head).1 cw (by omega : (k - 1) + 1 ≤ q)
      (mem_outN.mp head).2

/-- With only one available successor outside the same exterior bank,
a prescribed start determines a path and all of its labels. -/
theorem same_path_of_unique_successor {D : CH.Digraph} {V E : Finset ℕ}
    {p t : ℕ → ℕ} {len : ℕ} (start : p 0 = t 0)
    (pstep : ∀ i < len, p (i + 1) ∈ outN D V (p i) \ E)
    (tstep : ∀ i < len, t (i + 1) ∈ outN D V (t i) \ E)
    (unique : ∀ i < len, (outN D V (p i) \ E).card ≤ 1) :
    ∀ i ≤ len, p i = t i := by
  intro i hi
  induction i with
  | zero => exact start
  | succ i ih =>
    have eq := ih (by omega)
    have other := tstep i (by omega)
    rw [← eq] at other
    exact card_le_one.mp (unique i (by omega)) _ (pstep i (by omega)) _ other

/-- Two large sets of entry heads cannot be confined to disjoint types of
reachable sink. The sink's literal omitted column fixes the start. -/
theorem unique_start_of_sink_omission {D : CH.Digraph} {V P Q : Finset ℕ}
    {q m : ℕ} (free : QFree D V q) (pv : P ⊆ V)
    (time : m + 2 ≤ q) (short : ∀ x ∈ P,
      ∃ s ∈ P, (∀ z ∈ P, D s z ≠ true) ∧ ∃ i ≤ m, Walk D P x s i)
    (omission : ∀ s ∈ P, (∀ z ∈ P, D s z ≠ true) →
      ∃ b ∈ Q, outN D V s = Q.erase b)
    {a b : ℕ} (ha : a ∈ Q) (hb : b ∈ Q)
    (overlap : P.card < (outN D P a).card + (outN D P b).card) :
    a = b := by
  classical
  by_contra ne
  have hit : (outN D P a ∩ outN D P b).Nonempty := by
    by_contra empty
    have dis : Disjoint (outN D P a) (outN D P b) :=
      disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp empty)
    have bound := card_le_card (union_subset
      (outN_subset : outN D P a ⊆ P) (outN_subset : outN D P b ⊆ P))
    rw [card_union_of_disjoint dis] at bound
    omega
  obtain ⟨x, hx⟩ := hit
  obtain ⟨ax, bx⟩ := mem_inter.mp hx
  obtain ⟨s, hs, stop, i, hi, route⟩ := short x (mem_outN.mp ax).1
  obtain ⟨o, _, row⟩ := omission s hs stop
  have identifies {u : ℕ} (uq : u ∈ Q) (ux : x ∈ outN D P u) : u = o := by
    by_contra h
    have su := mem_outN.mp (row.symm ▸ mem_erase.mpr ⟨h, uq⟩)
    have path := Walk.step (pv (mem_outN.mp ux).1) (mem_outN.mp ux).2 (route.mono pv)
    exact free u _ (by omega) (by omega) (path.snoc su.1 su.2)
  exact ne ((identifies ha ax).trans (identifies hb bx).symm)

/-- When a first layer has two sinks, a simple shortest path to any sink
leaves another actual sink off the path. -/
theorem sink_path_le_of_two_sinks {D : CH.Digraph} {P : Finset ℕ} {q : ℕ}
    (free : QFree D P q) (size : P.card ≤ q)
    {a b : ℕ} (ha : a ∈ P) (hb : b ∈ P) (ne : a ≠ b)
    (sa : ∀ z ∈ P, D a z ≠ true) (sb : ∀ z ∈ P, D b z ≠ true) {x : ℕ} (hx : x ∈ P) :
    ∃ s ∈ P, (∀ z ∈ P, D s z ≠ true) ∧
      ∃ i, i + 2 ≤ P.card ∧ Walk D P x s i := by
  classical
  obtain ⟨p⟩ := exists_shortest_sink_path free size hx
  let y := if p.vertex p.len = a then b else a
  have hy : y ∈ P := by dsimp [y]; split <;> assumption
  have last : y ≠ p.vertex p.len := by
    dsimp [y]
    split
    · next e => exact fun h => ne (e.symm.trans h.symm)
    · next e => exact Ne.symm e
  have sink : ∀ z ∈ P, D y z ≠ true := by
    dsimp [y]
    split <;> assumption
  let verts := (range (p.len + 1)).image p.vertex
  have miss : y ∉ verts := by
    intro ym
    obtain ⟨i, hi, eq⟩ := mem_image.mp ym
    have hi' := mem_range.mp hi
    have inner : i < p.len := by
      by_contra! h
      exact last (eq.symm.trans (congrArg p.vertex (show i = p.len by omega)))
    exact sink _ (p.mem (i + 1) (by omega)) (eq ▸ p.edge i inner)
  have sub : insert y verts ⊆ P := by
    refine insert_subset hy ?_
    intro z hz
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
    exact p.mem i (by have := mem_range.mp hi; omega)
  have count := card_le_card sub
  rw [card_insert_of_notMem miss, card_image_of_injOn (p.injective free size), card_range] at count
  exact ⟨_, p.mem _ le_rfl, p.sink, p.len, by omega,
    by simpa only [p.start, Nat.sub_zero] using p.walk (Nat.zero_le _) le_rfl⟩

/-- Among any two distinct labels in an acyclic bank, one reaches a sink
without using all labels of the bank. -/
theorem short_sink_from_two_entries {D : CH.Digraph} {P : Finset ℕ} {q : ℕ}
    (free : QFree D P q) (size : P.card ≤ q)
    {x y : ℕ} (hx : x ∈ P) (hy : y ∈ P) (ne : x ≠ y) :
    ∃ z ∈ ({x,y} : Finset ℕ), ∃ s ∈ P,
      (∀ t ∈ P, D s t ≠ true) ∧ ∃ i, i + 2 ≤ P.card ∧ Walk D P z s i := by
  classical
  obtain ⟨p⟩ := exists_shortest_sink_path free size hx
  have small := p.bounded
  by_cases h : p.len + 2 ≤ P.card
  · exact ⟨x, mem_insert_self _ _, _, p.mem _ le_rfl, p.sink, p.len, h,
      by simpa only [p.start, Nat.sub_zero] using p.walk (Nat.zero_le _) le_rfl⟩
  · have whole : (range (p.len + 1)).image p.vertex = P := by
      apply eq_of_subset_of_card_le
      · intro z hz
        obtain ⟨j, hj, rfl⟩ := mem_image.mp hz
        exact p.mem j (by have := mem_range.mp hj; omega)
      · rw [card_image_of_injOn (p.injective free size), card_range]
        omega
    obtain ⟨j, hj, jy⟩ := mem_image.mp (whole.symm ▸ hy)
    have jb := mem_range.mp hj
    have jp : 0 < j := by
      by_contra! h0
      exact ne (p.start.symm.trans (by simpa [show j = 0 by omega] using jy))
    refine ⟨y, mem_insert_of_mem (mem_singleton_self _), _, p.mem _ le_rfl, p.sink,
      p.len - j, by omega, ?_⟩
    exact jy ▸ p.walk (by omega : j ≤ p.len) le_rfl

/-- Two starts with at least two common actual bank heads cannot require
different omissions, even when the bank has just one sink. -/
theorem unique_start_of_two_common_heads {D : CH.Digraph} {V P Q : Finset ℕ}
    {q : ℕ} (free : QFree D V q) (sub : P ⊆ V) (size : P.card ≤ q)
    (omission : ∀ s ∈ P, (∀ z ∈ P, D s z ≠ true) →
      ∃ b ∈ Q, outN D V s = Q.erase b)
    {a b : ℕ} (ha : a ∈ Q) (hb : b ∈ Q)
    (overlap : 2 ≤ (outN D P a ∩ outN D P b).card) : a = b := by
  obtain ⟨x, hx⟩ := card_pos.mp (show 0 < (outN D P a ∩ outN D P b).card by omega)
  obtain ⟨y, hy⟩ := card_pos.mp (show 0 < ((outN D P a ∩ outN D P b).erase x).card by
    rw [card_erase_of_mem hx]; omega)
  have ym := mem_erase.mp hy
  have xv := (mem_outN.mp (mem_inter.mp hx).1).1
  have yv := (mem_outN.mp (mem_inter.mp ym.2).1).1
  obtain ⟨z, hz, s, hs, stop, i, hi, path⟩ :=
    short_sink_from_two_entries (free.mono_set sub) size xv yv ym.1.symm
  have zh : z ∈ outN D P a ∩ outN D P b := by
    rcases mem_insert.mp hz with rfl | e
    · exact hx
    · rw [mem_singleton.mp e]
      exact ym.2
  obtain ⟨o, _, row⟩ := omission s hs stop
  have identifies {u : ℕ} (uq : u ∈ Q) (uz : z ∈ outN D P u) : u = o := by
    by_contra h
    have su := mem_outN.mp (row.symm ▸ mem_erase.mpr ⟨h, uq⟩)
    have route := Walk.step (sub (mem_outN.mp uz).1) (mem_outN.mp uz).2 (path.mono sub)
    exact free u _ (by omega) (by omega) (route.snoc su.1 su.2)
  exact (identifies ha (mem_inter.mp zh).1).trans (identifies hb (mem_inter.mp zh).2).symm

/-- Every reach past the first layer has an actual first entry at the second
layer, with the remaining radius reduced by two. -/
theorem from_second_layer {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hu : u ∈ V) (extra : ℕ) {v : ℕ}
    (reach : v ∈ ball D V u (extra + 2)) (outside : v ∉ ball D V u 1) :
    ∃ y ∈ ball D V u 2 \ ball D V u 1, v ∈ ball D V y extra := by
  induction extra generalizing v with
  | zero =>
    exact ⟨v, mem_sdiff.mpr ⟨reach, outside⟩, self_mem_ball (ball_subset reach)⟩
  | succ t ih =>
    rw [show t + 1 + 2 = (t + 2) + 1 by omega] at reach
    by_cases old : v ∈ ball D V u (t + 2)
    · obtain ⟨y, hy, vr⟩ := ih old outside
      exact ⟨y, hy, ball_mono_radius (by omega) vr⟩
    · obtain ⟨z, hz, zv⟩ := ball_succ_pred hu reach old
      have zOut : z ∉ ball D V u 1 := fun h =>
        old (ball_mono_radius (by omega : 2 ≤ t + 2) (ball_step h (ball_subset reach) zv))
      obtain ⟨y, hy, zr⟩ := ih hz zOut
      exact ⟨y, hy, ball_step zr (ball_subset reach) zv⟩

/-- Two distinct exact-degree rows with identical physical second layers
have a missing pair at any radius between two and the cutoff. -/
theorem same_second_layer_incomparable {D : CH.Digraph} {V : Finset ℕ} {r q k : ℕ}
    (free : QFree D V q) (reg : OutEq r D V) (lo : 2 ≤ k) (fit : k ≤ q)
    {u v : ℕ} (hu : u ∈ V) (hv : v ∈ V) (ne : u ≠ v)
    (same : ball D V u 2 \ ball D V u 1 = ball D V v 2 \ ball D V v 1) :
    v ∉ ball D V u k ∧ u ∉ ball D V v k := by
  have avoid {a b : ℕ} (ha : a ∈ V) (hb : b ∈ V) (ab : a ≠ b)
      (eq : ball D V a 2 \ ball D V a 1 = ball D V b 2 \ ball D V b 1) :
      b ∉ ball D V a k := by
    intro rb
    by_cases h : b ∈ ball D V a 1
    · have bx : b ∈ outN D V a := ((mem_ball_one ha).mp h).resolve_left (Ne.symm ab)
      have inc : outN D V b ⊆ outN D V a := by
        intro z hz
        obtain ⟨zv, bz⟩ := mem_outN.mp hz
        have z2 : z ∈ ball D V a 2 := ball_step h zv bz
        have z1 : z ∈ ball D V a 1 := by
          by_contra oz
          have zY := mem_sdiff.mp (eq ▸ mem_sdiff.mpr ⟨z2, oz⟩)
          exact zY.2 ((mem_ball_one hb).mpr (Or.inr hz))
        rcases (mem_ball_one ha).mp z1 with rfl | yes
        · exact (no_back_arc free ha h (by omega : 1 + 1 ≤ q) bz).elim
        · exact yes
      have eqOut := eq_of_subset_of_card_le inc (by rw [reg _ ha, reg _ hb])
      exact loopfree free (by omega) hb (mem_outN.mp (eqOut.symm ▸ bx)).2
    · have rb' : b ∈ ball D V a (k - 2 + 2) := by rwa [Nat.sub_add_cancel lo]
      obtain ⟨y, hy, yr⟩ := from_second_layer ha (k - 2) rb' h
      have hy' : y ∈ ball D V b 2 \ ball D V b 1 := eq ▸ hy
      obtain ⟨_, i, hi, wi⟩ := mem_ball.mp (mem_sdiff.mp hy').1
      obtain ⟨_, j, hj, wj⟩ := mem_ball.mp yr
      have nz : 0 < i := by
        by_contra! h0
        have iz : i = 0 := by omega
        have yz := walk_zero (iz ▸ wi)
        exact (mem_sdiff.mp hy').2 (yz ▸ self_mem_ball hb)
      exact free b _ (by omega) (by omega) (wi.append wj)
  exact ⟨avoid hu hv ne same, avoid hv hu ne.symm same.symm⟩

/-- A full first-layer path and the physical second-layer omission exposed
by a unique sink whose two-ball cannot fit into the exterior layers. -/
theorem unique_sink_geometry {D : CH.Digraph} {V : Finset ℕ} {r q u a : ℕ}
    (free : QFree D V q) (diag : r ≤ q) (room : 4 ≤ r)
    (reg : OutEq r D V) (hu : u ∈ V) (ha : a ∈ outN D V u)
    (sink : ∀ z ∈ outN D V u, D a z ≠ true)
    (unique : ∀ z ∈ outN D V u, (∀ x ∈ outN D V u, D z x ≠ true) → z = a)
    (two : (ball D V u 2).card = 2 * r + 2)
    (third : (ball D V u 3 \ ball D V u 2).card < r)
    (strong : 2 * r + 2 ≤ (ball D V a 2).card) :
    let X := outN D V u
    let Y := ball D V u 2 \ ball D V u 1
    let Z := ball D V u 3 \ ball D V u 2
    q = r ∧ ∃ x ∈ X, ∃ p : ShortestSinkPath D X x,
      p.len + 1 = r ∧ p.vertex p.len = a ∧
      (range (p.len + 1)).image p.vertex = X ∧
      ball D V a 2 = insert a (insert x (Y ∪ Z)) := by
  classical
  let X := outN D V u
  let Y := ball D V u 2 \ ball D V u 1
  let Z := ball D V u 3 \ ball D V u 2
  let P := outN D V a
  have xv : X ⊆ V := outN_subset
  have av := xv ha
  have a1 := (mem_ball_one hu).mpr (Or.inr ha)
  have yv : Y ⊆ V := sdiff_subset.trans ball_subset
  have nx : X.card = r := reg u hu
  have b1 : (ball D V u 1).card = r + 1 := by
    have h : ball D V u 1 = insert u X := by
      ext b
      exact (mem_ball_one hu).trans mem_insert.symm
    rw [h, card_insert_of_notMem, nx]
    exact fun hx => loopfree free (by omega) hu (mem_outN.mp hx).2
  have ny : Y.card = r + 1 := by
    have part := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1 ≤ 2))
    change Y.card + (ball D V u 1).card = (ball D V u 2).card at part
    omega
  have contained : P ⊆ Y := by
    intro z hz
    obtain ⟨zv, az⟩ := mem_outN.mp hz
    refine mem_sdiff.mpr ⟨ball_step a1 zv az, ?_⟩
    intro z1
    rcases (mem_ball_one hu).mp z1 with rfl | zx
    · exact no_back_arc free hu a1 (by omega : 1 + 1 ≤ q) az
    · exact sink z zx az
  have heads {b z : ℕ} (hb : b ∈ P) (hz : z ∈ V) (e : D b z = true) : z ∈ X ∪ Y ∪ Z := by
    have b2 := (mem_sdiff.mp (contained hb)).1
    have z3 := ball_step b2 hz e
    by_cases z2 : z ∈ ball D V u 2
    · apply mem_union_left
      by_cases z1 : z ∈ ball D V u 1
      · rcases (mem_ball_one hu).mp z1 with rfl | zx
        · exact (no_back_arc free hu b2 (by omega : 2 + 1 ≤ q) e).elim
        · exact mem_union_left _ zx
      · exact mem_union_right _ (mem_sdiff.mpr ⟨z2, z1⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨z3, z2⟩)
  have span {x : ℕ} (return_to : ∀ b ∈ P, ∀ v ∈ X, D b v = true → v = x) :
      ball D V a 2 ⊆ insert a (insert x (Y ∪ Z)) := by
    intro v hv
    by_cases va : v = a
    · exact mem_insert.mpr (Or.inl va)
    obtain ⟨b, hb, bv⟩ := exists_pred av hv va
    rcases (mem_ball_one av).mp hb with rfl | bp
    · exact mem_insert_of_mem (mem_insert_of_mem
        (mem_union_left _ (contained (mem_outN.mpr ⟨ball_subset hv, bv⟩))))
    rcases mem_union.mp (heads bp (ball_subset hv) bv) with xy | hz
    · rcases mem_union.mp xy with hx | hy
      · exact mem_insert_of_mem (mem_insert.mpr (Or.inl (return_to b bp v hx bv)))
      · exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ hy))
    · exact mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ hz))
  obtain ⟨x, hx, b, hb, bx⟩ : ∃ x ∈ X, ∃ b ∈ P, D b x = true := by
    by_contra h
    have inc := span (x:=a) (fun b hb z hz e => (h ⟨z, hz, b, hb, e⟩).elim)
    rw [insert_idem] at inc
    have cards := (card_le_card inc).trans
      ((card_insert_le _ _).trans (Nat.succ_le_succ (card_union_le _ _)))
    change Z.card < r at third
    omega
  obtain ⟨p⟩ := exists_shortest_sink_path (free.mono_set xv) (by omega) hx
  have last := unique _ (p.mem _ le_rfl) p.sink
  have long {v b : ℕ} (bv : b ∈ P) (vx : v ∈ X) (arc : D b v = true)
      {m : ℕ} (path : Walk D X v a m) : q ≤ m + 1 := by
    by_contra! h
    exact free v _ (by omega) (by omega)
      (((path.mono xv).snoc (yv (contained bv)) (mem_outN.mp bv).2).snoc (xv vx) arc)
  have len : p.len + 1 = r := by
    have path := p.walk (Nat.zero_le p.len) le_rfl
    rw [p.start, last, Nat.sub_zero] at path
    have bound := long hb hx bx path
    have upper := p.bounded
    omega
  have qe : q = r := by
    have path := p.walk (Nat.zero_le p.len) le_rfl
    rw [p.start, last, Nat.sub_zero] at path
    have bound := long hb hx bx path
    omega
  have full : (range (p.len + 1)).image p.vertex = X := by
    apply eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
      exact p.mem i (by have := mem_range.mp hi; omega)
    · rw [card_image_of_injOn (p.injective (free.mono_set xv) (by omega)), card_range, nx, len]
  have inc := span (x:=x) (by
    intro c hc v hv cv
    have hv' : v ∈ (range (p.len + 1)).image p.vertex := full.symm ▸ hv
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hv'
    have bound : i ≤ p.len := by have := mem_range.mp hi; omega
    have path := p.walk bound le_rfl
    rw [last] at path
    have dl := long hc hv cv path
    simpa [show i = 0 by omega] using p.start)
  have cb := (card_insert_le a (insert x (Y ∪ Z))).trans
    (Nat.succ_le_succ ((card_insert_le x (Y ∪ Z)).trans (Nat.succ_le_succ (card_union_le _ _))))
  change (insert a (insert x (Y ∪ Z))).card ≤ Y.card + Z.card + 1 + 1 at cb
  change Z.card < r at third
  have geometry : ball D V a 2 = insert a (insert x (Y ∪ Z)) :=
    eq_of_subset_of_card_le inc (by omega)
  exact ⟨qe, x, hx, p, len, last, full, geometry⟩

/-- The outgoing row of a first-layer sink is contained in the actual
second layer of its root. If the layer has one spare label, it omits one
specified physical label. -/
theorem sink_row_omission {D : CH.Digraph} {V : Finset ℕ} {q r a s : ℕ}
    (free : QFree D V q) (fit : 2 ≤ q) (reg : OutEq r D V) (av : a ∈ V)
    (sa : s ∈ outN D V a) (sink : ∀ z ∈ outN D V a, D s z ≠ true)
    (size : (ball D V a 2 \ ball D V a 1).card = r + 1) :
    ∃ b ∈ ball D V a 2 \ ball D V a 1, outN D V s = (ball D V a 2 \ ball D V a 1).erase b := by
  classical
  let Q := ball D V a 2 \ ball D V a 1
  have H : outN D V s ⊆ Q := by
    intro z hz
    obtain ⟨zv, e⟩ := mem_outN.mp hz
    have s1 := (mem_ball_one av).mpr (Or.inr sa)
    refine mem_sdiff.mpr ⟨ball_step s1 zv e, ?_⟩
    intro mz
    rcases (mem_ball_one av).mp mz with rfl | zh
    · exact no_back_arc free av s1 (by omega : 1 + 1 ≤ q) e
    · exact sink z zh e
  have xs := reg s (mem_outN.mp sa).1
  have xc := card_sdiff_add_card_eq_card H
  change Q.card = r + 1 at size
  obtain ⟨b, hb⟩ := card_pos.mp (show 0 < (Q \ outN D V s).card by omega)
  obtain ⟨bq, off⟩ := mem_sdiff.mp hb
  refine ⟨b,bq,eq_of_subset_of_card_le (fun z hz=>mem_erase.mpr ⟨fun e=>off (e ▸ hz),H hz⟩) ?_⟩
  rw [card_erase_of_mem bq, size, xs]
  omega

/-- A physical first-layer path with its endpoint's exact second ball.
The path, start and omitted layer labels all refer to the original graph. -/
structure SinkBank (D : CH.Digraph) (V : Finset ℕ) (u a r : ℕ) where
  start : ℕ
  path : ShortestSinkPath D (outN D V u) start
  length : path.len + 1 = r
  last : path.vertex path.len = a
  support : (range (path.len + 1)).image path.vertex = outN D V u
  child_ball : ball D V a 2 = insert a (insert start
    ((ball D V u 2 \ ball D V u 1) ∪ (ball D V u 3 \ ball D V u 2)))

namespace SinkBank

/-- In the active path, the chosen successor is the unique native head
outside the child's punctured two-ball. -/
theorem successor_outside {D V u a r q} (bank : SinkBank D V u a r)
    (free : QFree D V q) (diag : r ≤ q) (reg : OutEq r D V)
    (hu : u ∈ V) {i : ℕ} (hi : i < bank.path.len) :
    outN D V (bank.path.vertex i) \ (ball D V a 2).erase a =
      {bank.path.vertex (i + 1)} := by
  let X := outN D V u
  let Y := ball D V u 2 \ ball D V u 1
  let Z := ball D V u 3 \ ball D V u 2
  let p := bank.path
  change i < p.len at hi
  have length : p.len + 1 = r := bank.length
  have xv : X ⊆ V := outN_subset
  have nc : X.card ≤ q := (reg u hu).le.trans diag
  have inc (j) (hj : j ≤ p.len) : p.vertex j ∈ ball D V u 1 :=
    (mem_ball_one hu).mpr (Or.inr (p.mem j hj))
  have unique (j) (hj : j ≤ p.len) (e : p.vertex (i + 1) = p.vertex j) : j = i + 1 := by
    have inj := p.injective (free.mono_set xv) nc
    exact (inj (mem_range.mpr (by omega)) (mem_range.mpr (by omega)) e).symm
  have outside : p.vertex (i + 1) ∉ (ball D V a 2).erase a := by
    intro bad
    obtain ⟨na, hm⟩ := mem_erase.mp bad
    rw [bank.child_ball] at hm
    rcases mem_insert.mp hm with e | h
    · exact na e
    rcases mem_insert.mp h with e | h
    · have j := unique 0 (Nat.zero_le _) (e.trans p.start.symm)
      omega
    rcases mem_union.mp h with hy | hz
    · exact (mem_sdiff.mp hy).2 (inc _ (by omega))
    · exact (mem_sdiff.mp hz).2 (ball_mono_radius (by decide : 1 ≤ 2) (inc _ (by omega)))
  apply Subset.antisymm
  · intro z hz
    obtain ⟨row, off⟩ := mem_sdiff.mp hz
    obtain ⟨zv, edge⟩ := mem_outN.mp row
    have z2 := ball_step (inc _ (by omega)) zv edge
    have zx : z ∈ X := by
      by_cases z1 : z ∈ ball D V u 1
      · rcases (mem_ball_one hu).mp z1 with rfl | hx
        · exact (no_back_arc free hu (inc _ (by omega)) (by omega : 1+1≤q) edge).elim
        · exact hx
      · have zy : z ∈ Y := mem_sdiff.mpr ⟨z2,z1⟩
        have za : z ≠ a := fun e => z1 (e ▸ (bank.last ▸ inc p.len le_rfl))
        exact (off (mem_erase.mpr ⟨za, by
          rw [bank.child_ball]
          exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ zy))⟩)).elim
    have hm : z ∈ (range (p.len + 1)).image p.vertex := bank.support.symm ▸ (show z ∈ outN D V u from zx)
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hm
    have bound : j ≤ p.len := by have := mem_range.mp hj; omega
    exact mem_singleton.mpr (congrArg p.vertex (p.no_chord (free.mono_set xv) nc (by omega) bound edge))
  · exact singleton_subset_iff.mpr
      (mem_sdiff.mpr ⟨mem_outN.mpr ⟨xv (p.mem _ (by omega)),p.edge i hi⟩,outside⟩)

end SinkBank

#print axioms no_child_return
#print axioms same_path_of_unique_successor
#print axioms unique_start_of_sink_omission
#print axioms sink_path_le_of_two_sinks
#print axioms short_sink_from_two_entries
#print axioms unique_start_of_two_common_heads
#print axioms same_second_layer_incomparable
#print axioms unique_sink_geometry
#print axioms sink_row_omission
#print axioms SinkBank.successor_outside
end LeanCH.BR.TallBankTransfer
