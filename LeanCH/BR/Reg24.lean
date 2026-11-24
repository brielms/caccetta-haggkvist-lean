import LeanCH.BR.Reg24Eight

/-!
# No 8-regular digraph on 24 vertices without cycles of length `≤ 3` (Lean 4.35.0)

Paper source: `checkpoints/boundary_20261111/Z8_attempt_subagent.md`, Lemma 2 and Theorem 3
(audited in `Z8_audit_subagent.md`).

Setting (`RHyp k G`): labels `range (3k)`, loopless, no directed cycle of length `≤ 3`, every
out-degree and every in-degree exactly `k`. At a label `v`: `II v = I(v)`, `OO v = O(v)`,
`MM v` = the `k - 1` non-neighbours.

* `two_heads` (**Lemma 2**): every `x ∈ O(v)` has at least 2 heads inside `O(v)`.
* `src_eq_mid`: transitive triples (`a → b → c`, `a → c`) counted at the source `a`
  (`Σ_a e(O(a))`) and at the middle `b` (`Σ_b e(I(b), O(b))`) agree (any digraph, any label set).
* `mid` (middle count at one vertex): `k² ≤ e(I(b), O(b)) + 2 e(O(b))`.
* `cube`: `3k · k² ≤ 3 Σ_a e(O(a))`.
* `no_regular` (**Theorem 3**): no such digraph for `1 ≤ k ≤ 8`.
  - `k ≤ 6`: `D[O(v)]` contradicts CH(2) (`BR(3,2)` through `ch_subset`);
  - `k = 7`: `BR(3,2)` makes `D[O(v)]` 2-regular, so `e = 14` and `3 · 14 < 49`;
  - `k = 8`: Lemma 1(v) (`eight_arcs`) gives `e(O(v)) ≤ 21`, and `3 · 21 < 64`.

  Only `BR(3,2)` is imported; `BR(3,3..7)` are not used.
* `no_regular_24`: the case `k = 8`, stated on `range 24`.
-/

namespace LeanCH.BR.Reg24

open CH Compose.Boundary Compose.FloorSix
open LeanCH.BR.BR35 hiding V Hyp Root root_of

/-- In-neighbours of `u` among the `3k` labels. -/
def II (G : CH.Digraph) (k u : Nat) : Finset Nat :=
  (Finset.range (3 * k)).filter (fun v => G v u = true)

/-- Out-neighbours of `u` among the `3k` labels. -/
def OO (G : CH.Digraph) (k u : Nat) : Finset Nat :=
  (Finset.range (3 * k)).filter (fun v => G u v = true)

/-- Non-neighbours of `u` among the `3k` labels. -/
def MM (G : CH.Digraph) (k u : Nat) : Finset Nat :=
  (Finset.range (3 * k)).filter (fun v => v ≠ u ∧ G v u = false ∧ G u v = false)

/-- A `k`-regular digraph on the labels `range (3k)` with no loop and no directed cycle of
length `≤ 3`. -/
structure RHyp (k : Nat) (G : CH.Digraph) : Prop where
  loopless : CH.Loopless G (3 * k)
  noShort : ¬ CH.HasDirectedCycleAtMost G (3 * k) 3
  out : ∀ v, v < 3 * k → oc G (Finset.range (3 * k)) v = k
  inn : ∀ v, v < 3 * k → ic G (Finset.range (3 * k)) v = k

theorem mem_II {G : CH.Digraph} {k u v : Nat} : v ∈ II G k u ↔ v < 3 * k ∧ G v u = true := by
  simp [II]

theorem mem_OO {G : CH.Digraph} {k u v : Nat} : v ∈ OO G k u ↔ v < 3 * k ∧ G u v = true := by
  simp [OO]

theorem mem_MM {G : CH.Digraph} {k u v : Nat} :
    v ∈ MM G k u ↔ v < 3 * k ∧ v ≠ u ∧ G v u = false ∧ G u v = false := by
  simp [MM]

section free

variable {k : Nat} {G : CH.Digraph} {u : Nat}

theorem ltI {w : Nat} (h : w ∈ II G k u) : w < 3 * k := (mem_II.mp h).1
theorem ltO {w : Nat} (h : w ∈ OO G k u) : w < 3 * k := (mem_OO.mp h).1
theorem ltM {w : Nat} (h : w ∈ MM G k u) : w < 3 * k := (mem_MM.mp h).1
theorem subI : II G k u ⊆ Finset.range (3 * k) := Finset.filter_subset _ _
theorem subO : OO G k u ⊆ Finset.range (3 * k) := Finset.filter_subset _ _
theorem subM : MM G k u ⊆ Finset.range (3 * k) := Finset.filter_subset _ _

theorem uM : u ∉ MM G k u := fun h => (mem_MM.mp h).2.1 rfl

theorem dIM : Disjoint (II G k u) (MM G k u) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  have := (mem_II.mp h1).2; rw [(mem_MM.mp h2).2.2.1] at this; exact Bool.false_ne_true this

theorem dOM : Disjoint (OO G k u) (MM G k u) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  have := (mem_OO.mp h1).2; rw [(mem_MM.mp h2).2.2.2] at this; exact Bool.false_ne_true this

theorem V_eq (hu : u < 3 * k) :
    Finset.range (3 * k) = insert u (II G k u ∪ OO G k u ∪ MM G k u) := by
  ext v
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_union, mem_II, mem_OO, mem_MM]
  constructor
  · intro hv
    by_cases h1 : v = u
    · exact Or.inl h1
    right
    cases h2 : G v u
    · cases h3 : G u v
      · exact Or.inr ⟨hv, h1, rfl, rfl⟩
      · exact Or.inl (Or.inr ⟨hv, rfl⟩)
    · exact Or.inl (Or.inl ⟨hv, rfl⟩)
  · rintro (rfl | (h | h) | h)
    · exact hu
    · exact h.1
    · exact h.1
    · exact h.1

end free

namespace RHyp

variable {k : Nat} {G : CH.Digraph} (H : RHyp k G)
include H

theorem n2 {a b : Nat} (ha : a < 3 * k) (hb : b < 3 * k) (h1 : G a b = true) (h2 : G b a = true) :
    False :=
  no2 H.loopless H.noShort ha hb h1 h2

theorem tri {a b c : Nat} (ha : a < 3 * k) (hb : b < 3 * k) (hc : c < 3 * k) (h1 : G a b = true)
    (h2 : G b c = true) : G c a = false := by
  cases h' : G c a
  · rfl
  · exact (no3 H.loopless H.noShort ha hb hc h1 h2 h').elim

theorem back {a b : Nat} (ha : a < 3 * k) (hb : b < 3 * k) (h : G a b = true) : G b a = false := by
  cases h' : G b a
  · rfl
  · exact (H.n2 ha hb h h').elim

variable {u : Nat}

theorem uI (hu : u < 3 * k) : u ∉ II G k u := fun h => by
  have := (mem_II.mp h).2; rw [H.loopless u hu] at this; exact Bool.false_ne_true this

theorem uO (hu : u < 3 * k) : u ∉ OO G k u := fun h => by
  have := (mem_OO.mp h).2; rw [H.loopless u hu] at this; exact Bool.false_ne_true this

theorem dIO (hu : u < 3 * k) : Disjoint (II G k u) (OO G k u) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  exact H.n2 (ltI h1) hu (mem_II.mp h1).2 (mem_OO.mp h2).2

theorem part (hu : u < 3 * k) (p : Nat → Prop) [DecidablePred p] :
    ((Finset.range (3 * k)).filter p).card =
      (if p u then 1 else 0) + ((II G k u).filter p).card + ((OO G k u).filter p).card +
        ((MM G k u).filter p).card := by
  have hun : u ∉ II G k u ∪ OO G k u ∪ MM G k u := by
    simp only [Finset.mem_union, not_or]
    exact ⟨⟨H.uI hu, H.uO hu⟩, uM⟩
  have hd1 : Disjoint (II G k u ∪ OO G k u) (MM G k u) :=
    Finset.disjoint_union_left.mpr ⟨dIM, dOM⟩
  have hd2 := H.dIO hu
  have e1 : ((II G k u).filter p ∪ (OO G k u).filter p ∪ (MM G k u).filter p).card =
      ((II G k u).filter p).card + ((OO G k u).filter p).card + ((MM G k u).filter p).card := by
    rw [← Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hd1),
      Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hd2)]
  rw [V_eq (G := G) hu, Finset.filter_insert, Finset.filter_union, Finset.filter_union]
  split_ifs with hp
  · rw [Finset.card_insert_of_notMem, e1]
    · omega
    · intro h
      apply hun
      simp only [Finset.mem_union, Finset.mem_filter] at h ⊢
      tauto
  · rw [e1]
    omega

theorem cardO (hu : u < 3 * k) : (OO G k u).card = k := H.out u hu
theorem cardI (hu : u < 3 * k) : (II G k u).card = k := H.inn u hu

theorem cardM (hu : u < 3 * k) : (MM G k u).card + 1 = k := by
  have h := H.part hu (fun _ => True)
  simp only [Finset.filter_true_of_mem (fun _ _ => trivial), ite_true, Finset.card_range] at h
  have h1 := H.cardO hu
  have h2 := H.cardI hu
  omega

theorem split_out (hu : u < 3 * k) (w : Nat) :
    oc G (Finset.range (3 * k)) w = (if G w u = true then 1 else 0) + oc G (II G k u) w +
      oc G (OO G k u) w + oc G (MM G k u) w :=
  H.part hu (fun v => G w v = true)

theorem split_in (hu : u < 3 * k) (w : Nat) :
    ic G (Finset.range (3 * k)) w = (if G u w = true then 1 else 0) + ic G (II G k u) w +
      ic G (OO G k u) w + ic G (MM G k u) w :=
  H.part hu (fun v => G v w = true)

/-- An out-neighbour of `u` heads no in-neighbour of `u`. -/
theorem O_noI (hu : u < 3 * k) {x w : Nat} (hx : x ∈ OO G k u) (hw : w ∈ II G k u) :
    G x w = false :=
  H.tri (ltI hw) hu (ltO hx) (mem_II.mp hw).2 (mem_OO.mp hx).2

theorem outO (hu : u < 3 * k) {x : Nat} (hx : x ∈ OO G k u) :
    oc G (Finset.range (3 * k)) x = oc G (OO G k u) x + oc G (MM G k u) x := by
  rw [H.split_out hu x, H.back hu (ltO hx) (mem_OO.mp hx).2,
    oc_eq_zero (fun w hw => H.O_noI hu hx hw)]
  simp

theorem inI (hu : u < 3 * k) {w : Nat} (hw : w ∈ II G k u) :
    ic G (Finset.range (3 * k)) w = ic G (II G k u) w + ic G (MM G k u) w := by
  rw [H.split_in hu w, H.back (ltI hw) hu (mem_II.mp hw).2,
    ic_eq_zero (fun x hx => H.O_noI hu hx hw)]
  simp

/-- **Lemma 2.** In a `k`-regular No2/No3 digraph on `3k` vertices, every out-neighbour `x` of `v`
has at least two heads inside `O(v)`. -/
theorem two_heads {v : Nat} (hv : v < 3 * k) {x : Nat} (hx : x ∈ OO G k v) :
    2 ≤ oc G (OO G k v) x := by
  by_contra hlt
  have hxl := ltO hx
  have hO := H.cardO hv
  have hI := H.cardI hv
  have hM := H.cardM hv
  -- `out(x) = k` forces `x` to head all of `M(v)`
  have ho := H.outO hv hx
  rw [H.out x hxl] at ho
  have hMle := oc_le (G := G) (MM G k v) x
  have hall : ∀ m ∈ MM G k v, G x m = true := all_of_oc (by omega)
  -- `in(x) = k`: no row heads `x` and at most `k - 2` vertices of `O(v)` do, so some `w ∈ I(v)`
  -- does
  have hi := H.split_in hv x
  rw [ite_eq_left (mem_OO.mp hx).2, H.inn x hxl] at hi
  have hiM : ic G (MM G k v) x = 0 := ic_eq_zero (fun m hm => H.back hxl (ltM hm) (hall m hm))
  have hOO := oc_ic_le_mem H.loopless H.noShort subO hx
  obtain ⟨w, hwI, hwx⟩ := exists_of_ic (G := G) (A := II G k v) (w := x) (by omega)
  -- no row heads `w` (`m → w → x → m`), so `in(w) ≤ k - 1`
  have hw := H.inI hv hwI
  rw [H.inn w (ltI hwI)] at hw
  have hwM : ic G (MM G k v) w = 0 :=
    ic_eq_zero (fun m hm => H.tri (ltI hwI) hxl (ltM hm) hwx (hall m hm))
  have hII := oc_ic_le_mem H.loopless H.noShort subI hwI
  omega

/-- The middle count at one vertex `c ∈ O(b)`: `k ≤ in_I(c) + in_O(c) + out_O(c)`. Rows heading
`c` are rows that `c` misses, and `c` misses `out_O(c) - 1` of the `k - 1` rows. -/
theorem mid_pt {b : Nat} (hb : b < 3 * k) {c : Nat} (hc : c ∈ OO G k b) :
    k ≤ ic G (II G k b) c + ic G (OO G k b) c + oc G (OO G k b) c := by
  have hcl := ltO hc
  have hi := H.split_in hb c
  rw [ite_eq_left (mem_OO.mp hc).2, H.inn c hcl] at hi
  have ho := H.outO hb hc
  rw [H.out c hcl] at ho
  have hM := H.cardM hb
  have hMM := oc_ic_le H.loopless H.noShort subM hcl (B := MM G k b) (fun v hv _ => hv)
  omega

/-- **Middle count.** `k² ≤ e(I(b), O(b)) + 2 e(O(b))`. -/
theorem mid {b : Nat} (hb : b < 3 * k) :
    k * k ≤ ∑ c ∈ OO G k b, ic G (II G k b) c + 2 * ∑ c ∈ OO G k b, oc G (OO G k b) c := by
  have h := Finset.sum_le_sum (fun c hc => H.mid_pt hb hc)
  rw [Finset.sum_const, H.cardO hb, smul_eq_mul, Finset.sum_add_distrib,
    Finset.sum_add_distrib] at h
  have hs := swap G (OO G k b) (OO G k b)
  omega

end RHyp

/-- **Transitive triples.** Counted at the source and at the middle vertex. -/
theorem src_eq_mid (G : CH.Digraph) (V : Finset Nat) :
    ∑ a ∈ V, ∑ x ∈ V.filter (fun y => G a y = true), oc G (V.filter (fun y => G a y = true)) x =
      ∑ b ∈ V, ∑ c ∈ V.filter (fun y => G b y = true),
        ic G (V.filter (fun y => G y b = true)) c := by
  classical
  have hL : ∀ a ∈ V,
      ∑ x ∈ V.filter (fun y => G a y = true), oc G (V.filter (fun y => G a y = true)) x =
        ∑ b ∈ V, ∑ c ∈ V, (if G a b = true ∧ G b c = true ∧ G a c = true then 1 else 0) := by
    intro a _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    unfold oc
    rw [Finset.card_filter, Finset.sum_filter]
    by_cases h : G a b = true
    · rw [ite_eq_left h]
      apply Finset.sum_congr rfl
      intro c _
      by_cases h1 : G a c = true <;> by_cases h2 : G b c = true <;> simp [h, h1, h2]
    · rw [ite_eq_right h]
      symm
      apply Finset.sum_eq_zero
      intro c _
      simp [h]
  have hR : ∀ b ∈ V,
      ∑ c ∈ V.filter (fun y => G b y = true), ic G (V.filter (fun y => G y b = true)) c =
        ∑ c ∈ V, ∑ a ∈ V, (if G a b = true ∧ G b c = true ∧ G a c = true then 1 else 0) := by
    intro b _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    unfold ic
    rw [Finset.card_filter, Finset.sum_filter]
    by_cases h : G b c = true
    · rw [ite_eq_left h]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h1 : G a b = true <;> by_cases h2 : G a c = true <;> simp [h, h1, h2]
    · rw [ite_eq_right h]
      symm
      apply Finset.sum_eq_zero
      intro a _
      simp [h]
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun b _ => Finset.sum_comm)

namespace RHyp

variable {k : Nat} {G : CH.Digraph} (H : RHyp k G)
include H

/-- **Theorem 3, counting half.** `3k · k² ≤ 3 T` with `T = Σ_a e(O(a))`, i.e. the average of
`e(O(a))` is at least `k² / 3`. -/
theorem cube :
    3 * k * (k * k) ≤ 3 * ∑ a ∈ Finset.range (3 * k), ∑ x ∈ OO G k a, oc G (OO G k a) x := by
  have h := Finset.sum_le_sum (fun b hb => H.mid (Finset.mem_range.mp hb))
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    at h
  have he := src_eq_mid G (Finset.range (3 * k))
  change ∑ a ∈ Finset.range (3 * k), ∑ x ∈ OO G k a, oc G (OO G k a) x =
    ∑ b ∈ Finset.range (3 * k), ∑ c ∈ OO G k b, ic G (II G k b) c at he
  omega

end RHyp

/-- **Theorem 3.** For `1 ≤ k ≤ 8` there is no `k`-regular loopless digraph on `3k` vertices
without directed cycles of length at most 3. -/
theorem no_regular {k : Nat} (hk1 : 1 ≤ k) (hk : k ≤ 8) (G : CH.Digraph)
    (loopless : CH.Loopless G (3 * k))
    (outdeg : ∀ v, v < 3 * k → ((Finset.range (3 * k)).filter (fun w => G v w = true)).card = k)
    (indeg : ∀ v, v < 3 * k → (par G (3 * k) v).card = k)
    (noShort : ¬ CH.HasDirectedCycleAtMost G (3 * k) 3) : False := by
  have H : RHyp k G := ⟨loopless, noShort, outdeg, indeg⟩
  have hcube := H.cube
  rcases (by omega : k ≤ 6 ∨ k = 7 ∨ k = 8) with h6 | rfl | rfl
  · -- `k ≤ 6`: `D[O(0)]` has internal minimum out-degree 2 on at most 6 vertices, against CH(2)
    have h0 : 0 < 3 * k := by omega
    exact LeanCH.BR.BR36.ch_subset (by norm_num) LeanCH.BR.SmallBR.br_two subO
      (Finset.card_pos.mp (by rw [H.cardO h0]; omega)) (by rw [H.cardO h0]; omega) loopless noShort
      (fun x hx => H.two_heads h0 hx)
  · -- `k = 7`: `BR(3,2)` makes every `D[O(a)]` 2-regular, so `e(O(a)) = 14`
    have hb : ∀ a ∈ Finset.range (3 * 7), ∑ x ∈ OO G 7 a, oc G (OO G 7 a) x = 14 := by
      intro a ha
      have ha' := Finset.mem_range.mp ha
      have hreg : ∀ x ∈ OO G 7 a, oc G (OO G 7 a) x = 2 :=
        LeanCH.BR.StrictCap.induced_regular LeanCH.BR.SmallBR.br_two subO
          (H.cardO ha') loopless noShort (fun x hx => H.two_heads ha' hx)
      rw [Finset.sum_congr rfl hreg, Finset.sum_const, H.cardO ha', smul_eq_mul]
    rw [Finset.sum_congr rfl hb, Finset.sum_const, Finset.card_range, smul_eq_mul] at hcube
    omega
  · -- `k = 8`: Lemma 1(v) gives `e(O(a)) ≤ 21`, and `3 · 21 < 64`
    have hb : ∀ a ∈ Finset.range (3 * 8), ∑ x ∈ OO G 8 a, oc G (OO G 8 a) x ≤ 21 := by
      intro a ha
      have ha' := Finset.mem_range.mp ha
      exact eight_arcs loopless noShort subO (H.cardO ha') (fun x hx => H.two_heads ha' hx)
    have h := Finset.sum_le_sum hb
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at h
    omega

/-- **No 8-regular No2/No3 digraph on 24 vertices.** No loopless digraph on the labels `range 24`
in which every out-degree and every in-degree is exactly 8 is free of directed cycles of length at
most 3. -/
theorem no_regular_24 (G : CH.Digraph) (loopless : CH.Loopless G 24)
    (outdeg : ∀ v, v < 24 → ((Finset.range 24).filter (fun w => G v w = true)).card = 8)
    (indeg : ∀ v, v < 24 → (par G 24 v).card = 8)
    (noShort : ¬ CH.HasDirectedCycleAtMost G 24 3) : False :=
  no_regular (k := 8) (by norm_num) le_rfl G loopless outdeg indeg noShort

end LeanCH.BR.Reg24
