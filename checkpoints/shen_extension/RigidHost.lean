import checkpoints.shen_extension.FifthStripAllParity

/-!
# The rigid host as a metric object

A `q`-free host of order `q s`, `q = 2 i + 1`, out-degree `≥ s`, whose `i`-balls have exactly
`s i + 1` labels and whose `(i+1)`-balls have exactly `s (i+1)` labels (`Rigid`). Generic in
`q, s, i`. `rigid_of_top` shows the fifth-strip top order is such a host.

* (R2) `rev_inner`, `rev_outer`: in-balls are exact too.
* (R3) `part_outer`, `part_inner`: `ball v i` and `reverseBall v (i+1)` meet only in `v` and cover
  `V`; likewise `ball v (i+1)` and `reverseBall v i`.
* (R4) `dich`: for `x ≠ y`, `y ∈ ball x i ↔ x ∉ ball y (i+1)`. `antipode_symm`: the layer
  `i + 1` relation is symmetric; `antipode_card`: each vertex has exactly `s - 1` antipodes.
* (R6) `diameter`: every `x` is within `q` of every `y`.
* (R5) `arc_return`: an arc `v → u` has `v ∈ layer q u`, so `d(u,v) = q` exactly
  (`arc_return_walk`), and the arc lies on a closed walk of length `q + 1`.
* (R7) `rev_tail`: `|reverseBall v (q - k)| ≤ s (q - k)` for `k ≤ i`.
* (R8) `stuck_row_far`, `stuck_row_iff`, `stuck_row_heads`: rows of `layer i z`.
* (R9) `swap`, `swap_free`, `swap_degree`, `rigid_swap_of_top`: rerouting one arc `x → y`
  to `x → t` when `x` is not within `q - 1` of `t` keeps a host a host (and rigid).
-/

set_option linter.style.longLine false
namespace LeanCH.BR.RigidHost
open Finset BRq2 BRq3 FifthStripAll
open DotTwoPassShellTransport (layer)
open ShapeClimbRoot (mem_layer card_ball_succ)

/-- The rigid host. -/
structure Rigid (D : CH.Digraph) (V : Finset ℕ) (q s i : ℕ) : Prop where
  free : QFree D V q
  odd : q = 2*i + 1
  degree : ∀ v ∈ V, s ≤ (outN D V v).card
  size : V.card = q*s
  floor : ∀ k ≤ i, ∀ v ∈ V, s*k + 1 ≤ (ball D V v k).card
  inner : ∀ v ∈ V, (ball D V v i).card = s*i + 1
  outer : ∀ v ∈ V, (ball D V v (i+1)).card = s*(i+1)

/-- **Instance.** The fifth-strip top order is rigid. -/
theorem rigid_of_top {a : ℕ} (ha : 2 ≤ a) (L : LedgerFloors a) (tc : Top a ((2*a+7)*(a+7)))
    {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V (2*a+7))
    (degree : ∀ v ∈ V, a+7 ≤ (outN D V v).card)
    (size : V.card = (2*a+7)*(a+7)) : Rigid D V (2*a+7) (a+7) (a+3) := by
  have rig := top_rigid ha L tc free degree size
  refine ⟨free, by omega, degree, size, ?_, fun v hv => (rig v hv).1,
    fun v hv => (rig v hv).2⟩
  intro k hk v hv
  rcases (by omega : k ≤ a+1 ∨ k = a+2 ∨ k = a+3) with h | rfl | rfl
  · exact ShenFifthStrip.inner_growth free degree hv k h
  · exact L.f2 D V free degree v hv
  · exact (rig v hv).1.ge

section
variable {D : CH.Digraph} {V : Finset ℕ} {q s i : ℕ}

theorem Rigid.order (R : Rigid D V q s i) : V.card = s*(i+1) + s*i := by
  rw [R.size, R.odd]; ring

/-! ### (R2) exact in-balls -/

theorem rev_inner (R : Rigid D V q s i) : ∀ v ∈ V, (reverseBall D V v i).card = s*i + 1 := by
  have h := two_balls_boundary_cards (i := i+1) (j := i) (a := s*(i+1)) (b := s*i+1) R.free
    (by rw [R.odd]; omega) (fun v hv => (R.outer v hv).ge) (fun v hv => (R.inner v hv).ge)
    (by have := R.order; omega)
  exact fun v hv => (h v hv).2.2

theorem rev_outer (R : Rigid D V q s i) : ∀ v ∈ V, (reverseBall D V v (i+1)).card = s*(i+1) := by
  have h := two_balls_boundary_cards (i := i) (j := i+1) (a := s*i+1) (b := s*(i+1)) R.free
    (by rw [R.odd]; omega) (fun v hv => (R.inner v hv).ge) (fun v hv => (R.outer v hv).ge)
    (by have := R.order; omega)
  exact fun v hv => (h v hv).2.2

/-! ### (R3) exact partitions -/

theorem part_outer (R : Rigid D V q s i) {v : ℕ} (hv : v ∈ V) :
    reverseBall D V v (i+1) = (V \ ball D V v i) ∪ {v} :=
  two_balls_boundary_complement (a := s*i+1) (b := s*(i+1)) R.free (by rw [R.odd]; omega)
    (fun w hw => (R.inner w hw).ge) (fun w hw => (R.outer w hw).ge)
    (by have := R.order; omega) hv

theorem part_inner (R : Rigid D V q s i) {v : ℕ} (hv : v ∈ V) :
    reverseBall D V v i = (V \ ball D V v (i+1)) ∪ {v} :=
  two_balls_boundary_complement (a := s*(i+1)) (b := s*i+1) R.free (by rw [R.odd]; omega)
    (fun w hw => (R.outer w hw).ge) (fun w hw => (R.inner w hw).ge)
    (by have := R.order; omega) hv

/-! ### (R4) the dichotomy and antipodes -/

/-- **Dichotomy.** For `x ≠ y`: `d(x,y) ≤ i ⟺ ¬ d(y,x) ≤ i + 1`. -/
theorem dich (R : Rigid D V q s i) {x y : ℕ} (hx : x ∈ V) (hy : y ∈ V) (ne : x ≠ y) :
    y ∈ ball D V x i ↔ x ∉ ball D V y (i+1) := by
  have p := part_outer R hx
  have key : y ∈ reverseBall D V x (i+1) ↔ x ∈ ball D V y (i+1) := by
    simp only [reverseBall, mem_filter, hy, true_and]
  rw [p] at key
  simp only [mem_union, mem_sdiff, hy, true_and, mem_singleton, Ne.symm ne, or_false] at key
  constructor
  · intro h h'; exact (key.mpr h') h
  · intro h; by_contra h'; exact h (key.mp h')

/-- The second form: `d(x,y) ≤ i + 1 ⟺ ¬ d(y,x) ≤ i`. -/
theorem dich' (R : Rigid D V q s i) {x y : ℕ} (hx : x ∈ V) (hy : y ∈ V) (ne : x ≠ y) :
    y ∈ ball D V x (i+1) ↔ x ∉ ball D V y i := by
  rw [dich R hy hx (Ne.symm ne)]; exact not_not.symm

theorem mem_layer_succ {u w : ℕ} :
    w ∈ layer D V (i+1) u ↔ w ∈ ball D V u (i+1) ∧ w ∉ ball D V u i := by
  rw [mem_layer, Nat.add_sub_cancel]

/-- **Antipodes are symmetric.** -/
theorem antipode_symm (R : Rigid D V q s i) {v w : ℕ} (hv : v ∈ V) (hw : w ∈ V) :
    w ∈ layer D V (i+1) v ↔ v ∈ layer D V (i+1) w := by
  by_cases e : v = w
  · subst e; rfl
  have A := dich R hv hw e
  have B := dich R hw hv (Ne.symm e)
  rw [mem_layer_succ, mem_layer_succ]
  tauto

/-- Each vertex has exactly `s - 1` antipodes. -/
theorem antipode_card (R : Rigid D V q s i) {v : ℕ} (hv : v ∈ V) :
    (layer D V (i+1) v).card = s - 1 := by
  have e := card_ball_succ (D := D) (V := V) (u := v) i
  rw [R.outer v hv, R.inner v hv] at e
  have : s*(i+1) = s*i + s := by ring
  omega

/-! ### (R6) diameter -/

theorem diameter (R : Rigid D V q s i) {x y : ℕ} (hx : x ∈ V) (hy : y ∈ V) :
    x ∈ ball D V y q := by
  by_contra hno
  have dis : Disjoint (ball D V y (i+1)) (reverseBall D V x i) := by
    rw [disjoint_left]
    intro z hz hz'
    have hxz : x ∈ ball D V z i := (mem_filter.mp hz').2
    have := ball_trans hz hxz
    rw [show i + 1 + i = q by rw [R.odd]; omega] at this
    exact hno this
  have hsub : ball D V y (i+1) ∪ reverseBall D V x i ⊆ V :=
    union_subset ball_subset (filter_subset _ _)
  have c := card_le_card hsub
  rw [card_union_of_disjoint dis, R.outer y hy, rev_inner R x hx] at c
  have := R.order
  omega

/-! ### (R5) every arc has return distance exactly `q` -/

theorem arc_return (R : Rigid D V q s i) {u v : ℕ} (hu : u ∈ V) (hv : v ∈ V)
    (arc : D v u = true) : v ∈ ball D V u q ∧ v ∉ ball D V u (q-1) := by
  refine ⟨diameter R hv hu, fun h => no_back_arc R.free hu h (by rw [R.odd]; omega) arc⟩

theorem arc_return_walk (R : Rigid D V q s i) {u v : ℕ} (hu : u ∈ V) (hv : v ∈ V)
    (arc : D v u = true) : Walk D V u v q ∧ Walk D V v v (q+1) := by
  obtain ⟨h1, h2⟩ := arc_return R hu hv arc
  obtain ⟨-, j, hj, w⟩ := mem_ball.mp h1
  have : j = q := by
    by_contra ne
    exact h2 (mem_ball.mpr ⟨hv, j, by omega, w⟩)
  subst this
  exact ⟨w, .step hu arc w⟩

/-- In-neighbours of `u` lie in `layer q u`. -/
theorem in_layer_q (R : Rigid D V q s i) {u v : ℕ} (hu : u ∈ V) (hv : v ∈ V)
    (arc : D v u = true) : v ∈ layer D V q u :=
  mem_layer.mpr (arc_return R hu hv arc)

/-! ### (R7) tails -/

theorem rev_tail (R : Rigid D V q s i) {k : ℕ} (hk : k ≤ i) {v : ℕ} (hv : v ∈ V) :
    (reverseBall D V v (q-k)).card ≤ s*(q-k) := by
  have h := reverseBall_add_ball_le (v := v) (i := k) (j := q-k) R.free (by have := R.odd; omega)
  have f := R.floor k hk v hv
  have e : s*(q-k) + s*k = q*s := by
    rw [← mul_add, Nat.sub_add_cancel (by rw [R.odd]; omega), mul_comm]
  have := R.size
  omega

/-! ### (R8) stuck rows -/

theorem layer_ne {u v k : ℕ} (hu : u ∈ V) (hv : v ∈ layer D V k u) : v ≠ u := by
  rintro rfl
  exact (mem_layer.mp hv).2 (self_mem_ball hu)

/-- A row `v` of `layer i z` has `d(v,z) ≥ i + 2`. -/
theorem stuck_row_far (R : Rigid D V q s i) {z v : ℕ} (hz : z ∈ V) (hv : v ∈ layer D V i z) :
    z ∉ ball D V v (i+1) :=
  (dich R hz (ball_subset (mem_layer.mp hv).1) (layer_ne hz hv).symm).mp (mem_layer.mp hv).1

/-- Row `v` of `layer i z` heads `layer (i+1) z` iff `d(v,z) = i + 2`. -/
theorem stuck_row_iff (R : Rigid D V q s i) {z v : ℕ} (hz : z ∈ V) (hv : v ∈ layer D V i z) :
    (∃ h ∈ outN D V v, h ∈ layer D V (i+1) z) ↔ z ∈ ball D V v (i+2) := by
  have hvV : v ∈ V := ball_subset (mem_layer.mp hv).1
  constructor
  · rintro ⟨h, hh, hl⟩
    have hhV := (mem_outN.mp hh).1
    have zh : z ∈ layer D V (i+1) h := (antipode_symm R hz hhV).mp hl
    have := ball_trans (mem_ball_one_of_out hh) (mem_layer_succ.mp zh).1
    rwa [show 1 + (i+1) = i+2 by omega] at this
  · intro hb
    have far := stuck_row_far R hz hv
    obtain ⟨-, j, hj, w⟩ := mem_ball.mp hb
    have : j = (i+1)+1 := by
      by_contra ne
      exact far (mem_ball.mpr ⟨hz, j, by omega, w⟩)
    subst this
    cases w with
    | step hb' hab w' =>
      rename_i h
      refine ⟨h, mem_outN.mpr ⟨hb', hab⟩, ?_⟩
      have zh : z ∈ ball D V h (i+1) := mem_ball.mpr ⟨hz, _, le_rfl, w'⟩
      have zh' : z ∉ ball D V h i := by
        intro hi
        have := ball_trans (mem_ball_one_of_out (mem_outN.mpr ⟨hb', hab⟩)) hi
        exact far (by rwa [show 1 + i = i+1 by omega] at this)
      exact (antipode_symm R hb' hz).mp (mem_layer_succ.mpr ⟨zh, zh'⟩)

/-- **Stuck rows.** If `d(v,z) ≥ i + 3` for a row `v` of `layer i z` (`1 ≤ i`), all heads of
`v` lie in `ball z i` and at least one lies in `ball z (i-1)`. -/
theorem stuck_row_heads (R : Rigid D V q s i) (hi : 1 ≤ i) {z v : ℕ} (hz : z ∈ V)
    (hv : v ∈ layer D V i z) (stuck : z ∉ ball D V v (i+2)) :
    outN D V v ⊆ ball D V z i ∧ ∃ h ∈ outN D V v, h ∈ ball D V z (i-1) := by
  have hvV : v ∈ V := ball_subset (mem_layer.mp hv).1
  have sub : outN D V v ⊆ ball D V z i := by
    intro h hh
    by_contra hn
    have hb := ball_step (mem_layer.mp hv).1 (mem_outN.mp hh).1 (mem_outN.mp hh).2
    exact stuck ((stuck_row_iff R hz hv).mp ⟨h, hh, mem_layer_succ.mpr ⟨hb, hn⟩⟩)
  refine ⟨sub, ?_⟩
  by_contra hno
  push Not at hno
  have hsub : insert v (outN D V v) ⊆ layer D V i z := by
    intro h hh
    rcases mem_insert.mp hh with rfl | hh
    · exact hv
    · exact mem_layer.mpr ⟨sub hh, hno h hh⟩
  have vn : v ∉ outN D V v := fun h =>
    loopfree R.free (by rw [R.odd]; omega) hvV (mem_outN.mp h).2
  have c := card_le_card hsub
  rw [card_insert_of_notMem vn] at c
  have e := card_ball_succ (D := D) (V := V) (u := z) (i-1)
  rw [Nat.sub_add_cancel hi, R.inner z hz] at e
  have f := R.floor (i-1) (by omega) z hz
  have d := R.degree v hvV
  have m : s*i = s*(i-1) + s := by
    rw [← Nat.mul_succ]; congr 1; omega
  omega

end

/-! ### (R9) swap closure -/

/-- The arc `x → y` replaced by `x → t`. -/
def swap (D : CH.Digraph) (x y t : ℕ) : CH.Digraph := fun a b =>
  if a = x then (if b = t then true else if b = y then false else D a b) else D a b

/-- `D` plus the arc `x → t`. -/
def addArc (D : CH.Digraph) (x t : ℕ) : CH.Digraph := fun a b => D a b || (decide (a = x) && decide (b = t))

section
variable {D : CH.Digraph} {V : Finset ℕ}

theorem addArc_walk {x t : ℕ} {a b m : ℕ} (w : Walk (addArc D x t) V a b m) :
    Walk D V a b m ∨ ∃ m1 m2, m1 + 1 + m2 = m ∧ Walk D V t b m2 ∧ Walk (addArc D x t) V a x m1 := by
  induction w with
  | refl a => exact Or.inl (.refl a)
  | @step a c b k hc hac w' ih =>
    rcases ih with wD | ⟨m1, m2, e, wt, wa⟩
    · by_cases h : a = x ∧ c = t
      · obtain ⟨rfl, rfl⟩ := h
        exact Or.inr ⟨0, k, by omega, wD, .refl a⟩
      · have : D a c = true := by
          simp only [addArc, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hac
          tauto
        exact Or.inl (.step hc this wD)
    · exact Or.inr ⟨m1+1, m2, by omega, wt, .step hc hac wa⟩

theorem addArc_free {q x t : ℕ} (hx : x ∈ V) (free : QFree D V q)
    (far : x ∉ ball D V t (q-1)) : QFree (addArc D x t) V q := by
  intro a ℓ h1 h2 w
  rcases addArc_walk w with wD | ⟨m1, m2, e, wt, wa⟩
  · exact free a ℓ h1 h2 wD
  · have sub : ∀ a b, D a b = true → addArc D x t a b = true := fun a b h => by
      simp [addArc, h]
    have w2 := (walk_sub sub wt).append wa
    rcases addArc_walk w2 with wD | ⟨n1, n2, e', wt', -⟩
    · exact far (mem_ball.mpr ⟨hx, _, by omega, wD⟩)
    · exact far (mem_ball.mpr ⟨hx, _, by omega, wt'⟩)

theorem swap_le_addArc {x y t : ℕ} : ∀ a b, swap D x y t a b = true → addArc D x t a b = true := by
  intro a b h
  simp only [swap] at h
  simp only [addArc, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  by_cases h1 : a = x <;> by_cases h2 : b = t <;> by_cases h3 : b = y <;> simp_all

/-- **Swap keeps `q`-freeness** when `x` is not within `q - 1` of `t`. -/
theorem swap_free {q x y t : ℕ} (hx : x ∈ V) (free : QFree D V q)
    (far : x ∉ ball D V t (q-1)) : QFree (swap D x y t) V q :=
  qfree_sub swap_le_addArc (addArc_free hx free far)

theorem outN_swap_other {x y t v : ℕ} (e : v ≠ x) : outN (swap D x y t) V v = outN D V v := by
  ext w; simp only [mem_outN, swap, e, ite_false]

theorem outN_swap_self {x y t : ℕ} (ht : t ∈ V) (hxt : D x t = false) (hy : y ∈ outN D V x) :
    outN (swap D x y t) V x = insert t ((outN D V x).erase y) := by
  have yt : y ≠ t := by rintro rfl; rw [(mem_outN.mp hy).2] at hxt; exact absurd hxt (by simp)
  ext w
  simp only [mem_outN, swap, ite_true, mem_insert, mem_erase]
  by_cases h1 : w = t
  · subst h1; simp [ht]
  · by_cases h2 : w = y
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem swap_card {x y t : ℕ} (ht : t ∈ V) (hxt : D x t = false) (hy : y ∈ outN D V x) :
    (outN (swap D x y t) V x).card = (outN D V x).card := by
  rw [outN_swap_self ht hxt hy, card_insert_of_notMem, card_erase_of_mem hy]
  · have := card_pos.mpr ⟨y, hy⟩; omega
  · intro h
    have := (mem_outN.mp (mem_of_mem_erase h)).2
    rw [hxt] at this; exact absurd this (by simp)

/-- **Swap keeps the out-degrees.** -/
theorem swap_degree {s x y t : ℕ} (ht : t ∈ V) (hxt : D x t = false) (hy : y ∈ outN D V x)
    (degree : ∀ v ∈ V, s ≤ (outN D V v).card) : ∀ v ∈ V, s ≤ (outN (swap D x y t) V v).card := by
  intro v hv
  by_cases e : v = x
  · subst e; rw [swap_card ht hxt hy]; exact degree v hv
  · rw [outN_swap_other e]; exact degree v hv

/-- **The swapped fifth-strip top host is rigid again.** -/
theorem rigid_swap_of_top {a : ℕ} (ha : 2 ≤ a) (L : LedgerFloors a) (tc : Top a ((2*a+7)*(a+7)))
    (free : QFree D V (2*a+7)) (degree : ∀ v ∈ V, a+7 ≤ (outN D V v).card)
    (size : V.card = (2*a+7)*(a+7)) {x y t : ℕ} (hx : x ∈ V) (ht : t ∈ V)
    (hxt : D x t = false) (hy : y ∈ outN D V x) (far : x ∉ ball D V t (2*a+7-1)) :
    Rigid (swap D x y t) V (2*a+7) (a+7) (a+3) :=
  rigid_of_top ha L tc (swap_free hx free far) (swap_degree ht hxt hy degree) size

end

#print axioms rigid_of_top
#print axioms rev_inner
#print axioms rev_outer
#print axioms part_outer
#print axioms part_inner
#print axioms dich
#print axioms antipode_symm
#print axioms antipode_card
#print axioms diameter
#print axioms arc_return
#print axioms arc_return_walk
#print axioms in_layer_q
#print axioms rev_tail
#print axioms stuck_row_far
#print axioms stuck_row_iff
#print axioms stuck_row_heads
#print axioms swap_free
#print axioms swap_degree
#print axioms rigid_swap_of_top

/-! ## Part 2 tools -/

/-! ### Route (v): transfer to a lower degree -/

theorem outN_sdiff {D : CH.Digraph} {V S : Finset ℕ} {w : ℕ} :
    outN D (V \ S) w = outN D V w \ S := by
  ext x; simp only [mem_outN, mem_sdiff]; tauto

/-- **Transfer.** Removing a set `S` that no outside vertex heads more than `t` times keeps
`q`-freeness and leaves out-degree at least `s - t`. -/
theorem transfer {D : CH.Digraph} {V S : Finset ℕ} {q s t : ℕ} (free : QFree D V q)
    (degree : ∀ v ∈ V, s ≤ (outN D V v).card)
    (few : ∀ w ∈ V \ S, (outN D V w ∩ S).card ≤ t) :
    QFree D (V \ S) q ∧ ∀ w ∈ V \ S, s - t ≤ (outN D (V \ S) w).card := by
  refine ⟨free.mono_set sdiff_subset, fun w hw => ?_⟩
  rw [outN_sdiff]
  have e := card_sdiff_add_card_inter (outN D V w) S
  have := few w hw
  have := degree w (mem_sdiff.mp hw).1
  omega

/-- **Transfer to an order bound.** If every nonempty `q`-free host of degree `s - t` has at
least `L` labels, then `L ≤ |V| - |S|`. -/
theorem transfer_order {D : CH.Digraph} {V S : Finset ℕ} {q s t L : ℕ} (free : QFree D V q)
    (degree : ∀ v ∈ V, s ≤ (outN D V v).card) (hS : S ⊆ V) (ne : (V \ S).Nonempty)
    (few : ∀ w ∈ V \ S, (outN D V w ∩ S).card ≤ t)
    (order : MixedRadiusCompletion.Order q (s - t) L) : L + S.card ≤ V.card := by
  obtain ⟨f, d⟩ := transfer free degree few
  have := order D (V \ S) f d ne
  rw [card_sdiff_of_subset hS] at this
  have := card_le_card hS
  omega

/-- **Route (v) closes the fifth-strip top order** (any parity, `a ≥ 1`, no rigidity used) once
a set `S` of at least `q` labels is found that no outside vertex heads twice. -/
theorem fifth_top_false_of_sparse {a : ℕ} (ha : 1 ≤ a) {D : CH.Digraph} {V S : Finset ℕ}
    (free : QFree D V (2*a+7)) (degree : ∀ v ∈ V, a+7 ≤ (outN D V v).card)
    (size : V.card = (2*a+7)*(a+7)) (hS : S ⊆ V) (big : 2*a+7 ≤ S.card)
    (ne : (V \ S).Nonempty) (few : ∀ w ∈ V \ S, (outN D V w ∩ S).card ≤ 1) : False := by
  have h := transfer_order (t := 1) free degree hS ne few (low_order ha)
  have e : (2*a+7)*(a+7) = (2*a+7)*(a+6) + (2*a+7) := by ring
  omega

/-! ### Route (iv): a narrow root closes a rigid host -/

/-- **A narrow root is impossible.** In a rigid host (`0 < s < q`, `s/2 + i ≤ q`, `1 ≤ i`), no
root has all of its first `i` layers of width at most `s`. Equivalently, every root has a layer
of width `≥ s + 1` among its first `i` layers. -/
theorem narrow_root_false {D : CH.Digraph} {V : Finset ℕ} {q s i : ℕ} (R : Rigid D V q s i)
    (hs : 0 < s) (hsq : s < q) (height : s/2 + i ≤ q) (hi : 1 ≤ i) {y : ℕ} (hy : y ∈ V)
    (narrow : ∀ j, 1 ≤ j → j ≤ i → (layer D V j y).card ≤ s) : False := by
  have up : ∀ k ≤ i, (ball D V y k).card ≤ s*k + 1 := by
    intro k
    induction k with
    | zero => intro _; rw [ShapeClimbRoot.ball_zero_eq hy]; simp
    | succ k ih =>
      intro hk
      have e := card_ball_succ (D := D) (V := V) (u := y) k
      have := narrow (k+1) (by omega) hk
      have := ih (by omega)
      have : s*(k+1) = s*k + s := by ring
      omega
  exact FifthStripAllParity.flat_root_false R.free hs hsq height (by omega) (by rw [R.odd]; omega)
    R.degree hy (fun k hk => le_antisymm (up k hk) (R.floor k hk y hy))
    (by rw [R.outer y hy])

/-- **Seymour's tight root** for even `i = 2k`: some root has an exact `k`-ball. -/
theorem seymour_tight_root {D : CH.Digraph} {V : Finset ℕ} {q s i k : ℕ} (R : Rigid D V q s i)
    (hk : i = 2*k) (ne : V.Nonempty) : ∃ y ∈ V, (ball D V y k).card = s*k + 1 := by
  by_contra h
  push Not at h
  have h2 := reach_seymour (k := k) (f := s*k+2) (A := s*i+1) R.free (by rw [R.odd]; omega) ne
    (fun v hv => by have := R.floor k (by omega) v hv; have := h v hv; omega)
    (fun v hv => by rw [← hk, R.inner v hv])
  have : s*i = 2*(s*k) := by rw [hk]; ring
  omega

#print axioms transfer
#print axioms transfer_order
#print axioms fifth_top_false_of_sparse
#print axioms narrow_root_false
#print axioms seymour_tight_root
end LeanCH.BR.RigidHost
