import checkpoints.shen_extension.ThinSuppliers

/-!
# One-head rows of small `q`-free sets

Setting: a finite set `S`, `QFree D S q`, every row of `S` has at least one head inside `S`.
A *one-head row* has exactly one head inside `S` (`ThinSuppliers.lone`; with minimum out-degree
one, "at most one" is "exactly one", `mem_lone_iff`). A row is *good* (`good`) when it is a
one-head row whose unique head (`ThinSuppliers.hd`) is again a one-head row.

* A1 `one_head_count` (generic, `1 ≤ q`, `|S| ≤ 2q`): at least `2q + 2 - |S|` one-head rows.
  This is exactly `ThinSuppliers.lone_count`, restated. `one_head_six`: at `q = 6`, `|S| ≤ 9`,
  at least `14 - |S|`.
* A2 `lone_within` (generic, `1 ≤ q`, `k ≤ q`, `|S| ≤ q + k + 1`, `|S| ≤ 2q`): every row reaches
  a one-head row within `k` steps inside `S`. Proof: the private-head completion of
  `ThinSuppliers` has minimum out-degree two, so its `k`-ball has `2k + 1` labels; if the
  `k`-ball avoided the one-head rows it would be a ball of `S` among the at most
  `2|S| - 2q - 2 ≤ 2k` rows with two heads. `lone_two_six`: at `q = 6`, `|S| ≤ 9`, within two
  steps (the paper's A2).
* `in_card` (generic, `2 ≤ q`): a row with two heads has at most `|S| - q - 1` in-neighbours in
  `S` (its `(q-1)`-ball has `q + 1` labels: three at radius one, then growth or a closed ball).
* A3 `good_count` (generic, `2 ≤ q`, `|S| ≤ q + 2`): at least `q - 1` good rows. `good_six`:
  at `q = 6`, `|S| ≤ 8`, at least five.
  The proof differs from the paper's shortest-cycle argument. With `N` the rows with two heads
  (`|N| ≤ 2|S| - 2q - 2`) and `B` the one-head rows whose head is in `N`,
  `|good| = |S| - |N| - |B|` and `|B| ≤ |N| (|S| - q - 1)` (`in_card`). This settles every case
  but `|S| = q + 2`, `|N| = 2`, `|B| = 2` (`hard_case`): there the two heads `a`, `b` of `N`
  have in-degree one (`p → a`, `p' → b`), the one-head rows form chains (`hd` iterated, `Exit`)
  leading to `a` or `b`; a head of `a` cannot lead back to `a` (a closed walk of length at most
  `q`), so both heads of `a` lead to `b` and both heads of `b` lead to `a`; the chains are
  disjoint and the shorter of two chains is shorter than their union (`pair_min`), so
  `a → x ⇝ b → y ⇝ a` has length at most `q`.
  Not proved here: the count `2` at `|S| = q + 3`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.OneHead
open Finset BRq2 BRq3 ThinSuppliers

variable {D : CH.Digraph} {q : ℕ} {S : Finset ℕ}

/-! ### A1 -/

theorem mem_lone_iff (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card) {v : ℕ} :
    v ∈ lone D S ↔ v ∈ S ∧ (outN D S v).card = 1 := by
  rw [mem_lone]
  constructor
  · rintro ⟨h, le⟩
    exact ⟨h, le_antisymm le (deg v h)⟩
  · rintro ⟨h, e⟩
    exact ⟨h, e.le⟩

/-- **A1.** At least `2q + 2 - |S|` one-head rows (`ThinSuppliers.lone_count`). -/
theorem one_head_count (free : QFree D S q) (hq : 1 ≤ q) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card)
    (ne : S.Nonempty) (small : S.card ≤ 2 * q) : 2 * q + 2 ≤ S.card + (lone D S).card :=
  lone_count free hq deg ne small

/-- **A1 at `q = 6`.** On at most nine labels, at least `14 - |S|` one-head rows. -/
theorem one_head_six (free : QFree D S 6) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card)
    (ne : S.Nonempty) (small : S.card ≤ 9) : 14 ≤ S.card + (lone D S).card :=
  lone_count free (by norm_num) deg ne (by omega)

/-! ### A2 -/

/-- **A2 (generic).** `1 ≤ q`, `k ≤ q`, `|S| ≤ q + k + 1`, `|S| ≤ 2q`: every row reaches a
one-head row within `k` steps inside `S`. -/
theorem lone_within (free : QFree D S q) (hq : 1 ≤ q) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card)
    {k : ℕ} (hk : k ≤ q) (small : S.card ≤ q + k + 1) (small2 : S.card ≤ 2 * q) {x : ℕ}
    (hx : x ∈ S) : ∃ c ∈ ball D S x k, c ∈ lone D S := by
  by_contra none
  push Not at none
  have sub := ball_lift hx none
  have big := BRq2.ball_growth q hq _ _ (clone_free deg free) (clone_out2 deg) x
    (mem_union_left _ hx) k hk
  have inS : ball D S x k ⊆ S \ lone D S :=
    fun c hc => mem_sdiff.mpr ⟨ball_subset hc, none c hc⟩
  have c1 := card_le_card sub
  have c2 := card_le_card inS
  rw [card_sdiff_of_subset lone_subset] at c2
  have count := lone_count free hq deg ⟨x, hx⟩ small2
  have := card_le_card (lone_subset (D := D) (S := S))
  omega

/-- **A2 at `q = 6`.** On at most nine labels every row reaches a one-head row within two
steps. -/
theorem lone_two_six (free : QFree D S 6) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card)
    (small : S.card ≤ 9) {x : ℕ} (hx : x ∈ S) : ∃ c ∈ ball D S x 2, c ∈ lone D S :=
  lone_within free (by norm_num) deg (by norm_num) (by omega) (by omega) hx

/-! ### In-degree of a row with two heads -/

/-- In-neighbours inside `S`. -/
noncomputable def inN (D : CH.Digraph) (S : Finset ℕ) (v : ℕ) : Finset ℕ :=
  S.filter (fun a => D a v = true)

theorem mem_inN {v a : ℕ} : a ∈ inN D S v ↔ a ∈ S ∧ D a v = true := mem_filter

/-- A row with two heads has a `(q-1)`-ball of at least `q + 1` labels (`2 ≤ q`). -/
theorem wide_ball (free : QFree D S q) (hq : 2 ≤ q) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card)
    {v : ℕ} (hv : v ∈ S) (two : 2 ≤ (outN D S v).card) : q + 1 ≤ (ball D S v (q - 1)).card := by
  rcases TubeAtCutoff.closed_or_grow (D := D) (S := S) (v := v) (a := 1) (M := q - 2) with
    ⟨j, -, hjq, cl⟩ | g
  · have T : ball D S v j ⊆ S := ball_subset
    have big := ReachLedger.closed_chain free T ⟨v, self_mem_ball hv⟩ (fun x hx => by
      obtain ⟨y, hy⟩ := card_pos.mp (show 0 < (outN D S x).card by have := deg x (T hx); omega)
      obtain ⟨yS, xy⟩ := mem_outN.mp hy
      exact ⟨y, cl x hx y yS xy, xy⟩)
    have := card_le_card (ball_mono_radius (D := D) (W := S) (u := v) (show j ≤ q - 1 by omega))
    omega
  · rw [show 1 + (q - 2) = q - 1 by omega] at g
    have b1 := ReachLedger.ball_one free (by omega) hv
    omega

/-- **In-degree.** A row with two heads has at most `|S| - q - 1` in-neighbours (`2 ≤ q`). -/
theorem in_card (free : QFree D S q) (hq : 2 ≤ q) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card)
    {v : ℕ} (hv : v ∈ S) (two : 2 ≤ (outN D S v).card) : (inN D S v).card + q + 1 ≤ S.card := by
  have B := wide_ball free hq deg hv two
  have sub : inN D S v ⊆ S \ ball D S v (q - 1) := by
    intro a ha
    obtain ⟨aS, av⟩ := mem_inN.mp ha
    exact mem_sdiff.mpr ⟨aS, fun h => no_back_arc free hv h (by omega) av⟩
  have := card_le_card sub
  rw [card_sdiff_of_subset ball_subset] at this
  have := card_le_card (ball_subset (D := D) (W := S) (u := v) (k := q - 1))
  omega

theorem two_of_not_lone {v : ℕ} (hv : v ∈ S) (hn : v ∉ lone D S) : 2 ≤ (outN D S v).card := by
  by_contra h
  exact hn (mem_lone.mpr ⟨hv, by omega⟩)

/-! ### Chains of one-head rows -/

/-- `v` leaves the one-head rows after exactly `k` steps of `hd`. -/
def Exit (D : CH.Digraph) (S : Finset ℕ) (v k : ℕ) : Prop :=
  (∀ i < k, (hd D S)^[i] v ∈ lone D S) ∧ (hd D S)^[k] v ∉ lone D S

/-- The first `k` labels of the `hd`-chain from `v`. -/
noncomputable def chain (D : CH.Digraph) (S : Finset ℕ) (v k : ℕ) : Finset ℕ :=
  (range k).image (fun i => (hd D S)^[i] v)

theorem iter_walk (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card) {v : ℕ} :
    ∀ n, (∀ i < n, (hd D S)^[i] v ∈ lone D S) → Walk D S v ((hd D S)^[n] v) n := by
  intro n
  induction n with
  | zero => intro _; exact .refl v
  | succ n ih =>
    intro h
    have w := ih (fun i hi => h i (by omega))
    obtain ⟨mS, arc⟩ := hd_mem deg (h n (by omega))
    rw [Function.iterate_succ_apply']
    exact w.snoc mS arc

theorem iter_ne (free : QFree D S q) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card) {v i j : ℕ}
    (hij : i < j) (hjq : j - i ≤ q) (h : ∀ t < j, (hd D S)^[t] v ∈ lone D S) :
    (hd D S)^[i] v ≠ (hd D S)^[j] v := by
  intro e
  have wl : ∀ t < j - i, (hd D S)^[t] ((hd D S)^[i] v) ∈ lone D S := by
    intro t ht
    rw [← Function.iterate_add_apply]
    exact h (t + i) (by omega)
  have walk := iter_walk deg (v := (hd D S)^[i] v) (j - i) wl
  rw [← Function.iterate_add_apply, show j - i + i = j by omega, ← e] at walk
  exact free _ (j - i) (by omega) hjq walk

/-- A chain inside the one-head rows has fewer than `|lone|` steps (`|lone| ≤ q`). -/
theorem stay_lt (free : QFree D S q) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card)
    (small : (lone D S).card ≤ q) {v n : ℕ} (h : ∀ i ≤ n, (hd D S)^[i] v ∈ lone D S) :
    n < (lone D S).card := by
  classical
  by_contra big
  push Not at big
  obtain ⟨i, hi, j, hj, ne, e⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := range ((lone D S).card + 1)) (t := lone D S) (f := fun i => (hd D S)^[i] v)
    (by simp) (by intro i hi; exact h i (by simp at hi; omega))
  simp only [mem_range] at hi hj
  rcases lt_or_gt_of_ne ne with lt | lt
  · exact iter_ne free deg lt (by omega) (fun t ht => h t (by omega)) e
  · exact iter_ne free deg lt (by omega) (fun t ht => h t (by omega)) e.symm

theorem exit_exists (free : QFree D S q) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card)
    (small : (lone D S).card ≤ q) {v : ℕ} (hv : v ∈ lone D S) :
    ∃ k, Exit D S v k ∧ 1 ≤ k ∧ k ≤ (lone D S).card := by
  classical
  have ex : ∃ k, (hd D S)^[k] v ∉ lone D S := by
    by_contra hall
    push Not at hall
    have := stay_lt free deg small (v := v) (n := (lone D S).card) (fun i _ => hall i)
    omega
  refine ⟨Nat.find ex, ⟨fun i hi => ?_, Nat.find_spec ex⟩, ?_, ?_⟩
  · have := Nat.find_min ex hi
    push Not at this
    exact this
  · by_contra h0
    have e : Nat.find ex = 0 := by omega
    have := Nat.find_spec ex
    rw [e] at this
    exact this hv
  · by_contra big
    push Not at big
    have := stay_lt free deg small (v := v) (n := Nat.find ex - 1) (fun i hi => by
      have := Nat.find_min ex (show i < Nat.find ex by omega)
      push Not at this
      exact this)
    omega

theorem exit_unique {v k k' : ℕ} (e : Exit D S v k) (e' : Exit D S v k') : k = k' := by
  by_contra ne
  rcases lt_or_gt_of_ne ne with h | h
  · exact e.2 (e'.1 k h)
  · exact e'.2 (e.1 k' h)

theorem exit_shift {v k i : ℕ} (e : Exit D S v k) (hi : i ≤ k) :
    Exit D S ((hd D S)^[i] v) (k - i) := by
  refine ⟨fun t ht => ?_, ?_⟩
  · rw [← Function.iterate_add_apply]
    exact e.1 (t + i) (by omega)
  · rw [← Function.iterate_add_apply, show k - i + i = k by omega]
    exact e.2

theorem exit_mem (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card) {v k : ℕ} (e : Exit D S v k)
    (hk : 1 ≤ k) : (hd D S)^[k] v ∈ S := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Function.iterate_succ_apply']
  exact (hd_mem deg (e.1 j (by omega))).1

theorem chain_sub {v k : ℕ} (e : Exit D S v k) : chain D S v k ⊆ lone D S := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hw
  exact e.1 i (mem_range.mp hi)

theorem chain_card (free : QFree D S q) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card) {v k : ℕ}
    (e : Exit D S v k) (hk : k ≤ q) : (chain D S v k).card = k := by
  rw [chain, card_image_of_injOn, card_range]
  intro i hi j hj eq
  simp only [coe_range, Set.mem_Iio] at hi hj
  by_contra ne
  rcases lt_or_gt_of_ne ne with lt | lt
  · exact iter_ne free deg lt (by omega) (fun t ht => e.1 t (by omega)) eq
  · exact iter_ne free deg lt (by omega) (fun t ht => e.1 t (by omega)) eq.symm

theorem chain_disjoint {x y kx ky : ℕ} (e : Exit D S x kx) (e' : Exit D S y ky)
    (ne : (hd D S)^[kx] x ≠ (hd D S)^[ky] y) : Disjoint (chain D S x kx) (chain D S y ky) := by
  rw [disjoint_left]
  intro w hw hw'
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hw
  obtain ⟨j, hj, ej⟩ := mem_image.mp hw'
  have ej' : (hd D S)^[j] y = (hd D S)^[i] x := ej
  rw [mem_range] at hi hj
  have s1 := exit_shift e hi.le
  have s2 := exit_shift e' hj.le
  rw [ej'] at s2
  have u := exit_unique s1 s2
  apply ne
  calc (hd D S)^[kx] x = (hd D S)^[kx - i] ((hd D S)^[i] x) := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hi.le]
    _ = (hd D S)^[ky - j] ((hd D S)^[j] y) := by rw [u, ej']
    _ = (hd D S)^[ky] y := by rw [← Function.iterate_add_apply, Nat.sub_add_cancel hj.le]

/-- The shorter of two chains is shorter than their union. -/
theorem pair_min (free : QFree D S q) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card) {x1 x2 k1 k2 : ℕ}
    (e1 : Exit D S x1 k1) (e2 : Exit D S x2 k2) (k1q : k1 ≤ q) (h2 : 1 ≤ k2) (ne : x1 ≠ x2)
    (le : k2 ≤ k1) : k2 + 1 ≤ (chain D S x1 k1 ∪ chain D S x2 k2).card := by
  classical
  have c1 := chain_card free deg e1 k1q
  have u1 := card_le_card (subset_union_left (s₁ := chain D S x1 k1) (s₂ := chain D S x2 k2))
  by_cases hx : x2 ∈ chain D S x1 k1
  · obtain ⟨i, hi, ei⟩ := mem_image.mp hx
    have ei' : (hd D S)^[i] x1 = x2 := ei
    rw [mem_range] at hi
    have i0 : i ≠ 0 := by
      rintro rfl
      exact ne (by simpa using ei')
    have s := exit_shift e1 hi.le
    rw [ei'] at s
    have := exit_unique e2 s
    omega
  · have sub : insert x2 (chain D S x1 k1) ⊆ chain D S x1 k1 ∪ chain D S x2 k2 := by
      intro w hw
      rcases mem_insert.mp hw with rfl | h
      · exact mem_union_right _ (mem_image.mpr ⟨0, mem_range.mpr (by omega), rfl⟩)
      · exact mem_union_left _ h
    have := card_le_card sub
    rw [card_insert_of_notMem hx] at this
    omega

theorem best_of_two (free : QFree D S q) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card)
    {x1 x2 k1 k2 : ℕ} (e1 : Exit D S x1 k1) (e2 : Exit D S x2 k2) (h1 : 1 ≤ k1) (h2 : 1 ≤ k2)
    (k1q : k1 ≤ q) (k2q : k2 ≤ q) (ne : x1 ≠ x2) :
    k1 + 1 ≤ (chain D S x1 k1 ∪ chain D S x2 k2).card ∨
      k2 + 1 ≤ (chain D S x1 k1 ∪ chain D S x2 k2).card := by
  rcases le_total k2 k1 with h | h
  · exact Or.inr (pair_min free deg e1 e2 k1q h2 ne h)
  · left
    have := pair_min free deg e2 e1 k2q h1 (Ne.symm ne) h
    rwa [union_comm] at this

/-! ### A3 -/

/-- One-head rows whose unique head is again a one-head row. -/
noncomputable def good (D : CH.Digraph) (S : Finset ℕ) : Finset ℕ :=
  (lone D S).filter (fun p => hd D S p ∈ lone D S)

theorem mem_good {p : ℕ} : p ∈ good D S ↔ p ∈ lone D S ∧ hd D S p ∈ lone D S := mem_filter

theorem good_subset : good D S ⊆ lone D S := filter_subset _ _

/-- In the hard case a head of `a` cannot lead back to `a`. -/
theorem far_exit (free : QFree D S q) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card)
    (Lc : (lone D S).card = q) {a b p : ℕ} (hp : p ∈ lone D S) (pb : hd D S p = b)
    (bn : b ∉ lone D S) (ab : a ≠ b) {x k : ℕ} (e : Exit D S x k) (k1 : 1 ≤ k)
    (kq : k ≤ q) (xS : x ∈ S) (ax : D a x = true) : (hd D S)^[k] x ≠ a := by
  classical
  intro back
  have kq' : k + 1 ≤ q := by
    by_contra h
    have kk : k = q := by omega
    have cc := chain_card free deg e kq
    have eq : chain D S x k = lone D S := eq_of_subset_of_card_le (chain_sub e) (by omega)
    have pc : p ∈ chain D S x k := by rw [eq]; exact hp
    obtain ⟨i, hi, ei⟩ := mem_image.mp pc
    have ei' : (hd D S)^[i] x = p := ei
    rw [mem_range] at hi
    have nxt : (hd D S)^[i + 1] x = b := by
      rw [Function.iterate_succ_apply', ei', pb]
    by_cases hlt : i + 1 < k
    · exact bn (nxt ▸ e.1 (i + 1) hlt)
    · have : i + 1 = k := by omega
      rw [this, back] at nxt
      exact ab nxt
  have w : Walk D S a ((hd D S)^[k] x) (k + 1) := .step xS ax (iter_walk deg k e.1)
  rw [back] at w
  exact free a (k + 1) (by omega) kq' w

/-- **The hard case.** `|S| = q + 2` with two rows of two heads: at most one one-head row has
its head among them. -/
theorem hard_case (free : QFree D S q) (hq : 2 ≤ q) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card)
    (hS : S.card = q + 2) (hN : (S \ lone D S).card = 2) {p1 p2 : ℕ} (h1 : p1 ∈ lone D S)
    (h2 : p2 ∈ lone D S) (n1 : hd D S p1 ∉ lone D S) (n2 : hd D S p2 ∉ lone D S) : p1 = p2 := by
  classical
  by_contra ne
  have Lc : (lone D S).card = q := by
    rw [card_sdiff_of_subset lone_subset] at hN
    omega
  have small : (lone D S).card ≤ q := Lc.le
  obtain ⟨a, ha⟩ : ∃ a, hd D S p1 = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, hd D S p2 = b := ⟨_, rfl⟩
  rw [ha] at n1
  rw [hb] at n2
  obtain ⟨aS, pa⟩ := hd_mem deg h1
  obtain ⟨bS, pb⟩ := hd_mem deg h2
  rw [ha] at aS pa
  rw [hb] at bS pb
  have in1 : ∀ v ∈ S, v ∉ lone D S → ∀ c ∈ S, ∀ c' ∈ S, D c v = true → D c' v = true → c = c' := by
    intro v hv hn c hc c' hc' cv c'v
    have := in_card free hq deg hv (two_of_not_lone hv hn)
    exact card_le_one.mp (by omega) c (mem_inN.mpr ⟨hc, cv⟩) c' (mem_inN.mpr ⟨hc', c'v⟩)
  have p1S := lone_subset h1
  have p2S := lone_subset h2
  have ab : a ≠ b := by
    intro e
    rw [e] at pa
    exact ne (in1 b bS n2 p1 p1S p2 p2S pa pb)
  have Nab : ∀ v ∈ S, v ∉ lone D S → v = a ∨ v = b := by
    intro v hv hn
    have sub : ({a, b} : Finset ℕ) ⊆ S \ lone D S := by
      intro w hw
      rcases mem_insert.mp hw with rfl | hw
      · exact mem_sdiff.mpr ⟨aS, n1⟩
      · rw [mem_singleton.mp hw]
        exact mem_sdiff.mpr ⟨bS, n2⟩
    have eq := eq_of_subset_of_card_le sub (by rw [hN, card_pair ab])
    have : v ∈ ({a, b} : Finset ℕ) := by rw [eq]; exact mem_sdiff.mpr ⟨hv, hn⟩
    simpa using this
  have Nba : ∀ w ∈ S, w ∉ lone D S → w = b ∨ w = a := fun w hw hn => (Nab w hw hn).symm
  -- two heads each
  obtain ⟨x1, hx1, x2, hx2, nx⟩ := one_lt_card.mp (show 1 < (outN D S a).card by
    have := two_of_not_lone aS n1; omega)
  obtain ⟨y1, hy1, y2, hy2, ny⟩ := one_lt_card.mp (show 1 < (outN D S b).card by
    have := two_of_not_lone bS n2; omega)
  -- exits
  have exitTo : ∀ c c' p', c ∈ S → c ∉ lone D S → c' ∉ lone D S → c ≠ c' → p' ∈ lone D S →
      hd D S p' = c' → (∀ w ∈ S, w ∉ lone D S → w = c ∨ w = c') →
      ∀ x ∈ outN D S c, ∃ k, Exit D S x k ∧ 1 ≤ k ∧ k ≤ q ∧ (hd D S)^[k] x = c' := by
    intro c c' p' cS cn c'n cc' hp' pc' two x hx
    obtain ⟨xS, cx⟩ := mem_outN.mp hx
    have xl : x ∈ lone D S := by
      by_contra xn
      rcases two x xS xn with h | h
      · rw [h] at cx
        exact loopfree free (by omega) cS cx
      · -- `c → c'`, but the only in-neighbour of `c'` is `p'`
        rw [h] at cx xS
        have := in1 c' xS c'n c cS p' (lone_subset hp') cx
          (by have := (hd_mem deg hp').2; rwa [pc'] at this)
        exact cn (by rw [this]; exact hp')
    obtain ⟨k, e, k1, kL⟩ := exit_exists free deg small xl
    refine ⟨k, e, k1, by omega, ?_⟩
    rcases two _ (exit_mem deg e k1) e.2 with h | h
    · exact absurd h (far_exit free deg Lc hp' pc' c'n cc' e k1 (by omega) xS cx)
    · exact h
  obtain ⟨kx1, ex1, kx1p, kx1q, bx1⟩ := exitTo a b p2 aS n1 n2 ab h2 hb Nab x1 hx1
  obtain ⟨kx2, ex2, kx2p, kx2q, bx2⟩ := exitTo a b p2 aS n1 n2 ab h2 hb Nab x2 hx2
  obtain ⟨ky1, ey1, ky1p, ky1q, ay1⟩ := exitTo b a p1 bS n2 n1 (Ne.symm ab) h1 ha Nba y1 hy1
  obtain ⟨ky2, ey2, ky2p, ky2q, ay2⟩ := exitTo b a p1 bS n2 n1 (Ne.symm ab) h1 ha Nba y2 hy2
  set CX := chain D S x1 kx1 ∪ chain D S x2 kx2 with hCX
  set CY := chain D S y1 ky1 ∪ chain D S y2 ky2 with hCY
  have dis : Disjoint CX CY := by
    have d : ∀ x kx y ky, Exit D S x kx → (hd D S)^[kx] x = b → Exit D S y ky →
        (hd D S)^[ky] y = a → Disjoint (chain D S x kx) (chain D S y ky) :=
      fun x kx y ky e hx e' hy => chain_disjoint e e' (by rw [hx, hy]; exact Ne.symm ab)
    rw [hCX, hCY, disjoint_union_left, disjoint_union_right, disjoint_union_right]
    exact ⟨⟨d _ _ _ _ ex1 bx1 ey1 ay1, d _ _ _ _ ex1 bx1 ey2 ay2⟩,
      ⟨d _ _ _ _ ex2 bx2 ey1 ay1, d _ _ _ _ ex2 bx2 ey2 ay2⟩⟩
  have inL : CX ∪ CY ⊆ lone D S :=
    union_subset (union_subset (chain_sub ex1) (chain_sub ex2))
      (union_subset (chain_sub ey1) (chain_sub ey2))
  have tot := card_le_card inL
  rw [card_union_of_disjoint dis, Lc] at tot
  -- the short closed walk `a → x ⇝ b → y ⇝ a`
  have bestX : ∃ x k, x ∈ outN D S a ∧ Exit D S x k ∧ (hd D S)^[k] x = b ∧ k + 1 ≤ CX.card := by
    rcases best_of_two free deg ex1 ex2 kx1p kx2p kx1q kx2q nx with h | h
    · exact ⟨x1, kx1, hx1, ex1, bx1, h⟩
    · exact ⟨x2, kx2, hx2, ex2, bx2, h⟩
  have bestY : ∃ y k, y ∈ outN D S b ∧ Exit D S y k ∧ (hd D S)^[k] y = a ∧ k + 1 ≤ CY.card := by
    rcases best_of_two free deg ey1 ey2 ky1p ky2p ky1q ky2q ny with h | h
    · exact ⟨y1, ky1, hy1, ey1, ay1, h⟩
    · exact ⟨y2, ky2, hy2, ey2, ay2, h⟩
  obtain ⟨x, kx, hx, ex, bx, cx⟩ := bestX
  obtain ⟨y, ky, hy, ey, ay, cy⟩ := bestY
  obtain ⟨xS, axx⟩ := mem_outN.mp hx
  obtain ⟨yS, byy⟩ := mem_outN.mp hy
  have wx : Walk D S a b (kx + 1) := by
    have := Walk.step xS axx (iter_walk deg kx ex.1)
    rwa [bx] at this
  have wy : Walk D S b a (ky + 1) := by
    have := Walk.step yS byy (iter_walk deg ky ey.1)
    rwa [ay] at this
  exact free a (kx + 1 + (ky + 1)) (by omega) (by omega) (wx.append wy)

/-- **A3 (generic).** `2 ≤ q`, `|S| ≤ q + 2`: at least `q - 1` good rows. -/
theorem good_count (free : QFree D S q) (hq : 2 ≤ q) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card)
    (ne : S.Nonempty) (small : S.card ≤ q + 2) : q ≤ (good D S).card + 1 := by
  classical
  have count := lone_count free (by omega) deg ne (by omega)
  have LS := card_le_card (lone_subset (D := D) (S := S))
  have Nc : (S \ lone D S).card + (lone D S).card = S.card := by
    rw [card_sdiff_of_subset lone_subset]
    omega
  set B := (lone D S).filter (fun p => hd D S p ∉ lone D S) with hB
  have split : (good D S).card + B.card = (lone D S).card :=
    card_filter_add_card_filter_not (s := lone D S) (fun p => hd D S p ∈ lone D S)
  have Bsub : B ⊆ (S \ lone D S).biUnion (inN D S) := by
    intro p hp
    obtain ⟨pL, hpn⟩ := mem_filter.mp hp
    obtain ⟨hS, arc⟩ := hd_mem deg pL
    exact mem_biUnion.mpr ⟨hd D S p, mem_sdiff.mpr ⟨hS, hpn⟩, mem_inN.mpr ⟨lone_subset pL, arc⟩⟩
  have Bc : B.card ≤ (S \ lone D S).card * (S.card - q - 1) := by
    calc B.card ≤ ((S \ lone D S).biUnion (inN D S)).card := card_le_card Bsub
      _ ≤ ∑ v ∈ S \ lone D S, (inN D S v).card := card_biUnion_le
      _ ≤ ∑ _v ∈ S \ lone D S, (S.card - q - 1) := sum_le_sum (fun v hv => by
          obtain ⟨vS, vn⟩ := mem_sdiff.mp hv
          have := in_card free hq deg vS (two_of_not_lone vS vn)
          omega)
      _ = (S \ lone D S).card * (S.card - q - 1) := by rw [sum_const, smul_eq_mul]
  by_cases top : S.card = q + 2
  · rw [top, show q + 2 - q - 1 = 1 by omega, mul_one] at Bc
    by_cases n2 : (S \ lone D S).card = 2
    · have B1 : B.card ≤ 1 := card_le_one.mpr (fun p hp p' hp' => by
        obtain ⟨pL, pn⟩ := mem_filter.mp hp
        obtain ⟨pL', pn'⟩ := mem_filter.mp hp'
        exact hard_case free hq deg top n2 pL pL' pn pn')
      omega
    · omega
  · have n0 : (S \ lone D S).card = 0 := by omega
    rw [n0, zero_mul] at Bc
    have big := ReachLedger.closed_chain free (subset_refl S) ne (fun x hx => by
      obtain ⟨y, hy⟩ := card_pos.mp (show 0 < (outN D S x).card by have := deg x hx; omega)
      obtain ⟨yS, xy⟩ := mem_outN.mp hy
      exact ⟨y, yS, xy⟩)
    omega

/-- **A3 at `q = 6`.** On at most eight labels, at least five good rows. -/
theorem good_six (free : QFree D S 6) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card)
    (ne : S.Nonempty) (small : S.card ≤ 8) : 5 ≤ (good D S).card := by
  have := good_count free (by norm_num) deg ne (by omega)
  omega

/-! ### A3 at `|S| = q + 3` -/

/-- In-neighbours lie outside the `(q-1)`-ball. -/
theorem in_le_ball (free : QFree D S q) (hq : 1 ≤ q) {v : ℕ} (hv : v ∈ S) :
    (inN D S v).card + (ball D S v (q - 1)).card ≤ S.card := by
  have sub : inN D S v ⊆ S \ ball D S v (q - 1) := by
    intro a ha
    obtain ⟨aS, av⟩ := mem_inN.mp ha
    exact mem_sdiff.mpr ⟨aS, fun h => no_back_arc free hv h (by omega) av⟩
  have := card_le_card sub
  rw [card_sdiff_of_subset ball_subset] at this
  have := card_le_card (ball_subset (D := D) (W := S) (u := v) (k := q - 1))
  omega

/-- A row with two heads has `|B_k| ≥ k + 2` for `1 ≤ k ≤ q - 1`. -/
theorem ball_two_heads (free : QFree D S q) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card) {v : ℕ}
    (hv : v ∈ S) (two : 2 ≤ (outN D S v).card) {k : ℕ} (hk1 : 1 ≤ k) (hk : k + 1 ≤ q) :
    k + 2 ≤ (ball D S v k).card := by
  rcases TubeAtCutoff.closed_or_grow (D := D) (S := S) (v := v) (a := 1) (M := k - 1) with
    ⟨j, -, hjk, cl⟩ | g
  · have T : ball D S v j ⊆ S := ball_subset
    have big := ReachLedger.closed_chain free T ⟨v, self_mem_ball hv⟩ (fun x hx => by
      obtain ⟨y, hy⟩ := card_pos.mp (show 0 < (outN D S x).card by have := deg x (T hx); omega)
      obtain ⟨yS, xy⟩ := mem_outN.mp hy
      exact ⟨y, cl x hx y yS xy, xy⟩)
    have := card_le_card (ball_mono_radius (D := D) (W := S) (u := v) (show j ≤ k by omega))
    omega
  · rw [show 1 + (k - 1) = k by omega] at g
    have b1 := ReachLedger.ball_one free (by omega) hv
    omega

/-- One step back: `|B_k(y)| + 1 ≤ |B_{k+1}(v)|` for an arc `v → y`, `k + 1 ≤ q`. -/
theorem ball_head (free : QFree D S q) {v y k : ℕ} (vS : v ∈ S) (yS : y ∈ S) (vy : D v y = true)
    (hk : k + 1 ≤ q) : (ball D S y k).card + 1 ≤ (ball D S v (k + 1)).card := by
  have nv : v ∉ ball D S y k := fun h => no_back_arc free yS h hk vy
  have sub : insert v (ball D S y k) ⊆ ball D S v (k + 1) :=
    insert_subset (self_mem_ball vS) (ReachLedger.ball_succ yS vy)
  have := card_le_card sub
  rwa [card_insert_of_notMem nv] at this

theorem orbit_walk {N : Finset ℕ} {τ : ℕ → ℕ} (maps : ∀ a ∈ N, τ a ∈ N)
    (step : ∀ a ∈ N, ∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ 2 ∧ Walk D S a (τ a) ℓ) :
    ∀ n, ∀ a ∈ N, τ^[n] a ∈ N ∧ ∃ ℓ, n ≤ ℓ ∧ ℓ ≤ 2 * n ∧ Walk D S a (τ^[n] a) ℓ := by
  intro n
  induction n with
  | zero => intro a ha; exact ⟨ha, 0, le_rfl, le_rfl, .refl a⟩
  | succ n ih =>
    intro a ha
    obtain ⟨m, ℓ, h1, h2, w⟩ := ih a ha
    obtain ⟨ℓ', h1', h2', w'⟩ := step _ m
    refine ⟨?_, ℓ + ℓ', by omega, by omega, ?_⟩
    · rw [Function.iterate_succ_apply']
      exact maps _ m
    · rw [Function.iterate_succ_apply']
      exact w.append w'

theorem orbit_ne (free : QFree D S q) {N : Finset ℕ} {τ : ℕ → ℕ} (maps : ∀ a ∈ N, τ a ∈ N)
    (step : ∀ a ∈ N, ∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ 2 ∧ Walk D S a (τ a) ℓ) {a : ℕ} (ha : a ∈ N) {i j : ℕ}
    (hij : i < j) (hq : 2 * (j - i) ≤ q) : τ^[i] a ≠ τ^[j] a := by
  intro e
  obtain ⟨m, -⟩ := orbit_walk maps step i a ha
  obtain ⟨-, ℓ, h1, h2, w⟩ := orbit_walk maps step (j - i) (τ^[i] a) m
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij.le, ← e] at w
  exact free _ ℓ (by omega) (by omega) w

/-- **A3 at `|S| = q + 3` (generic, `6 ≤ q`).** At least two good rows.

Proof. If at most one row is good, every row `a` with two heads has a head that is not good;
it is a row with two heads, or a one-head row whose head has two heads, so `a` reaches a row
`τ a` with two heads in one or two steps. The orbit `a, τ a, τ² a, τ³ a` has no repetition
(a closed walk of length at most `6 ≤ q`), and there are at most `4` rows with two heads
(`lone_count`), so exactly four, `τ` is a `4`-cycle, every row reached in one or two steps is
`τ a`, and `τ` is injective. Then every head of `a` is `τ a`, a one-head row whose head is
`τ a`, or the good row, whose in-degree is at most `2` (its `(q-1)`-ball has `q + 1` labels).
Counting heads of the four rows (`≥ 8`) against `q - 1` one-head rows, at least `8 - q` of them
point to `τ a` directly, and the `4`-cycle closes a walk of length `8 - (8 - q) = q`.
`6 ≤ q` enters only through orbit repetitions of length up to three (closed walks up to `6`). -/
theorem good_top (free : QFree D S q) (hq : 6 ≤ q) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card)
    (hS : S.card = q + 3) : 2 ≤ (good D S).card := by
  classical
  by_contra few
  push Not at few
  have gone : ∀ p ∈ good D S, ∀ p' ∈ good D S, p = p' := card_le_one.mp (by omega)
  have ne : S.Nonempty := card_pos.mp (by omega)
  have count := lone_count free (by omega) deg ne (by omega)
  have LS := card_le_card (lone_subset (D := D) (S := S))
  have GL := card_le_card (good_subset (D := D) (S := S))
  have Nc : (S \ lone D S).card + (lone D S).card = S.card := by
    rw [card_sdiff_of_subset lone_subset]
    omega
  set N := S \ lone D S with hN
  have mem_N : ∀ {v : ℕ}, v ∈ N ↔ v ∈ S ∧ v ∉ lone D S := by
    intro v
    rw [hN, mem_sdiff]
  set B := (lone D S).filter (fun p => hd D S p ∉ lone D S) with hB
  have split : (good D S).card + B.card = (lone D S).card :=
    card_filter_add_card_filter_not (s := lone D S) (fun p => hd D S p ∈ lone D S)
  -- some row has two heads
  have Nne : N.Nonempty := by
    by_contra e
    rw [not_nonempty_iff_eq_empty] at e
    have Bz : B = ∅ := filter_eq_empty_iff.mpr (fun p hp hn => by
      have : hd D S p ∈ N := mem_N.mpr ⟨(hd_mem deg hp).1, hn⟩
      rw [e] at this
      simp at this)
    have b0 : B.card = 0 := by rw [Bz]; rfl
    have n0 : N.card = 0 := by rw [e]; rfl
    omega
  -- a short successor among the rows with two heads
  have short : ∀ a ∈ N, ∃ b ∈ N, ∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ 2 ∧ Walk D S a b ℓ := by
    intro a ha
    obtain ⟨aS, an⟩ := mem_N.mp ha
    obtain ⟨x1, hx1, x2, hx2, nx⟩ := one_lt_card.mp (show 1 < (outN D S a).card by
      have := two_of_not_lone aS an; omega)
    have pick : ∃ x ∈ outN D S a, x ∉ good D S := by
      by_contra h
      push Not at h
      exact nx (gone x1 (h x1 hx1) x2 (h x2 hx2))
    obtain ⟨x, hx, xg⟩ := pick
    obtain ⟨xS, ax⟩ := mem_outN.mp hx
    by_cases xl : x ∈ lone D S
    · have hn : hd D S x ∉ lone D S := fun h => xg (mem_good.mpr ⟨xl, h⟩)
      obtain ⟨hS', xh⟩ := hd_mem deg xl
      exact ⟨hd D S x, mem_N.mpr ⟨hS', hn⟩, 2, by norm_num, le_rfl,
        .step xS ax (.step hS' xh (.refl _))⟩
    · exact ⟨x, mem_N.mpr ⟨xS, xl⟩, 1, le_rfl, by norm_num, .step xS ax (.refl _)⟩
  have ex : ∀ a, ∃ b, a ∈ N → b ∈ N ∧ ∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ 2 ∧ Walk D S a b ℓ := by
    intro a
    by_cases ha : a ∈ N
    · obtain ⟨b, hb, w⟩ := short a ha
      exact ⟨b, fun _ => ⟨hb, w⟩⟩
    · exact ⟨a, fun h => absurd h ha⟩
  choose τ hτ using ex
  have maps : ∀ a ∈ N, τ a ∈ N := fun a ha => (hτ a ha).1
  have step : ∀ a ∈ N, ∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ 2 ∧ Walk D S a (τ a) ℓ := fun a ha => (hτ a ha).2
  have dist : ∀ a ∈ N, ∀ i j, i < j → j ≤ i + 3 → τ^[i] a ≠ τ^[j] a :=
    fun a ha i j h1 h2 => orbit_ne free maps step ha h1 (by omega)
  have mapsI : ∀ a ∈ N, ∀ i, τ^[i] a ∈ N := fun a ha i => (orbit_walk maps step i a ha).1
  have NS : ∀ {v : ℕ}, v ∈ N → v ∈ S := fun h => (mem_N.mp h).1
  -- the orbit of any row with two heads is all of `N`
  have injO : ∀ a ∈ N, Set.InjOn (fun i => τ^[i] a) ↑(range 4) := by
    intro a ha i hi j hj e
    simp only [coe_range, Set.mem_Iio] at hi hj
    by_contra ne
    rcases lt_or_gt_of_ne ne with h | h
    · exact dist a ha i j h (by omega) e
    · exact dist a ha j i h (by omega) e.symm
  have orb : ∀ a ∈ N, (range 4).image (fun i => τ^[i] a) = N := by
    intro a ha
    have c4 : ((range 4).image (fun i => τ^[i] a)).card = 4 := by
      rw [card_image_of_injOn (injO a ha), card_range]
    have sub : (range 4).image (fun i => τ^[i] a) ⊆ N := by
      intro b hb
      obtain ⟨i, -, rfl⟩ := mem_image.mp hb
      exact mapsI a ha i
    exact eq_of_subset_of_card_le sub (by omega)
  have Nfour : N.card = 4 := by
    obtain ⟨a, ha⟩ := Nne
    rw [← orb a ha, card_image_of_injOn (injO a ha), card_range]
  have cover : ∀ a ∈ N, ∀ b ∈ N, ∃ i < 4, τ^[i] a = b := by
    intro a ha b hb
    rw [← orb a ha] at hb
    obtain ⟨i, hi, e⟩ := mem_image.mp hb
    exact ⟨i, mem_range.mp hi, e⟩
  have four : ∀ a ∈ N, τ^[4] a = a := by
    intro a ha
    obtain ⟨i, hi, e⟩ := cover a ha _ (mapsI a ha 4)
    by_cases i0 : i = 0
    · rw [i0] at e
      exact e.symm
    · exact absurd e (dist a ha i 4 hi (by omega))
  have walkO : ∀ a ∈ N, ∀ n, ∃ ℓ, ℓ ≤ 2 * n ∧ Walk D S a (τ^[n] a) ℓ := by
    intro a ha n
    obtain ⟨-, ℓ, -, h2, w⟩ := orbit_walk maps step n a ha
    exact ⟨ℓ, h2, w⟩
  -- the successor is unique
  have uniq : ∀ a ∈ N, ∀ b ∈ N, ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 2 → Walk D S a b ℓ → b = τ a := by
    intro a ha b hb ℓ h1 h2 w
    obtain ⟨i, hi, e⟩ := cover a ha b hb
    subst e
    interval_cases i
    · exact absurd w (free _ ℓ h1 (by omega))
    · rfl
    · obtain ⟨ℓ', h', w'⟩ := walkO _ (mapsI a ha 2) 2
      have back : τ^[2] (τ^[2] a) = a := by
        rw [← Function.iterate_add_apply]
        exact four a ha
      rw [back] at w'
      exact absurd (w.append w') (free a (ℓ + ℓ') (by omega) (by omega))
    · obtain ⟨ℓ', h', w'⟩ := walkO _ (mapsI a ha 3) 1
      have back : τ^[1] (τ^[3] a) = a := by
        rw [← Function.iterate_add_apply]
        exact four a ha
      rw [back] at w'
      exact absurd (w.append w') (free a (ℓ + ℓ') (by omega) (by omega))
  have inj : ∀ a ∈ N, ∀ a' ∈ N, τ a = τ a' → a = a' := by
    intro a ha a' ha' e
    obtain ⟨i, hi, e'⟩ := cover a ha a' ha'
    subst e'
    interval_cases i
    · rfl
    · exact absurd e (dist a ha 1 2 (by norm_num) (by norm_num))
    · exact absurd e (dist a ha 1 3 (by norm_num) (by norm_num))
    · have f4 : τ (τ^[3] a) = a := four a ha
      rw [f4] at e
      exact absurd e.symm (dist a ha 0 1 (by norm_num) (by norm_num))
  -- every head of a row with two heads is accounted for
  have heads : ∀ a ∈ N, outN D S a ⊆ ((outN D S a).filter (fun x => x = τ a)) ∪
      (B.filter (fun x => hd D S x = τ a)) ∪ ((good D S).filter (fun g => D a g = true)) := by
    intro a ha x hx
    obtain ⟨xS, ax⟩ := mem_outN.mp hx
    by_cases xl : x ∈ lone D S
    · by_cases xg : x ∈ good D S
      · exact mem_union_right _ (mem_filter.mpr ⟨xg, ax⟩)
      · have hn : hd D S x ∉ lone D S := fun h => xg (mem_good.mpr ⟨xl, h⟩)
        obtain ⟨hS', xh⟩ := hd_mem deg xl
        have := uniq a ha _ (mem_N.mpr ⟨hS', hn⟩) 2 (by norm_num) le_rfl
          (.step xS ax (.step hS' xh (.refl _)))
        exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_filter.mpr ⟨xl, hn⟩, this⟩))
    · have := uniq a ha x (mem_N.mpr ⟨xS, xl⟩) 1 le_rfl (by norm_num) (.step xS ax (.refl _))
      exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hx, this⟩))
  -- the good row has in-degree at most two
  have gin : ∀ g ∈ good D S, (inN D S g).card ≤ 2 := by
    intro g hg
    obtain ⟨gl, yl⟩ := mem_good.mp hg
    obtain ⟨yS, gy⟩ := hd_mem deg gl
    have gS := lone_subset gl
    have yng : hd D S g ∉ good D S := by
      intro h
      have := gone _ h g hg
      rw [this] at gy
      exact loopfree free (by omega) gS gy
    have bn : hd D S (hd D S g) ∉ lone D S := fun h => yng (mem_good.mpr ⟨yl, h⟩)
    obtain ⟨bS, yb⟩ := hd_mem deg yl
    have b3 := ball_two_heads free deg bS (two_of_not_lone bS bn) (k := q - 3) (by omega) (by omega)
    have h2 := ball_head free yS bS yb (k := q - 3) (by omega)
    rw [show q - 3 + 1 = q - 2 by omega] at h2
    have h1 := ball_head free gS yS gy (k := q - 2) (by omega)
    rw [show q - 2 + 1 = q - 1 by omega] at h1
    have := in_le_ball free (by omega) gS
    omega
  -- the count
  have lower : ∑ _a ∈ N, 2 ≤ ∑ a ∈ N, (outN D S a).card :=
    sum_le_sum (fun a ha => two_of_not_lone (mem_N.mp ha).1 (mem_N.mp ha).2)
  have upper : ∀ a ∈ N, (outN D S a).card ≤ (if D a (τ a) = true then 1 else 0) +
      (B.filter (fun x => hd D S x = τ a)).card +
      ((good D S).filter (fun g => D a g = true)).card := by
    intro a ha
    have c := (card_le_card (heads a ha)).trans
      ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
    have c1 : ((outN D S a).filter (fun x => x = τ a)).card ≤
        (if D a (τ a) = true then 1 else 0) := by
      split_ifs with h
      · exact card_le_one.mpr (fun x hx y hy => by
          rw [(mem_filter.mp hx).2, (mem_filter.mp hy).2])
      · rw [Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
        intro x hx e
        rw [e] at hx
        exact h (mem_outN.mp hx).2
    omega
  have sumU := sum_le_sum upper
  rw [sum_add_distrib, sum_add_distrib] at sumU
  have sB : ∑ a ∈ N, (B.filter (fun x => hd D S x = τ a)).card ≤ B.card := by
    simp only [card_filter]
    rw [sum_comm]
    calc ∑ x ∈ B, ∑ a ∈ N, (if hd D S x = τ a then 1 else 0)
        = ∑ x ∈ B, (N.filter (fun a => hd D S x = τ a)).card := by simp only [card_filter]
      _ ≤ ∑ _x ∈ B, 1 := sum_le_sum (fun x _ => card_le_one.mpr (fun a h a' h' =>
          inj a (mem_filter.mp h).1 a' (mem_filter.mp h').1
            ((mem_filter.mp h).2.symm.trans (mem_filter.mp h').2)))
      _ = B.card := by rw [sum_const, smul_eq_mul, mul_one]
  have sG : ∑ a ∈ N, ((good D S).filter (fun g => D a g = true)).card ≤ 2 * (good D S).card := by
    simp only [card_filter]
    rw [sum_comm]
    calc ∑ g ∈ good D S, ∑ a ∈ N, (if D a g = true then 1 else 0)
        = ∑ g ∈ good D S, (N.filter (fun a => D a g = true)).card := by simp only [card_filter]
      _ ≤ ∑ _g ∈ good D S, 2 := sum_le_sum (fun g hg => (card_le_card (fun a ha =>
          mem_inN.mpr ⟨NS (mem_filter.mp ha).1, (mem_filter.mp ha).2⟩)).trans (gin g hg))
      _ = 2 * (good D S).card := by rw [sum_const, smul_eq_mul, mul_comm]
  have sD : ∑ a ∈ N, (if D a (τ a) = true then 1 else 0) =
      (N.filter (fun a => D a (τ a) = true)).card := (card_filter _ _).symm
  rw [sum_const, smul_eq_mul, Nfour] at lower
  -- at least `8 - q` direct arcs
  obtain ⟨a, ha⟩ := Nne
  have sD' : ∑ c ∈ N, (if D c (τ c) = true then 1 else 0) =
      ∑ i ∈ range 4, (if D (τ^[i] a) (τ (τ^[i] a)) = true then 1 else 0) := by
    rw [← orb a ha, sum_image (injO a ha)]
  simp only [sum_range_succ, sum_range_zero, zero_add] at sD'
  -- walks with the direct arcs used
  have stepD : ∀ c ∈ N, ∃ ℓ, 1 ≤ ℓ ∧ ℓ + (if D c (τ c) = true then 1 else 0) ≤ 2 ∧
      Walk D S c (τ c) ℓ := by
    intro c hc
    by_cases h : D c (τ c) = true
    · exact ⟨1, le_rfl, by simp [h], .step (NS (maps c hc)) h (.refl _)⟩
    · obtain ⟨ℓ, h1, h2, w⟩ := step c hc
      exact ⟨ℓ, h1, by simp [h]; omega, w⟩
  obtain ⟨l0, p0, q0, w0⟩ := stepD _ (mapsI a ha 0)
  obtain ⟨l1, p1, q1, w1⟩ := stepD _ (mapsI a ha 1)
  obtain ⟨l2, p2, q2, w2⟩ := stepD _ (mapsI a ha 2)
  obtain ⟨l3, p3, q3, w3⟩ := stepD _ (mapsI a ha 3)
  have w : Walk D S a (τ (τ^[3] a)) (l0 + (l1 + (l2 + l3))) := w0.append (w1.append (w2.append w3))
  have f4 : τ (τ^[3] a) = a := four a ha
  rw [f4] at w
  exact free a _ (by omega) (by omega) w

/-- **A3 at `q = 6`, nine labels.** At least two good rows. -/
theorem good_nine (free : QFree D S 6) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card)
    (hS : S.card = 9) : 2 ≤ (good D S).card :=
  good_top free le_rfl deg hS

#print axioms good_top
#print axioms good_nine
#print axioms one_head_count
#print axioms one_head_six
#print axioms lone_within
#print axioms lone_two_six
#print axioms in_card
#print axioms hard_case
#print axioms good_count
#print axioms good_six

end LeanCH.BR.OneHead
