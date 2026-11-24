import checkpoints.shen_extension.MixedRadiusCompletion
import checkpoints.shen_extension.ShapeClimbDead

/-!
# Local-reach capacity of a punctured ball (the retained-layer count)

Appendices 20–21 of the degree-nine dossier, generic in the cutoff `q`, the degree `r`, the
lower degrees without hosts, the radius floors and the layer widths. Nothing is fixed.

Cut a root's ball at radius `R` (`R + 1 ≤ q`). The punctured `R`-ball `F` keeps every head of its
rows except those in the layer `R + 1`, so `F` is `q`-free of minimum out-degree `m = r - E` when
`|L (R + 1)| ≤ E` (`minOut_prefix_erase`). For a row `v` of layer `i` the local reach
`g_j = |ball_F v j| - 1` is at least `score … i j`:

* retained floors (`retained`): a path of `j` steps from `v` stays inside `F` while `i + j ≤ R`,
  and only its last label can leave `F`, into `L (R + 1)`, when `i + j = R + 1`. So
  `g_j ≥ f_j - 1` resp. `g_j ≥ f_j - 1 - E`, `f_j` the global closed floor;
* the step (`local_step`): if `g_j ≤ q t` for a degree `t` without hosts, the punctured `j`-ball
  of `v` in `F` is a fragment and `g_(j+1) ≥ g_j + m + 1 - t` (`ReachLedger.ball_growth`). The
  rule `step` is the monotone hull of `u ↦ u + max_t (m + 1 - t)`; with every degree below `m`
  available it is the paper's `u + max(0, m - ⌊(u-1)/q⌋)`.

The capacity (`ReachLedger.ledger`): for `a + b ≤ q`, `∑_F (|ball a| + |ball b|) ≤ |F| (|F| + 1)`,
since no pair is reached both ways. `ReachDeadP` checks the computed total against it at every
cut; `reach_false` is its soundness.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.ReachCapacity
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion ShapeClimbRoot ShapeClimbDead
open DotTwoPassShellTransport (layer shell layer_subset)

/-! ### The arithmetic -/

/-- Gain of the step at a punctured reach `w`: the best `m + 1 - t` over degrees `t` without
hosts whose range `q t` covers `w`. -/
def gain (q m : ℕ) (degrees : List ℕ) (w : ℕ) : ℕ :=
  ((degrees.filter (fun t => decide (1 ≤ t ∧ w ≤ q * t))).map (fun t => m + 1 - t)).foldr max 0

def next (q m : ℕ) (degrees : List ℕ) (w : ℕ) : ℕ := w + gain q m degrees w

/-- The monotone step: the least `next w` over `w ∈ [u, u + m]`. -/
def step (q m : ℕ) (degrees : List ℕ) (u : ℕ) : ℕ :=
  ((List.range (m + 1)).map (fun i => next q m degrees (u + i))).foldr min (next q m degrees u)

theorem foldr_max_cases : ∀ (l : List ℕ), l.foldr max 0 = 0 ∨ l.foldr max 0 ∈ l
  | [] => Or.inl rfl
  | a :: l => by
    rcases foldr_max_cases l with h | h
    · right
      simp [h]
    · simp only [List.foldr_cons, List.mem_cons]
      rcases le_total a (l.foldr max 0) with le | le
      · right; right; rw [max_eq_right le]; exact h
      · right; left; rw [max_eq_left le]

theorem foldr_max_le {c : ℕ} : ∀ (l : List ℕ), (∀ x ∈ l, x ≤ c) → l.foldr max 0 ≤ c
  | [], _ => Nat.zero_le _
  | a :: l, h => by
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (foldr_max_le l (fun x hx => h x (by simp [hx])))

theorem foldr_min_le : ∀ (l : List ℕ) (x : ℕ), l.foldr min x ≤ x ∧ ∀ y ∈ l, l.foldr min x ≤ y
  | [], x => ⟨le_rfl, by simp⟩
  | a :: l, x => by
    obtain ⟨h1, h2⟩ := foldr_min_le l x
    simp only [List.foldr_cons, List.mem_cons]
    refine ⟨(min_le_right _ _).trans h1, fun y hy => ?_⟩
    rcases hy with rfl | hy
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (h2 y hy)

theorem gain_le (q m : ℕ) (degrees : List ℕ) (w : ℕ) : gain q m degrees w ≤ m := by
  unfold gain
  refine foldr_max_le _ (fun x hx => ?_)
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  have := (of_decide_eq_true (List.mem_filter.mp ht).2).1
  omega

theorem gain_cases (q m : ℕ) (degrees : List ℕ) (w : ℕ) :
    gain q m degrees w = 0 ∨ ∃ t ∈ degrees, 1 ≤ t ∧ w ≤ q * t ∧ gain q m degrees w = m + 1 - t := by
  unfold gain
  rcases foldr_max_cases ((degrees.filter (fun t => decide (1 ≤ t ∧ w ≤ q * t))).map
    (fun t => m + 1 - t)) with h | h
  · exact Or.inl h
  · right
    obtain ⟨t, ht, e⟩ := List.mem_map.mp h
    obtain ⟨tm, td⟩ := List.mem_filter.mp ht
    exact ⟨t, tm, (of_decide_eq_true td).1, (of_decide_eq_true td).2, e.symm⟩

theorem step_le_next (q m : ℕ) (degrees : List ℕ) (u : ℕ) :
    step q m degrees u ≤ u + m := by
  have := (foldr_min_le ((List.range (m + 1)).map (fun i => next q m degrees (u + i)))
    (next q m degrees u)).1
  have g := gain_le q m degrees u
  unfold step
  unfold next at this ⊢
  omega

theorem step_le_of {q m : ℕ} {degrees : List ℕ} {u w : ℕ} (lo : u ≤ w) (hi : w ≤ u + m) :
    step q m degrees u ≤ next q m degrees w := by
  have := (foldr_min_le ((List.range (m + 1)).map (fun i => next q m degrees (u + i)))
    (next q m degrees u)).2 (next q m degrees w)
    (List.mem_map.mpr ⟨w - u, List.mem_range.mpr (by omega), by rw [Nat.add_sub_cancel' lo]⟩)
  exact this

/-! ### The step in a fragment-free graph -/

section graph
variable {D : CH.Digraph} {S : Finset ℕ} {q m : ℕ}

/-- **Local step.** In a `q`-free graph of minimum out-degree `m`, a punctured `j`-reach of at
least `u` gives a punctured `(j + 1)`-reach of at least `step u`. -/
theorem local_step {degrees : List ℕ} (lower : ∀ t ∈ degrees, NoHost q t)
    (free : QFree D S q) (deg : ∀ x ∈ S, m ≤ (outN D S x).card) {v j u : ℕ} (vS : v ∈ S)
    (hj : 1 ≤ j) (jq : j + 1 ≤ q) (low : u + 1 ≤ (ball D S v j).card) :
    step q m degrees u + 1 ≤ (ball D S v (j + 1)).card := by
  have mono : (ball D S v j).card ≤ (ball D S v (j + 1)).card :=
    card_le_card (ball_mono_radius (by omega))
  have pos : 1 ≤ (ball D S v j).card := card_pos.mpr ⟨v, self_mem_ball vS⟩
  set w := (ball D S v j).card - 1 with hw
  by_cases near : w ≤ u + m
  · have s := step_le_of (q := q) (degrees := degrees) (show u ≤ w by omega) near
    have grow : w + gain q m degrees w + 1 ≤ (ball D S v (j + 1)).card := by
      rcases gain_cases q m degrees w with g | ⟨t, ht, t1, cov, g⟩
      · rw [g]; omega
      · rcases Nat.eq_zero_or_pos m with m0 | mpos
        · have := gain_le q m degrees w
          omega
        · have := ReachLedger.ball_growth (lower t ht) free deg mpos vS hj jq (by omega)
          omega
    unfold next at s
    omega
  · have := step_le_next q m degrees u
    omega

end graph

/-! ### The punctured ball of a root -/

section root
variable {D : CH.Digraph} {V : Finset ℕ} {q u R : ℕ}

theorem mem_ball_trans {v w p j : ℕ} (hv : v ∈ ball D V u p) (hw : w ∈ ball D V v j) :
    w ∈ ball D V u (p + j) := by
  obtain ⟨_, i1, h1, w1⟩ := mem_ball.mp hv
  obtain ⟨wV, i2, h2, w2⟩ := mem_ball.mp hw
  exact mem_ball.mpr ⟨wV, i1 + i2, by omega, w1.append w2⟩

/-- A walk of `l` steps from a label within `p` of the root, `p + l ≤ R + 1`, ending in the
`R`-ball, runs inside the punctured `R`-ball. -/
theorem walk_inside (free : QFree D V q) (hu : u ∈ V) (Rq : R + 1 ≤ q) {x y l : ℕ}
    (w : Walk D V x y l) : ∀ {p : ℕ}, x ∈ ball D V u p → p + l ≤ R + 1 → y ∈ ball D V u R →
      Walk D ((ball D V u R).erase u) x y l := by
  induction w with
  | refl a => intro _ _ _ _; exact .refl a
  | @step a b c k hb hab rest ih =>
    intro p ha hl hc
    have bb : b ∈ ball D V u (p + 1) := ball_step ha hb hab
    have bne : b ≠ u := by
      rintro rfl
      exact no_back_arc free hu ha (by omega) hab
    have bR : b ∈ ball D V u R := by
      rcases Nat.lt_or_ge (p + 1) (R + 1) with h | h
      · exact ball_mono_radius (by omega) bb
      · obtain rfl : k = 0 := by omega
        cases rest
        exact hc
    exact .step (mem_erase.mpr ⟨bne, bR⟩) hab (ih bb (by omega) hc)

theorem mem_punct_of_layer {i v : ℕ} (_hi : 1 ≤ i) (iR : i ≤ R) (hv : v ∈ layer D V i u) :
    v ∈ (ball D V u R).erase u := by
  obtain ⟨vb, vn⟩ := mem_layer.mp hv
  refine mem_erase.mpr ⟨?_, ball_mono_radius iR vb⟩
  rintro rfl
  exact vn (self_mem_ball (mem_ball.mp vb).1)

/-- **Retention.** Labels of the `j`-ball of `v` (within `p` of the root, `p + j ≤ R + 1`)
that lie in the `R`-ball are in the local `j`-ball of `v` in the punctured `R`-ball. -/
theorem retained {v p j w : ℕ} (free : QFree D V q) (hu : u ∈ V) (Rq : R + 1 ≤ q)
    (vF : v ∈ (ball D V u R).erase u) (vp : v ∈ ball D V u p) (pj : p + j ≤ R + 1)
    (hw : w ∈ ball D V v j) (wR : w ∈ ball D V u R) :
    w ∈ ball D ((ball D V u R).erase u) v j := by
  obtain ⟨_, l, hl, wl⟩ := mem_ball.mp hw
  have inside := walk_inside free hu Rq wl vp (by omega) wR
  refine mem_ball.mpr ⟨?_, l, hl, inside⟩
  rcases inside.end_mem_or with e | e
  · rw [e]; exact vF
  · exact e

theorem retained_inner {v p j : ℕ} (free : QFree D V q) (hu : u ∈ V) (Rq : R + 1 ≤ q)
    (vF : v ∈ (ball D V u R).erase u) (vp : v ∈ ball D V u p) (pj : p + j ≤ R) :
    (ball D V v j).card ≤ (ball D ((ball D V u R).erase u) v j).card :=
  card_le_card (fun w hw => retained free hu Rq vF vp (by omega) hw
    (ball_mono_radius pj (mem_ball_trans vp hw)))

theorem retained_edge {v p j : ℕ} (free : QFree D V q) (hu : u ∈ V) (Rq : R + 1 ≤ q)
    (vF : v ∈ (ball D V u R).erase u) (vp : v ∈ ball D V u p) (pj : p + j = R + 1) :
    (ball D V v j).card ≤ (ball D ((ball D V u R).erase u) v j).card + (layer D V (R + 1) u).card := by
  classical
  refine (card_le_card (s := ball D V v j)
    (t := ball D ((ball D V u R).erase u) v j ∪ layer D V (R + 1) u) ?_).trans (card_union_le _ _)
  intro w hw
  have far : w ∈ ball D V u (R + 1) := by
    have := mem_ball_trans vp hw
    rwa [pj] at this
  by_cases wR : w ∈ ball D V u R
  · exact mem_union_left _ (retained free hu Rq vF vp (by omega) hw wR)
  · exact mem_union_right _ (mem_layer.mpr ⟨far, by simpa using wR⟩)

/-- Rows of the punctured `R`-ball keep `r - E` heads inside it. -/
theorem punct_deg {r E : ℕ} (free : QFree D V q) (hu : u ∈ V) (Rq : R + 1 ≤ q)
    (deg : ∀ v ∈ V, r ≤ (outN D V v).card) (hE : (layer D V (R + 1) u).card ≤ E) :
    ∀ x ∈ (ball D V u R).erase u, r - E ≤ (outN D ((ball D V u R).erase u) x).card := by
  intro x hx
  by_cases c : (layer D V (R + 1) u).card ≤ r
  · have eq : ball D V u (R + 1) \ ball D V u R = layer D V (R + 1) u := by
      simp only [layer, Nat.add_sub_cancel]
    have := minOut_prefix_erase (d := r - (layer D V (R + 1) u).card) free hu Rq deg
      (by rw [eq]; omega) x hx
    omega
  · omega

/-- The punctured `R`-ball is the disjoint union of the layers `1 … R`. -/
theorem punct_eq_layers (hu : u ∈ V) :
    (ball D V u R).erase u = (range R).biUnion (fun i => layer D V (i + 1) u) := by
  ext v
  simp only [mem_biUnion, mem_range]
  constructor
  · intro hv
    obtain ⟨j, h1, h2, hj⟩ := layer_of_ball hu (mem_erase.mp hv).2 (mem_erase.mp hv).1
    exact ⟨j - 1, by omega, by rwa [Nat.sub_add_cancel h1]⟩
  · rintro ⟨i, _hi, hv⟩
    exact mem_punct_of_layer (by omega) (by omega) hv

theorem sum_punct (hu : u ∈ V) (f : ℕ → ℕ) :
    ∑ v ∈ (ball D V u R).erase u, f v = ∑ i ∈ range R, ∑ v ∈ layer D V (i + 1) u, f v := by
  rw [punct_eq_layers hu, sum_biUnion]
  intro i _ j _ ne
  exact layer_disjoint' (by omega)

end root

/-! ### Scores and the rule -/

/-- Retained global floor (punctured) of a row of layer `i` at radius `j`, cut at `R`. -/
def ret (fs : List ℕ) (R E i j : ℕ) : ℕ :=
  if i + j ≤ R then fs.getD j 0 - 1 else if i + j = R + 1 then fs.getD j 0 - 1 - E else 0

/-- Lower bound for the punctured local `j`-reach of a row of layer `i` in the punctured
`R`-ball, `|L (R + 1)| ≤ E`. -/
def score (q r : ℕ) (degrees fs : List ℕ) (R E i : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => max (r - E) (ret fs R E i 1)
  | j + 2 => max (step q (r - E) degrees (score q r degrees fs R E i (j + 1))) (ret fs R E i (j + 2))

/-- The scored total over the punctured `R`-ball at radii `a`, `b` (closed balls). -/
def total (q r : ℕ) (degrees fs ws : List ℕ) (R E a b : ℕ) : ℕ :=
  ∑ i ∈ range R, ws.getD i 0 *
    (score q r degrees fs R E (i + 1) a + score q r degrees fs R E (i + 1) b + 2)

/-- The cut at radius `R` and the radii `a`, `q - a` overflows the capacity. -/
def ReachCut (q r : ℕ) (degrees fs ws : List ℕ) (last R a : ℕ) : Prop :=
  1 ≤ R ∧ R ≤ ws.length ∧ R + 1 ≤ q ∧ 1 ≤ a ∧ a + a ≤ q ∧
    (ws.take R).sum * ((ws.take R).sum + 1) < total q r degrees fs ws R (slot ws last R) a (q - a)

def ReachDeadP (q r : ℕ) (degrees fs ws : List ℕ) (last : ℕ) : Prop :=
  ∃ R ∈ range (ws.length + 1), ∃ a ∈ range (q / 2 + 1), ReachCut q r degrees fs ws last R a

instance {q r degrees fs ws last R a} : Decidable (ReachCut q r degrees fs ws last R a) := by
  unfold ReachCut; infer_instance
instance {q r degrees fs ws last} : Decidable (ReachDeadP q r degrees fs ws last) := by
  unfold ReachDeadP; infer_instance

def ReachDead (q r : ℕ) (degrees fs ws : List ℕ) (last : ℕ) : Bool :=
  decide (ReachDeadP q r degrees fs ws last)

section sound
variable {D : CH.Digraph} {V : Finset ℕ} {q r u R E : ℕ} {degrees fs : List ℕ}

theorem ret_sound (free : QFree D V q) (hu : u ∈ V) (Rq : R + 1 ≤ q)
    (deg : ∀ v ∈ V, r ≤ (outN D V v).card) (floors : ∀ j, Floor q r j (fs.getD j 0))
    (hE : (layer D V (R + 1) u).card ≤ E) {i v : ℕ} (hi : 1 ≤ i) (iR : i ≤ R)
    (hv : v ∈ layer D V i u) (j : ℕ) :
    ret fs R E i j + 1 ≤ (ball D ((ball D V u R).erase u) v j).card := by
  have vF := mem_punct_of_layer hi iR hv
  have vp : v ∈ ball D V u i := (mem_layer.mp hv).1
  have one : 1 ≤ (ball D ((ball D V u R).erase u) v j).card := card_pos.mpr ⟨v, self_mem_ball vF⟩
  have fl := floors j D V free deg v (layer_subset hv)
  unfold ret
  split_ifs with h1 h2
  · have := retained_inner free hu Rq vF vp h1
    omega
  · have := retained_edge free hu Rq vF vp h2
    omega
  · omega

theorem score_sound (free : QFree D V q) (hu : u ∈ V) (Rq : R + 1 ≤ q)
    (deg : ∀ v ∈ V, r ≤ (outN D V v).card) (floors : ∀ j, Floor q r j (fs.getD j 0))
    (lower : ∀ t ∈ degrees, NoHost q t)
    (hE : (layer D V (R + 1) u).card ≤ E) {i v : ℕ} (hi : 1 ≤ i) (iR : i ≤ R)
    (hv : v ∈ layer D V i u) : ∀ j, j ≤ q →
    score q r degrees fs R E i j + 1 ≤ (ball D ((ball D V u R).erase u) v j).card
  | 0, _ => by
    simp only [score]
    exact card_pos.mpr ⟨v, self_mem_ball (mem_punct_of_layer hi iR hv)⟩
  | 1, jq => by
    simp only [score]
    have vF := mem_punct_of_layer hi iR hv
    have Ffree : QFree D ((ball D V u R).erase u) q := free.mono_set ((erase_subset _ _).trans ball_subset)
    have b1 := ReachLedger.ball_one Ffree (by omega) vF
    have dg := punct_deg free hu Rq deg hE v vF
    have rt := ret_sound free hu Rq deg floors hE hi iR hv 1
    omega
  | j + 2, jq => by
    simp only [score]
    have vF := mem_punct_of_layer hi iR hv
    have Ffree : QFree D ((ball D V u R).erase u) q := free.mono_set ((erase_subset _ _).trans ball_subset)
    have ih := score_sound free hu Rq deg floors lower hE hi iR hv (j + 1) (by omega)
    have st := local_step (degrees := degrees) lower Ffree (punct_deg free hu Rq deg hE) vF
      (by omega) (by omega) ih
    change _ + 1 ≤ (ball D ((ball D V u R).erase u) v (j + 2)).card at st
    have rt := ret_sound free hu Rq deg floors hE hi iR hv (j + 2)
    omega

/-- **Soundness of the reach rule.** A `q`-free graph of minimum out-degree `r` with radius floors
`fs` and lower degrees `degrees` without hosts has no root whose layer widths are `ws`, with the
next layer at most `last`, when `ReachDead` holds. -/
theorem reach_false {ws : List ℕ} {last : ℕ} (free : QFree D V q)
    (deg : ∀ v ∈ V, r ≤ (outN D V v).card) (hu : u ∈ V)
    (floors : ∀ j, Floor q r j (fs.getD j 0)) (lower : ∀ t ∈ degrees, NoHost q t)
    (exact : ∀ i < ws.length, (layer D V (i + 1) u).card = ws.getD i 0)
    (bound : (layer D V (ws.length + 1) u).card ≤ last)
    (dead : ReachDead q r degrees fs ws last = true) : False := by
  obtain ⟨R, hR, a, ha, R1, Rlen, Rq, a1, aq, ovf⟩ := of_decide_eq_true dead
  have hE : (layer D V (R + 1) u).card ≤ slot ws last R := slot_le exact bound Rlen
  set F := (ball D V u R).erase u with hF
  have Ffree : QFree D F q := free.mono_set ((erase_subset _ _).trans ball_subset)
  have led := ReachLedger.ledger (D := D) (V := F) (i := a) (j := q - a) Ffree (by omega)
  have each : ∀ i ∈ range R, ws.getD i 0 *
      (score q r degrees fs R (slot ws last R) (i + 1) a +
        score q r degrees fs R (slot ws last R) (i + 1) (q - a) + 2)
      ≤ ∑ v ∈ layer D V (i + 1) u, ((ball D F v a).card + (ball D F v (q - a)).card) := by
    intro i hi
    have hi' := mem_range.mp hi
    have h : ∑ _v ∈ layer D V (i + 1) u, (score q r degrees fs R (slot ws last R) (i + 1) a +
        score q r degrees fs R (slot ws last R) (i + 1) (q - a) + 2)
        ≤ ∑ v ∈ layer D V (i + 1) u, ((ball D F v a).card + (ball D F v (q - a)).card) := by
      refine sum_le_sum (fun v hv => ?_)
      have s1 := score_sound free hu Rq deg floors lower hE (by omega) (by omega) hv a (by omega)
      have s2 := score_sound free hu Rq deg floors lower hE (by omega) (by omega) hv (q - a) (by omega)
      rw [← hF] at s1 s2
      omega
    rw [sum_const, smul_eq_mul, exact i (by omega)] at h
    exact h
  have tot := sum_le_sum each
  rw [← sum_punct hu, sum_add_distrib, ← hF] at tot
  have cs := card_ball_sum (D := D) (V := V) hu R
  have ce := card_erase_add_one (self_mem_ball (D := D) (W := V) (k := R) hu)
  rw [← hF] at ce
  have tk := take_sum_getD ws R
  have lw : ∑ j ∈ range R, (layer D V (j + 1) u).card = ∑ j ∈ range R, ws.getD j 0 :=
    sum_congr rfl (fun j hj => exact j (by have := mem_range.mp hj; omega))
  have size : F.card = (ws.take R).sum := by omega
  unfold total at ovf
  rw [← size] at ovf
  omega

end sound

#print axioms local_step
#print axioms retained
#print axioms score_sound
#print axioms reach_false

end LeanCH.BR.ReachCapacity
