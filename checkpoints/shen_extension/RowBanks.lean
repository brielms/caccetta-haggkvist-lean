import checkpoints.shen_extension.Supplier54
import checkpoints.shen_extension.TopRowFat

/-!
# Row banks for `r = q + 1` and `r = q + 2`

Generic structure lemmas (all with `q` free) for the rows `r = q + 1` and `r = q + 2`, used by
the open orders `72` (`q = 8`, `r = 9`) and `62`, `63` (`q = 7`, `r = 9`). Much of it already
exists and is only quoted:

* R1, thin root at `r = q + 1`: `LoopCollar.collar`; wrapper `thin_loop` here.
* R2, exact transfer: `LoopCollar.collar_ball` is the lower bound; the upper bound is new here
  (`loop_stays`, `transfer_le`), and `transfer_exact` is the equality.
* R3: `LoopCollar.loop_unique_head`.  R4: `TopRowFat.loop_complete`.
* R5, banks are equal or disjoint, for abstract banks: `banks_meet`, `banks_meet_r` (new; the
  root versions are `CollarLedger.loops_equal`, `CollarTwo.loops_equal`).
* R6, disjoint bank chains: `chain_card`, `no_cyclic_chain`, `bank_count` (new).
* R7, the two-radius score from `Supplier54.layer_ball`: `layer_ball_pair` (new).
-/

set_option linter.style.longLine false
namespace LeanCH.BR.RowBanks
open Finset BRq2 BRq3 LoopCollar
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)

variable {D : CH.Digraph} {q : ℕ}

/-! ### Balls in a set of internal out-degree at most one -/

/-- At internal out-degree at most one, the `k`-ball has at most `k + 1` labels. -/
theorem ball_one_head {S : Finset ℕ} (one : ∀ v ∈ S, (outN D S v).card ≤ 1) :
    ∀ k, ∀ x ∈ S, (ball D S x k).card ≤ k + 1 := by
  intro k
  induction k with
  | zero =>
    intro x _
    have sub : ball D S x 0 ⊆ {x} := by
      intro v hv
      obtain ⟨-, j, hj, w⟩ := mem_ball.mp hv
      obtain rfl : j = 0 := by omega
      cases w
      exact mem_singleton_self _
    simpa using card_le_card sub
  | succ k ih =>
    intro x xS
    by_cases h : (outN D S x).Nonempty
    · obtain ⟨b, hb⟩ := h
      have sub : ball D S x (k + 1) ⊆ insert x (ball D S b k) := by
        intro v hv
        obtain ⟨vS, j, hj, w⟩ := mem_ball.mp hv
        cases w with
        | refl => exact mem_insert_self _ _
        | step cS xc rest =>
          have cb := card_le_one.mp (one x xS) _ (mem_outN.mpr ⟨cS, xc⟩) b hb
          subst cb
          exact mem_insert_of_mem (mem_ball.mpr ⟨vS, _, by omega, rest⟩)
      have := (card_le_card sub).trans (card_insert_le _ _)
      have := ih b (mem_outN.mp hb).1
      omega
    · have sub : ball D S x (k + 1) ⊆ {x} := by
        intro v hv
        obtain ⟨-, j, hj, w⟩ := mem_ball.mp hv
        cases w with
        | refl => exact mem_singleton_self _
        | step cS xc rest => exact (h ⟨_, mem_outN.mpr ⟨cS, xc⟩⟩).elim
      have := card_le_card sub
      simp at this
      omega

/-! ### R1 and R2: the thin root at `r = q + 1` -/

section transfer
variable {V : Finset ℕ} {u : ℕ}

/-- **No re-entry.** If every row of `X` keeps its heads in `X ∪ Y` and points to all of `Y`,
then a walk of length at most `q` from a row of `X` to a row of `X` stays inside `X`: the first
step out lands in `Y`, and the end row points back to it. -/
theorem loop_stays {X Y : Finset ℕ} (free : QFree D V q)
    (keep : ∀ a ∈ X, outN D V a ⊆ X ∪ Y) (full : ∀ a ∈ X, Y ⊆ outN D V a) :
    ∀ k a w, a ∈ X → w ∈ X → Walk D V a w k → k ≤ q → Walk D X a w k := by
  intro k
  induction k with
  | zero =>
    intro a w _ _ wk _
    cases wk
    exact .refl _
  | succ k ih =>
    intro a w ha hw wk hk
    cases wk with
    | step bV ab rest =>
      rcases mem_union.mp (keep a ha (mem_outN.mpr ⟨bV, ab⟩)) with bX | bY
      · exact .step bX ab (ih _ w bX hw rest (by omega))
      · exact (free _ (k + 1) (by omega) hk
          (rest.snoc bV (mem_outN.mp (full w hw bY)).2)).elim

/-- **R2, upper bound** (generic, `i + 1 ≤ q`; no degree hypothesis). Heads `X` of `u` keep their
heads in `X ∪ Y` (`Y` the second layer), point to all of `Y`, and have at most one head in `X`.
Then for a head `x`: `|B_i(x)| + |X| ≤ |B_{i+1}(u)| + i`. Labels of `B_i(x)` outside `X` are in
`B_{i+1}(u) \ B_1(u)` (never `u`: that closes a walk of length `≤ i + 1 ≤ q`); labels in `X` are
reached inside `X` (`loop_stays`), so there are at most `i + 1` of them. -/
theorem transfer_le (free : QFree D V q) (hq : 1 ≤ q) (hu : u ∈ V)
    (keep : ∀ a ∈ outN D V u, outN D V a ⊆ outN D V u ∪ layer D V 2 u)
    (full : ∀ a ∈ outN D V u, layer D V 2 u ⊆ outN D V a)
    (one : ∀ a ∈ outN D V u, (outN D (outN D V u) a).card ≤ 1)
    {x : ℕ} (hx : x ∈ outN D V u) {i : ℕ} (hi : i + 1 ≤ q) :
    (ball D V x i).card + (outN D V u).card ≤ (ball D V u (i + 1)).card + i := by
  classical
  obtain ⟨xV, ux⟩ := mem_outN.mp hx
  have sub : ball D V x i ⊆
      (ball D V u (i + 1) \ ball D V u 1) ∪ ball D (outN D V u) x i := by
    intro v hv
    obtain ⟨vV, j, hj, w⟩ := mem_ball.mp hv
    by_cases vX : v ∈ outN D V u
    · exact mem_union_right _ (mem_ball.mpr
        ⟨vX, j, hj, loop_stays free keep full j x v hx vX w (by omega)⟩)
    · refine mem_union_left _ (mem_sdiff.mpr ⟨mem_ball.mpr ⟨vV, j + 1, by omega, .step xV ux w⟩, ?_⟩)
      intro h1
      rcases (mem_ball_one hu).mp h1 with rfl | h
      · exact free v (j + 1) (by omega) (by omega) (.step xV ux w)
      · exact vX h
  have c := (card_le_card sub).trans (card_union_le _ _)
  rw [card_sdiff_of_subset (ball_mono_radius (by omega))] at c
  have loop := ball_one_head one i x hx
  have b1 := ReachLedger.ball_one free hq hu
  have mono := card_le_card (ball_mono_radius (D := D) (W := V) (u := u) (show 1 ≤ i + 1 by omega))
  omega

/-- **R1: the thin root at `r = q + 1`** (`2 ≤ q`). Every out-degree `q + 1`, second layer of at
most `q` labels. Then the second layer has exactly `q` labels, every head has exactly one head
among the heads `X`, every head points to all of the second layer, and `X` is one loop: each
head reaches all of `X` inside `X` within `q` steps (so `X` is a chordless `(q+1)`-cycle). -/
theorem thin_loop (free : QFree D V q) (hq : 2 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 1) (hu : u ∈ V) (thin : (layer D V 2 u).card ≤ q) :
    (layer D V 2 u).card = q ∧
      ∀ x ∈ outN D V u, (outN D (outN D V u) x).card = 1 ∧ layer D V 2 u ⊆ outN D V x ∧
        ball D (outN D V u) x q = outN D V u := by
  obtain ⟨one, width, all⟩ := collar (r := q + 1) free hq hu (reg u hu)
    (fun y hy => (reg y (outN_subset hy)).ge) (by omega)
  refine ⟨by omega, fun x hx => ⟨one x hx, (all x hx).2, ?_⟩⟩
  refine eq_of_subset_of_card_le ball_subset ?_
  have := ball_grow (free.mono_set (outN_subset (D := D) (W := V) (y := u)))
    (fun v hv => (one v hv).ge) hx q le_rfl
  rw [reg u hu]
  exact this

/-- **R2: exact transfer at `r = q + 1`** (`2 ≤ q`, `i + 1 ≤ q`). Every out-degree `q + 1`,
second layer of `u` of at most `q` labels, `x` a head of `u`:
`|B_i(x)| + (q + 1) = |B_{i+1}(u)| + i`. Lower bound `LoopCollar.collar_ball`, upper bound
`transfer_le`. -/
theorem transfer_exact (free : QFree D V q) (hq : 2 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 1) (hu : u ∈ V) (thin : (layer D V 2 u).card ≤ q)
    {x : ℕ} (hx : x ∈ outN D V u) {i : ℕ} (hi : i + 1 ≤ q) :
    (ball D V x i).card + (q + 1) = (ball D V u (i + 1)).card + i := by
  obtain ⟨one, -, all⟩ := collar (r := q + 1) free hq hu (reg u hu)
    (fun y hy => (reg y (outN_subset hy)).ge) (by omega)
  have le := transfer_le free (by omega) hu (head_keep free hq hu) (fun a ha => (all a ha).2)
    (fun a ha => (one a ha).le) hx hi
  rw [reg u hu] at le
  have ge := collar_ball (r := q + 1) free hq hu (reg u hu)
    (fun y hy => (reg y (outN_subset hy)).ge) (by omega) hx (j := i) (by omega)
  omega

end transfer

/-! ### R5: banks are equal or disjoint -/

section banks
variable {V : Finset ℕ}

/-- **R5: two banks that meet are equal** (generic, `2 ≤ q`). A bank is a set `A` of `q + 1`
labels, each with exactly one head in `A`, all other heads in `Z`, and pointing to all of `Z`.
No size or disjointness hypothesis on `Z`, `Z'` is needed. If `A ∩ A' ≠ ∅` then `A = A'`: a
shared row `a` hands its `A`-successor `b` to `A'`, since otherwise `b ∈ Z'`, the `A'`-successor
`c` of `a` lies in `Z`, and `b → c → b` is a digon. -/
theorem banks_meet {A Z A' Z' : Finset ℕ} (free : QFree D V q) (hq : 2 ≤ q)
    (AV : A ⊆ V) (A'V : A' ⊆ V) (cA : A.card = q + 1) (cA' : A'.card = q + 1)
    (one : ∀ a ∈ A, (outN D A a).card = 1) (one' : ∀ a ∈ A', (outN D A' a).card = 1)
    (keep : ∀ a ∈ A, outN D V a ⊆ A ∪ Z) (keep' : ∀ a ∈ A', outN D V a ⊆ A' ∪ Z')
    (full : ∀ a ∈ A, Z ⊆ outN D V a) (full' : ∀ a ∈ A', Z' ⊆ outN D V a)
    {s : ℕ} (hs : s ∈ A) (hs' : s ∈ A') : A = A' := by
  classical
  have step : ∀ a ∈ A, a ∈ A' → ∀ b ∈ A, D a b = true → b ∈ A' := by
    intro a ha ha' b hb ab
    by_contra off
    have bV := AV hb
    have bZ' : b ∈ Z' :=
      (mem_union.mp (keep' a ha' (mem_outN.mpr ⟨bV, ab⟩))).resolve_left off
    obtain ⟨c, hc⟩ := card_pos.mp
      (by rw [one' a ha']; exact Nat.one_pos : 0 < (outN D A' a).card)
    obtain ⟨cIn', ac⟩ := mem_outN.mp hc
    have cV := A'V cIn'
    rcases mem_union.mp (keep a ha (mem_outN.mpr ⟨cV, ac⟩)) with cIn | cZ
    · have e := card_le_one.mp (one a ha).le c (mem_outN.mpr ⟨cIn, ac⟩) b (mem_outN.mpr ⟨hb, ab⟩)
      exact off (e ▸ cIn')
    · exact digonfree free hq bV cV (mem_outN.mp (full b hb cZ)).2
        (mem_outN.mp (full' c cIn' bZ')).2
  have reach : ball D A s q = A := by
    refine eq_of_subset_of_card_le ball_subset ?_
    rw [cA]
    exact ball_grow (free.mono_set AV) (fun v hv => (one v hv).ge) hs q le_rfl
  have walk : ∀ k a y, a ∈ A → a ∈ A' → Walk D A a y k → y ∈ A' := by
    intro k
    induction k with
    | zero =>
      intro a y _ ha' w
      cases w
      exact ha'
    | succ k ih =>
      intro a y ha ha' w
      cases w with
      | step bA ab rest => exact ih _ y bA (step a ha ha' _ bA ab) rest
  have sub : A ⊆ A' := by
    intro y hy
    rw [← reach] at hy
    obtain ⟨-, k, -, w⟩ := mem_ball.mp hy
    exact walk k s y hs hs' w
  exact eq_of_subset_of_card_le sub (by rw [cA, cA'])

/-- **R5 from degrees** (generic, `2 ≤ q`). Banks as in R3/R4: `A` of `q + 1` labels of
out-degree `r` keeping their heads in `A ∪ Z`, `A ∩ Z = ∅`, `|Z| + 1 ≤ r`; likewise `A'`, `Z'`.
If they meet they are equal. (`TopRowFat.loop_complete` supplies the one-head and completeness
facts.) -/
theorem banks_meet_r {A Z A' Z' : Finset ℕ} {r : ℕ} (free : QFree D V q) (hq : 2 ≤ q)
    (AV : A ⊆ V) (A'V : A' ⊆ V) (cA : A.card = q + 1) (cA' : A'.card = q + 1)
    (dj : Disjoint A Z) (dj' : Disjoint A' Z') (cZ : Z.card + 1 ≤ r) (cZ' : Z'.card + 1 ≤ r)
    (deg : ∀ a ∈ A, (outN D V a).card = r) (deg' : ∀ a ∈ A', (outN D V a).card = r)
    (keep : ∀ a ∈ A, outN D V a ⊆ A ∪ Z) (keep' : ∀ a ∈ A', outN D V a ⊆ A' ∪ Z')
    {s : ℕ} (hs : s ∈ A) (hs' : s ∈ A') : A = A' := by
  have L := TopRowFat.loop_complete free (by omega) AV cA dj cZ deg keep
  have L' := TopRowFat.loop_complete free (by omega) A'V cA' dj' cZ' deg' keep'
  exact banks_meet free hq AV A'V cA cA' (fun a ha => (L a ha).1) (fun a ha => (L' a ha).1)
    keep keep' (fun a ha => (L a ha).2.1) (fun a ha => (L' a ha).2.1) hs hs'

/-! ### R6: chains of banks -/

/-- **R6, count** (generic). `m + 1` pairwise disjoint sets of `q + 1` labels inside `V`:
`(m + 1)(q + 1) ≤ |V|`. (Completeness between consecutive banks is not needed for the count.) -/
theorem chain_card {A : ℕ → Finset ℕ} {m : ℕ}
    (AV : ∀ t ≤ m, A t ⊆ V) (cA : ∀ t ≤ m, (A t).card = q + 1)
    (dis : ∀ t ≤ m, ∀ t' ≤ m, t ≠ t' → Disjoint (A t) (A t')) :
    (m + 1) * (q + 1) ≤ V.card := by
  classical
  have cU : ((range (m + 1)).biUnion A).card = ∑ t ∈ range (m + 1), (A t).card := by
    apply card_biUnion
    intro t ht t' ht' ne
    exact dis t (by simp only [coe_range, Set.mem_Iio] at ht; omega) t'
      (by simp only [coe_range, Set.mem_Iio] at ht'; omega) ne
  have s : ∑ t ∈ range (m + 1), (A t).card = (m + 1) * (q + 1) := by
    rw [Finset.sum_congr rfl (fun t ht => cA t (by rw [mem_range] at ht; omega)), sum_const,
      card_range, smul_eq_mul]
  have sub : (range (m + 1)).biUnion A ⊆ V := by
    intro v hv
    obtain ⟨t, ht, hv⟩ := mem_biUnion.mp hv
    exact AV t (by rw [mem_range] at ht; omega) hv
  have := card_le_card sub
  omega

/-- **R6, no cyclic chain** (generic). Nonempty sets `A_0, …, A_m` in `V`, every row of `A_t`
pointing to every label of `A_{t+1}` (`t < m`) and every row of `A_m` to every label of `A_0`:
then `q < m + 1`. (One label in each closes a walk of length `m + 1`.) -/
theorem no_cyclic_chain {A : ℕ → Finset ℕ} {m : ℕ} (free : QFree D V q)
    (AV : ∀ t ≤ m, A t ⊆ V) (ne : ∀ t ≤ m, (A t).Nonempty)
    (link : ∀ t < m, ∀ a ∈ A t, ∀ b ∈ A (t + 1), D a b = true)
    (close : ∀ a ∈ A m, ∀ b ∈ A 0, D a b = true) (hm : m + 1 ≤ q) : False := by
  obtain ⟨a0, ha0⟩ := ne 0 (Nat.zero_le _)
  have path : ∀ t ≤ m, ∃ v ∈ A t, Walk D V a0 v t := by
    intro t
    induction t with
    | zero => exact fun _ => ⟨a0, ha0, .refl a0⟩
    | succ t ih =>
      intro ht
      obtain ⟨v, hv, w⟩ := ih (by omega)
      obtain ⟨b, hb⟩ := ne (t + 1) ht
      exact ⟨b, hb, w.snoc (AV (t + 1) ht hb) (link t (by omega) v hv b hb)⟩
  obtain ⟨v, hv, w⟩ := path m le_rfl
  exact free a0 (m + 1) (by omega) hm (w.snoc (AV 0 (Nat.zero_le _) ha0) (close v hv a0 ha0))

/-- **R6 at orders `n ≤ q (q + 2)`** (generic). At most `q` pairwise disjoint `(q+1)`-sets fit:
`m + 1` of them force `m + 1 ≤ q`. -/
theorem bank_count {A : ℕ → Finset ℕ} {m : ℕ}
    (AV : ∀ t ≤ m, A t ⊆ V) (cA : ∀ t ≤ m, (A t).card = q + 1)
    (dis : ∀ t ≤ m, ∀ t' ≤ m, t ≠ t' → Disjoint (A t) (A t'))
    (small : V.card ≤ q * (q + 2)) : m + 1 ≤ q := by
  have h := chain_card AV cA dis
  have lt : (m + 1) * (q + 1) < (q + 1) * (q + 1) := by nlinarith
  have := Nat.lt_of_mul_lt_mul_right lt
  omega

end banks

/-! ### R7: the two-radius score of a bank row -/

/-- **R7** (generic, `k + 1 ≤ q`). Under the hypotheses of `Supplier54.layer_ball` (rows of `A`
within `i ≥ 1` of `u`, each keeping a head in `A`; `s ∈ A` points to all of layer `i + 1`):
`|B_k(s)| + |B_{k+1}(s)| ≥ (2k + 3) + 2 (|L_{i+1}| + … + |L_{i+k}|) + |L_{i+k+1}|`.
For the score at `q = 2k + 1` take `k + 1 ≤ q`. -/
theorem layer_ball_pair {V : Finset ℕ} {u : ℕ} (free : QFree D V q) (hu : u ∈ V)
    {A : Finset ℕ} {i s k : ℕ} (hi : 1 ≤ i) (AV : A ⊆ V) (Ab : ∀ v ∈ A, v ∈ ball D V u i)
    (hs : s ∈ A) (deg : ∀ v ∈ A, 1 ≤ (outN D A v).card)
    (full : layer D V (i + 1) u ⊆ outN D V s) (hk : k + 1 ≤ q) :
    (2 * k + 3) + 2 * ∑ t ∈ range k, (layer D V (i + 1 + t) u).card +
        (layer D V (i + 1 + k) u).card ≤
      (ball D V s k).card + (ball D V s (k + 1)).card := by
  have b0 := Supplier54.layer_ball free hu hi AV Ab hs deg full (k := k) (by omega)
  have b1 := Supplier54.layer_ball free hu hi AV Ab hs deg full (k := k + 1) hk
  rw [sum_range_succ] at b1
  omega

#print axioms ball_one_head
#print axioms loop_stays
#print axioms transfer_le
#print axioms thin_loop
#print axioms transfer_exact
#print axioms banks_meet
#print axioms banks_meet_r
#print axioms chain_card
#print axioms no_cyclic_chain
#print axioms bank_count
#print axioms layer_ball_pair
end LeanCH.BR.RowBanks
