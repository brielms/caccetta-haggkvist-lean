import checkpoints.shen_extension.LoopCollar
import checkpoints.shen_extension.ReachLedger

/-!
# The collar ledger: thin roots are outvoted

A digraph with every out-degree exactly `q + 1` and no closed walk of length at most `q`.
Call a root *thin* when its second layer has at most `q` labels, *fat* otherwise.
By `LoopCollar.collar` the heads of a thin root form a loop of length `q + 1`.

* `loops_equal`: two thin roots whose loops share a head have the same heads.
* `twin_gap`: two roots with the same heads are a gap of each other at all radii up to `q`.
* `no_thin`: the count. Compare every row with the level `|V| + 1` of the two-ball ledger at
  radii `i + j ≤ q`. A thin root may fall short of the level by `δ`; each head of a thin root
  exceeds it by `π` (`LoopCollar.collar_ball`); fat roots do not fall short. Thin roots that
  share a loop are pairwise gaps, so `m` of them recover only `m (δ + 1 - m)`. If that is
  always less than the `(q + 1) π` their loop pays, there is no thin root at all.

Everything is generic in `q`, the radii and the floors; the floors are hypotheses.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.CollarLedger
open Finset BRq2 BRq3 FifthStripAll RigidHost LoopCollar
open DotTwoPassShellTransport (layer)
open ReachLedger (gap mem_gap ledger)

variable {D : CH.Digraph} {V : Finset ℕ} {q : ℕ}

/-- **Loops are equal or disjoint.** Two thin roots whose loops share a head have the same
heads. -/
theorem loops_equal (free : QFree D V q) (hq : 2 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 1)
    {u u' : ℕ} (hu : u ∈ V) (hu' : u' ∈ V)
    (thin : (layer D V 2 u).card ≤ q) (thin' : (layer D V 2 u').card ≤ q)
    {x : ℕ} (hx : x ∈ outN D V u) (hx' : x ∈ outN D V u') :
    outN D V u = outN D V u' := by
  classical
  have quota : ∀ w ∈ V, q + 1 ≤ (outN D V w).card := fun w hw => (reg w hw).ge
  obtain ⟨one, -, all⟩ := collar (r := q+1) free hq hu (reg u hu)
    (fun y hy => quota y (outN_subset hy)) (by omega)
  obtain ⟨one', -, all'⟩ := collar (r := q+1) free hq hu' (reg u' hu')
    (fun y hy => quota y (outN_subset hy)) (by omega)
  have keep := head_keep free hq hu
  have keep' := head_keep free hq hu'
  -- a common head hands its loop successor over
  have step : ∀ a ∈ outN D V u, a ∈ outN D V u' → ∀ b ∈ outN D V u, D a b = true →
      b ∈ outN D V u' := by
    intro a ha ha' b hb ab
    by_contra off
    have bV := (mem_outN.mp hb).1
    have bY' : b ∈ layer D V 2 u' :=
      (mem_union.mp (keep' a ha' (mem_outN.mpr ⟨bV, ab⟩))).resolve_left off
    obtain ⟨s, hs⟩ := card_pos.mp
      (by rw [one' a ha']; exact Nat.one_pos : 0 < (outN D (outN D V u') a).card)
    obtain ⟨sX', as⟩ := mem_outN.mp hs
    have sV := (mem_outN.mp sX').1
    have sne : s ≠ b := fun e => off (e ▸ sX')
    have sX : s ∉ outN D V u := by
      intro h
      have both : ({s, b} : Finset ℕ) ⊆ outN D (outN D V u) a := by
        intro z hz
        rcases mem_insert.mp hz with rfl | hz
        · exact mem_outN.mpr ⟨h, as⟩
        · rw [mem_singleton.mp hz]
          exact mem_outN.mpr ⟨hb, ab⟩
      have := card_le_card both
      rw [one a ha, card_pair sne] at this
      omega
    have sY : s ∈ layer D V 2 u :=
      (mem_union.mp (keep a ha (mem_outN.mpr ⟨sV, as⟩))).resolve_left sX
    have bs := (mem_outN.mp ((all b hb).2 sY)).2
    have sb := (mem_outN.mp ((all' s sX').2 bY')).2
    exact digonfree free hq bV sV bs sb
  -- every head of `u` is reached from `x` inside the loop
  have reach : ball D (outN D V u) x q = outN D V u := by
    refine eq_of_subset_of_card_le ball_subset ?_
    have := ball_grow (free.mono_set (outN_subset (D := D) (W := V) (y := u)))
      (fun v hv => (one v hv).ge) hx q le_rfl
    rw [reg u hu]
    exact this
  have walk : ∀ k a y, a ∈ outN D V u → a ∈ outN D V u' → Walk D (outN D V u) a y k →
      y ∈ outN D V u' := by
    intro k
    induction k with
    | zero =>
      intro a y _ ha' w
      cases w
      exact ha'
    | succ k ih =>
      intro a y ha ha' w
      cases w with
      | step bX ab rest => exact ih _ y bX (step a ha ha' _ bX ab) rest
  have sub : outN D V u ⊆ outN D V u' := by
    intro y hy
    rw [← reach] at hy
    obtain ⟨-, k, -, w⟩ := mem_ball.mp hy
    exact walk k x y hx hx' w
  exact eq_of_subset_of_card_le sub (by rw [reg u hu, reg u' hu'])

/-- Two roots with the same heads are a gap of each other at all radii up to `q`. -/
theorem twin_gap (free : QFree D V q) {u u' : ℕ} (hu : u ∈ V) (hu' : u' ∈ V) (ne : u ≠ u')
    (same : outN D V u = outN D V u') {i j : ℕ} (hi : i ≤ q) (hj : j ≤ q) :
    u' ∈ gap D V i j u :=
  mem_gap.mpr ⟨hu', fun h => twins_far free hu' ne same (ball_mono_radius hi h),
    fun h => twins_far free hu (Ne.symm ne) same.symm (ball_mono_radius hj h)⟩

/-- Double counting over the heads: every row of `T` has exactly `q + 1` heads. -/
theorem double (reg : ∀ v ∈ V, (outN D V v).card = q + 1) {T H : Finset ℕ} {R : ℕ → Finset ℕ}
    (tv : T ⊆ V) (h : ∀ v x, v ∈ T ∧ x ∈ outN D V v ↔ v ∈ R x ∧ x ∈ H) (f : ℕ → ℕ) :
    (q+1) * ∑ v ∈ T, f v = ∑ x ∈ H, ∑ v ∈ R x, f v := by
  have sw := Finset.sum_comm' (f := fun v _ => f v) h
  refine Eq.trans ?_ sw
  rw [mul_sum]
  exact sum_congr rfl (fun v hv => by simp only [sum_const, smul_eq_mul, reg v (tv hv)])

/-- **Thin roots are outvoted.** Floors `a`, `b` at radii `i`, `j` and `a'`, `b'` one radius
further out, for every row; `A + B` for the two balls of a fat row together. If fat rows reach
the level `|V| + 1`, heads of thin roots exceed it by `π`, thin roots fall short by at most
`δ`, and `m (δ + 1) < m² + (q + 1) π` for every `m`, then every root is fat. -/
theorem no_thin {i j a b A B a' b' π δ : ℕ} (free : QFree D V q) (hq : 2 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = q + 1) (hij : i + j ≤ q)
    (fa : ∀ v ∈ V, a ≤ (ball D V v i).card) (fb : ∀ v ∈ V, b ≤ (ball D V v j).card)
    (fa' : ∀ v ∈ V, a' ≤ (ball D V v (i+1)).card) (fb' : ∀ v ∈ V, b' ≤ (ball D V v (j+1)).card)
    (fat : ∀ v ∈ V, q + 1 ≤ (layer D V 2 v).card →
      A + B ≤ (ball D V v i).card + (ball D V v j).card)
    (fatpay : V.card + 1 ≤ A + B)
    (heads : V.card + 1 + π + 2*(q+1) ≤ a' + b' + i + j)
    (thinpay : V.card + 1 ≤ a + b + δ)
    (pay : ∀ m, m * (δ + 1) < m * m + (q+1) * π) :
    ∀ v ∈ V, q + 1 ≤ (layer D V 2 v).card := by
  classical
  by_contra exists_thin
  push Not at exists_thin
  obtain ⟨v0, v0V, v0thin⟩ := exists_thin
  have quota : ∀ w ∈ V, q + 1 ≤ (outN D V w).card := fun w hw => (reg w hw).ge
  set c : ℕ → ℕ := fun v => (ball D V v i).card + (ball D V v j).card + (gap D V i j v).card
    with hc
  set inH : ℕ → Prop := fun x => ∃ u ∈ V, (layer D V 2 u).card ≤ q ∧ x ∈ outN D V u with hinH
  set H := V.filter inH with hH
  set NH := V.filter (fun x => ¬ inH x) with hNH
  set T := NH.filter (fun v => (layer D V 2 v).card ≤ q) with hT
  set F := NH.filter (fun v => ¬ (layer D V 2 v).card ≤ q) with hF
  set R : ℕ → Finset ℕ := fun x => T.filter (fun v => x ∈ outN D V v) with hR
  have TV : T ⊆ V := (filter_subset _ _).trans (filter_subset _ _)
  -- the ledger
  have led : ∑ v ∈ V, c v = V.card * (V.card + 1) := by
    simp only [hc, sum_add_distrib]
    exact ledger free hij
  have split : ∑ v ∈ V, c v = ∑ v ∈ H, c v + (∑ v ∈ T, c v + ∑ v ∈ F, c v) := by
    rw [hT, hF, sum_filter_add_sum_filter_not, hH, hNH, sum_filter_add_sum_filter_not]
  have cards : H.card + (T.card + F.card) = V.card := by
    rw [hT, hF, Finset.card_filter_add_card_filter_not, hH, hNH,
      Finset.card_filter_add_card_filter_not]
  -- heads are above the level
  have headRow : ∀ x ∈ H, V.card + 1 + π ≤ c x := by
    intro x hx
    obtain ⟨-, u, uV, uthin, xu⟩ := mem_filter.mp hx
    have bi := collar_ball (r := q+1) free hq uV (reg u uV)
      (fun y hy => quota y (outN_subset hy)) (by omega) xu (j := i) (by omega)
    have bj := collar_ball (r := q+1) free hq uV (reg u uV)
      (fun y hy => quota y (outN_subset hy)) (by omega) xu (j := j) (by omega)
    have := fa' u uV
    have := fb' u uV
    simp only [hc]
    omega
  have hHsum : H.card * (V.card + 1 + π) ≤ ∑ v ∈ H, c v := by
    have := sum_le_sum headRow
    rwa [sum_const, smul_eq_mul] at this
  -- fat rows that are not heads reach the level
  have hFsum : F.card * (V.card + 1) ≤ ∑ v ∈ F, c v := by
    have each : ∀ v ∈ F, V.card + 1 ≤ c v := by
      intro v hv
      obtain ⟨vNH, vfat⟩ := mem_filter.mp hv
      have vV := (mem_filter.mp vNH).1
      have := fat v vV (by omega)
      simp only [hc]
      omega
    have := sum_le_sum each
    rwa [sum_const, smul_eq_mul] at this
  -- the thin rows on one head are pairwise gaps
  have classRow : ∀ x ∈ H, (R x).card * (V.card + 1) <
      ∑ v ∈ R x, c v + (q+1) * π := by
    intro x _
    have each : ∀ v ∈ R x, a + b + (R x).card ≤ c v + 1 := by
      intro v hv
      obtain ⟨vT, xv⟩ := mem_filter.mp hv
      have vV := TV vT
      have vthin := (mem_filter.mp vT).2
      have gaps : (R x).erase v ⊆ gap D V i j v := by
        intro w hw
        obtain ⟨wne, wR⟩ := mem_erase.mp hw
        obtain ⟨wT, xw⟩ := mem_filter.mp wR
        have wV := TV wT
        have wthin := (mem_filter.mp wT).2
        exact twin_gap free vV wV (Ne.symm wne)
          (loops_equal free hq reg vV wV vthin wthin xv xw) (by omega) (by omega)
      have g := card_le_card gaps
      rw [card_erase_of_mem hv] at g
      have := fa v vV
      have := fb v vV
      have pos : 0 < (R x).card := card_pos.mpr ⟨v, hv⟩
      simp only [hc]
      omega
    have total := sum_le_sum each
    rw [sum_const, smul_eq_mul, sum_add_distrib, sum_const, smul_eq_mul, mul_one] at total
    have p := pay (R x).card
    have e1 : (R x).card * (a + b + (R x).card) =
        (R x).card * (a + b) + (R x).card * (R x).card := by ring
    have e2 : (R x).card * (δ + 1) = (R x).card * δ + (R x).card := by ring
    have e3 : (R x).card * (V.card + 1) ≤ (R x).card * (a + b) + (R x).card * δ := by
      rw [← Nat.mul_add]
      exact Nat.mul_le_mul_left _ thinpay
    omega
  -- sum over the heads
  have Hne : H.Nonempty := by
    obtain ⟨x, hx⟩ := card_pos.mp (by rw [reg v0 v0V]; omega : 0 < (outN D V v0).card)
    exact ⟨x, mem_filter.mpr ⟨outN_subset hx, v0, v0V, by omega, hx⟩⟩
  have incidence : ∀ v x, v ∈ T ∧ x ∈ outN D V v ↔ v ∈ R x ∧ x ∈ H := by
    intro v x
    constructor
    · rintro ⟨vT, xv⟩
      exact ⟨mem_filter.mpr ⟨vT, xv⟩,
        mem_filter.mpr ⟨outN_subset xv, v, TV vT, (mem_filter.mp vT).2, xv⟩⟩
    · rintro ⟨vR, -⟩
      exact ⟨(mem_filter.mp vR).1, (mem_filter.mp vR).2⟩
  have dc := double reg TV incidence c
  have dn := double reg TV incidence (fun _ => V.card + 1)
  have strict := sum_lt_sum_of_nonempty Hne classRow
  rw [sum_add_distrib, sum_const, smul_eq_mul, ← dc] at strict
  have lhs : ∑ x ∈ H, (R x).card * (V.card + 1) = (q+1) * (T.card * (V.card + 1)) := by
    rw [← sum_const_nat (s := T) (f := fun _ => V.card + 1) (fun _ _ => rfl), dn]
    exact sum_congr rfl (fun x _ => by rw [sum_const, smul_eq_mul])
  rw [lhs] at strict
  have hTsum : T.card * (V.card + 1) < ∑ v ∈ T, c v + H.card * π := by
    have : (q+1) * (T.card * (V.card + 1)) < (q+1) * (∑ v ∈ T, c v + H.card * π) := by
      have e : (q+1) * (∑ v ∈ T, c v + H.card * π) =
          (q+1) * ∑ v ∈ T, c v + H.card * ((q+1) * π) := by ring
      omega
    exact Nat.lt_of_mul_lt_mul_left this
  -- total
  have e1 : V.card * (V.card + 1) =
      H.card * (V.card + 1) + T.card * (V.card + 1) + F.card * (V.card + 1) := by
    rw [← cards]
    ring
  have e2 : H.card * (V.card + 1 + π) = H.card * (V.card + 1) + H.card * π := by ring
  omega

#print axioms loops_equal
#print axioms twin_gap
#print axioms no_thin
end LeanCH.BR.CollarLedger
