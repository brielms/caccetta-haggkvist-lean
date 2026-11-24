import checkpoints.shen_extension.ReachLedgerCatalog
import checkpoints.shen_extension.WeightedJoint
import LeanCH.BR.BRq3FSE4

/-!
# Repair theory: signature-forced restoration, high columns, closed deletions, fresh labels

Lean 4.35.0. Every statement is for an arbitrary digraph `D`, label set `V`, cutoff `q`, degree
`r`, lower quota `t`, radius `i` and order `n`. No order, cutoff or degree is fixed here.
`ball D V v i` is the closed forward ball; `highReach D V H u` is the paper's `Q(u)` (labels of `H`
other than `u` within two steps), and `outN D H x` is the paper's `P(x)` (actual heads in `H`).

## Regime theorem

* `pair_regime`: no `q`-free digraph of minimum outdegree `r` on `n` labels exists when
  `NoHost q (r-1)`, `2 ≤ r`, `1 ≤ q`, `n ≤ q (r-1) + 2` and `r (r-1) < n - 1`. Proved from the
  one-unit deletion law (`closed_exit`) and a pair count after thinning to exact degree (`thin`).

## Signature-forced restoration (Appendix 11)

* `no_opposite`: two labels never reach each other at radii `i`, `j` with `i + j ≤ q`.
* `common_head`: a row whose two-ball has at most `2 r` labels shares a head with each of its heads.
* `reach_successor`: each high head `a` of such a row has a high successor `b ≠ a` within two
  steps of `a`, inside the row's high two-ball, provided common heads outside `H` head `H`.
* `heads_sub`, `signature_sub`, `signature_eq`, `orphan`: a deleted row's high signature sits in
  the high two-ball of each parent; with `|Q(u)| ≤ k ≤ |P(x)|` they are equal; above `k` there is
  no ordinary parent.
* `forced_port`, `port_cap`, `port_avoid`: if all of `Q(u)` but `a` are sinks of the radius-two
  graph on `Q(u)`, every ordinary row heading `H` heads `a`; then `a` has fewer high heads than
  `|Q(u)|`, and never heads a row that heads it.
* `pair_one_head`: with `|Q(u)| ≤ 2` and `4 ≤ q`, an ordinary row has at most one high head.
* `ordinary_loss`: with one deleted row per signature, an ordinary survivor loses at most
  `max 1 |P(u)|` heads to the deletion `X ∪ (H \ C)`.
* `cross_walk`, `cross_cycle`: the projected cross-loss digraph on ports has no cycle of `m` edges
  with `2 m ≤ q`.
* `clone_budget`: the clone repair in the paper's words (`WeightedJoint.weighted_exit`).

## High columns (Appendix 12)

* `cross_count`: `∑_{u∈A} |ball u i ∩ B| = ∑_{w∈B} |reverseBall w i ∩ A|`.
* `high_columns`: with `2 i ≤ q` and `H ⊆ V`,
  `2 ∑_{u∉H} |ball u i ∩ H| + h (h+1) + ∑_{w∈H} |gap w| + 2 ∑_{w∈H} |ball w i| ≤ 2 h (n+1)`.
* `few_highs`: the same with floors `m ≤ |ball u i ∩ H|` off `H` and `a ≤ |ball w i|` on `H`.

## Closed deletions and critical parents (Appendix 13)

* `OneLoss`, `closed_exit`: a proper set losing each outside row at most one head, of size at
  least `n - q (r-1)`, contradicts `NoHost q (r-1)`.
* `closed_extend`, `maximal_parent`, `source_large`: in a maximum proper closed set every outside
  label has a parent among the critical rows, and those rows number more than `q`.
* `walk_stays`, `restore_shut`, `partial_restore`: a retained part of a strongly connected critical
  set that keeps quota without new heads is the whole set.
* `cycle_walk`, `attach`, `one_tail`: attachment to a critical `(q+1)`-cycle: heads sit one or two
  steps after any tail, and a row with two consecutive heads has one tail.
* `lift_walk`, `fresh_lift`: fresh labels with no arcs among them, each segment `u → i → b` replaced
  by an original walk of one or two arcs: the repaired graph is `q`-free.
* `copy_lift` (Appendix 40): copies of a set `K` entered from rows heading some member of `K` and
  leaving to heads common to all of `K`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.SignatureRestoration
open Finset BRq2 BRq3 BR45 BypassRepair ReachLedger

variable {D : CH.Digraph} {V : Finset ℕ} {q : ℕ}

/-! ### Signatures -/

/-- The high two-ball `Q(u)`: labels of `H` other than `u` within two steps of `u`. -/
noncomputable def highReach (D : CH.Digraph) (V H : Finset ℕ) (u : ℕ) : Finset ℕ :=
  (ball D V u 2 ∩ H).erase u

theorem mem_highReach {H : Finset ℕ} {u b : ℕ} :
    b ∈ highReach D V H u ↔ b ≠ u ∧ b ∈ ball D V u 2 ∧ b ∈ H := by
  simp only [highReach, mem_erase, mem_inter]

/-- **No opposite arcs.** Two distinct labels never reach each other at radii `i`, `j`
with `i + j ≤ q`. -/
theorem no_opposite {i j a b : ℕ} (free : QFree D V q) (hij : i + j ≤ q) (ne : a ≠ b)
    (ab : b ∈ ball D V a i) (ba : a ∈ ball D V b j) : False := by
  obtain ⟨_, m, hm, wm⟩ := mem_ball.mp ab
  obtain ⟨_, n, hn, wn⟩ := mem_ball.mp ba
  have pos : 0 < m := by
    cases m with
    | zero => cases wm; exact absurd rfl ne
    | succ m => omega
  exact free a (m + n) (by omega) (by omega) (wm.append wn)

/-- **Common head.** A row whose two-ball has at most `2 r` labels shares a head with each of its
heads. -/
theorem common_head {r u a : ℕ} (free : QFree D V q) (hq : 2 ≤ q)
    (degree : ∀ v ∈ V, r ≤ (outN D V v).card) (uv : u ∈ V)
    (small : (ball D V u 2).card ≤ 2 * r) (ua : a ∈ outN D V u) :
    ∃ p ∈ V, D u p = true ∧ D a p = true := by
  classical
  obtain ⟨av, uaa⟩ := mem_outN.mp ua
  by_contra none
  have dis : Disjoint (outN D V u) (outN D V a) := disjoint_left.mpr (fun p hp hp' =>
    none ⟨p, (mem_outN.mp hp).1, (mem_outN.mp hp).2, (mem_outN.mp hp').2⟩)
  have sub : outN D V u ∪ outN D V a ⊆ (ball D V u 2).erase u := by
    intro w hw
    rcases mem_union.mp hw with h | h
    · obtain ⟨wv, uw⟩ := mem_outN.mp h
      refine mem_erase.mpr ⟨fun e => loopfree free (by omega) uv (by rw [e] at uw; exact uw), ?_⟩
      exact ball_mono_radius (by omega) (ball_of_adj wv uw)
    · obtain ⟨wv, aw⟩ := mem_outN.mp h
      refine mem_erase.mpr ⟨fun e => digonfree free hq uv av uaa (by rw [e] at aw; exact aw), ?_⟩
      exact mem_ball.mpr ⟨wv, 2, le_rfl, .step av uaa (.step wv aw (.refl w))⟩
  have c := card_le_card sub
  rw [card_union_of_disjoint dis, card_erase_of_mem (self_mem_ball uv)] at c
  have du := degree u uv
  have da := degree a av
  have pos := card_pos.mpr ⟨a, ua⟩
  omega

/-- **Successor in the signature.** Each high head `a` of a row with two-ball at most `2 r` has a
high label `b ≠ a` within two steps of `a` and inside `Q(u)`, provided that every common head
outside `H` heads `H`. -/
theorem reach_successor {r u a : ℕ} {H : Finset ℕ} (free : QFree D V q) (hq : 2 ≤ q) (hv : H ⊆ V)
    (degree : ∀ v ∈ V, r ≤ (outN D V v).card) (uv : u ∈ V)
    (small : (ball D V u 2).card ≤ 2 * r) (ua : a ∈ outN D H u)
    (port : ∀ p ∈ V, D u p = true → D a p = true → p ∉ H → ∃ b ∈ H, D p b = true) :
    ∃ b ∈ highReach D V H u, b ≠ a ∧ b ∈ ball D V a 2 := by
  obtain ⟨aH, uaa⟩ := mem_outN.mp ua
  have av := hv aH
  obtain ⟨p, pv, up, ap⟩ := common_head free hq degree uv small (mem_outN.mpr ⟨av, uaa⟩)
  have pa : p ≠ a := fun e => loopfree free (by omega) av (by rw [e] at ap; exact ap)
  have pu : p ≠ u := fun e => digonfree free hq uv av uaa (by rw [e] at ap; exact ap)
  by_cases pH : p ∈ H
  · exact ⟨p, mem_highReach.mpr ⟨pu, ball_mono_radius (by omega) (ball_of_adj pv up), pH⟩, pa,
      ball_mono_radius (by omega) (ball_of_adj pv ap)⟩
  · obtain ⟨b, bH, pb⟩ := port p pv up ap pH
    have bv := hv bH
    have ba : b ≠ a := fun e => digonfree free hq av pv ap (by rw [e] at pb; exact pb)
    have bu : b ≠ u := fun e => digonfree free hq uv pv up (by rw [e] at pb; exact pb)
    exact ⟨b, mem_highReach.mpr ⟨bu, mem_ball.mpr ⟨bv, 2, le_rfl, .step pv up (.step bv pb (.refl b))⟩, bH⟩,
      ba, mem_ball.mpr ⟨bv, 2, le_rfl, .step pv ap (.step bv pb (.refl b))⟩⟩

/-- A row's own high heads lie in its high two-ball. -/
theorem heads_sub {u : ℕ} {H : Finset ℕ} (free : QFree D V q) (hq : 1 ≤ q) (hv : H ⊆ V)
    (uv : u ∈ V) : outN D H u ⊆ highReach D V H u := by
  intro y hy
  obtain ⟨yH, uy⟩ := mem_outN.mp hy
  exact mem_highReach.mpr ⟨fun e => loopfree free hq uv (by rw [e] at uy; exact uy),
    ball_mono_radius (by omega) (ball_of_adj (hv yH) uy), yH⟩

/-- **Signature inclusion.** If `u → x`, the high heads of `x` lie in `Q(u)`. -/
theorem signature_sub {u x : ℕ} {H : Finset ℕ} (free : QFree D V q) (hq : 2 ≤ q) (hv : H ⊆ V)
    (uv : u ∈ V) (xv : x ∈ V) (ux : D u x = true) : outN D H x ⊆ highReach D V H u := by
  intro y hy
  obtain ⟨yH, xy⟩ := mem_outN.mp hy
  exact mem_highReach.mpr ⟨fun e => digonfree free hq uv xv ux (by rw [e] at xy; exact xy),
    mem_ball.mpr ⟨hv yH, 2, le_rfl, .step xv ux (.step (hv yH) xy (.refl y))⟩, yH⟩

/-- **Forced signature.** With `|Q(u)| ≤ k ≤ |P(x)|` and `u → x`, `P(x) = Q(u)`. -/
theorem signature_eq {k u x : ℕ} {H : Finset ℕ} (free : QFree D V q) (hq : 2 ≤ q) (hv : H ⊆ V)
    (uv : u ∈ V) (xv : x ∈ V) (ux : D u x = true) (small : (highReach D V H u).card ≤ k)
    (large : k ≤ (outN D H x).card) : outN D H x = highReach D V H u :=
  eq_of_subset_of_card_le (signature_sub free hq hv uv xv ux) (by omega)

/-- **Orphan.** A deleted row with more than `k` high heads has no parent with `|Q(u)| ≤ k`. -/
theorem orphan {k u x : ℕ} {H : Finset ℕ} (free : QFree D V q) (hq : 2 ≤ q) (hv : H ⊆ V)
    (uv : u ∈ V) (xv : x ∈ V) (small : (highReach D V H u).card ≤ k)
    (large : k < (outN D H x).card) : D u x ≠ true := fun ux => by
  have := card_le_card (signature_sub free hq hv uv xv ux)
  omega

/-- **Forced port.** If every label of `Q(u)` except `a` is a sink of the radius-two graph on
`Q(u)`, a row `u` that heads `H` heads `a`. -/
theorem forced_port {r u a : ℕ} {H : Finset ℕ} (free : QFree D V q) (hq : 2 ≤ q) (hv : H ⊆ V)
    (degree : ∀ v ∈ V, r ≤ (outN D V v).card) (uv : u ∈ V)
    (small : (ball D V u 2).card ≤ 2 * r)
    (port : ∀ c ∈ outN D H u, ∀ p ∈ V, D u p = true → D c p = true → p ∉ H →
      ∃ b ∈ H, D p b = true)
    (sinks : ∀ c ∈ highReach D V H u, c ≠ a → ∀ b ∈ highReach D V H u, b ≠ c →
      b ∉ ball D V c 2)
    (live : (outN D H u).Nonempty) : D u a = true ∧ a ∈ H := by
  obtain ⟨c, hc⟩ := live
  obtain ⟨b, bQ, bc, cb⟩ := reach_successor free hq hv degree uv small hc (port c hc)
  have cQ := heads_sub free (by omega) hv uv hc
  by_cases ca : c = a
  · rw [← ca]
    exact ⟨(mem_outN.mp hc).2, (mem_outN.mp hc).1⟩
  · exact absurd cb (sinks c cQ ca b bQ bc)

/-- **Port capacity.** A head `a ∈ H` of `u` has fewer high heads than `|Q(u)|`. -/
theorem port_cap {u a : ℕ} {H : Finset ℕ} (free : QFree D V q) (hq : 2 ≤ q) (hv : H ⊆ V)
    (uv : u ∈ V) (aH : a ∈ H) (ua : D u a = true) :
    (outN D H a).card + 1 ≤ (highReach D V H u).card := by
  have av := hv aH
  have sub : outN D H a ⊆ (highReach D V H u).erase a := by
    intro y hy
    obtain ⟨yH, ay⟩ := mem_outN.mp hy
    refine mem_erase.mpr ⟨fun e => loopfree free (by omega) av (by rw [e] at ay; exact ay), ?_⟩
    exact mem_highReach.mpr ⟨fun e => digonfree free hq uv av ua (by rw [e] at ay; exact ay),
      mem_ball.mpr ⟨hv yH, 2, le_rfl, .step av ua (.step (hv yH) ay (.refl y))⟩, yH⟩
  have aQ : a ∈ highReach D V H u := heads_sub free (by omega) hv uv (mem_outN.mpr ⟨aH, ua⟩)
  have c := card_le_card sub
  rw [card_erase_of_mem aQ] at c
  have pos := card_pos.mpr ⟨a, aQ⟩
  omega

/-- **Port avoidance.** A restored port never heads a row that heads it. -/
theorem port_avoid {a x : ℕ} (free : QFree D V q) (hq : 2 ≤ q) (av : a ∈ V) (xv : x ∈ V)
    (xa : D x a = true) : D a x ≠ true := fun ax => digonfree free hq xv av xa ax

/-- **One high head.** At `4 ≤ q`, a row with `|Q(u)| ≤ 2` and two-ball at most `2 r` has at most
one high head. -/
theorem pair_one_head {r u : ℕ} {H : Finset ℕ} (free : QFree D V q) (hq : 4 ≤ q) (hv : H ⊆ V)
    (degree : ∀ v ∈ V, r ≤ (outN D V v).card) (uv : u ∈ V)
    (small : (ball D V u 2).card ≤ 2 * r) (pair : (highReach D V H u).card ≤ 2)
    (port : ∀ c ∈ outN D H u, ∀ p ∈ V, D u p = true → D c p = true → p ∉ H →
      ∃ b ∈ H, D p b = true) :
    (outN D H u).card ≤ 1 := by
  rw [card_le_one]
  intro a ha a' ha'
  by_contra ne
  have aQ := heads_sub free (by omega) hv uv ha
  have aQ' := heads_sub free (by omega) hv uv ha'
  obtain ⟨b, bQ, ba, ab⟩ := reach_successor free (by omega) hv degree uv small ha (port a ha)
  obtain ⟨b', bQ', ba', ab'⟩ := reach_successor free (by omega) hv degree uv small ha' (port a' ha')
  have onlyTwo : ∀ c ∈ highReach D V H u, c = a ∨ c = a' := by
    intro c hc
    by_contra! off
    have : 2 < (highReach D V H u).card :=
      two_lt_card_iff.mpr ⟨a, a', c, aQ, aQ', hc, ne, fun e => off.1 e.symm, fun e => off.2 e.symm⟩
    omega
  have e1 : b = a' := (onlyTwo b bQ).resolve_left ba
  have e2 : b' = a := (onlyTwo b' bQ').resolve_right ba'
  rw [e1] at ab
  rw [e2] at ab'
  exact no_opposite free (by omega : 2 + 2 ≤ q) ne ab ab'

/-- **Ordinary loss.** Delete `X` (rows with at least `k` high heads, one per signature) and the
unrestored highs `H \ C`. An ordinary survivor (`|Q(u)| ≤ k`) whose high heads are restored when it
hits `X` loses at most `max 1 |P(u)|` heads. -/
theorem ordinary_loss {k u : ℕ} {H X C : Finset ℕ} (free : QFree D V q) (hq : 2 ≤ q)
    (hv : H ⊆ V) (xv : X ⊆ V) (uv : u ∈ V) (small : (highReach D V H u).card ≤ k)
    (large : ∀ x ∈ X, k ≤ (outN D H x).card)
    (select : ∀ x ∈ X, ∀ x' ∈ X, outN D H x = outN D H x' → x = x')
    (restore : (outN D X u).Nonempty → outN D H u ⊆ C) :
    (outN D (X ∪ (H \ C)) u).card ≤ max 1 (outN D H u).card := by
  have split : outN D (X ∪ (H \ C)) u = outN D X u ∪ outN D (H \ C) u := filter_union _ _ _
  rw [split]
  by_cases hit : (outN D X u).Nonempty
  · have one : (outN D X u).card ≤ 1 := by
      rw [card_le_one]
      intro x hx x' hx'
      obtain ⟨xX, ux⟩ := mem_outN.mp hx
      obtain ⟨xX', ux'⟩ := mem_outN.mp hx'
      exact select x xX x' xX' ((signature_eq free hq hv uv (xv xX) ux small (large x xX)).trans
        (signature_eq free hq hv uv (xv xX') ux' small (large x' xX')).symm)
    have none : outN D (H \ C) u = ∅ := by
      ext y
      simp only [mem_outN, mem_sdiff, notMem_empty, iff_false, not_and]
      intro ⟨yH, yC⟩ uy
      exact yC (restore hit (mem_outN.mpr ⟨yH, uy⟩))
    rw [none, union_empty]
    exact le_max_of_le_left one
  · have none : outN D X u = ∅ := not_nonempty_iff_eq_empty.mp hit
    rw [none, empty_union]
    refine le_max_of_le_right (card_le_card ?_)
    intro y hy
    obtain ⟨yHC, uy⟩ := mem_outN.mp hy
    exact mem_outN.mpr ⟨(mem_sdiff.mp yHC).1, uy⟩

/-- Ports `c i`, deleted rows `x i`, with `c i → x i → c (i+1)`: a walk of `2 m` arcs. -/
theorem cross_walk (c x : ℕ → ℕ) (cv : ∀ i, c i ∈ V) (xv : ∀ i, x i ∈ V)
    (out : ∀ i, D (c i) (x i) = true) (back : ∀ i, D (x i) (c (i+1)) = true) (m : ℕ) :
    Walk D V (c 0) (c m) (2 * m) := by
  induction m with
  | zero => exact .refl _
  | succ m ih =>
    have w : Walk D V (c 0) (c (m+1)) (2 * m + 2) :=
      ih.append (.step (xv m) (out m) (.step (cv (m+1)) (back m) (.refl (c (m+1)))))
    rw [show 2 * (m + 1) = 2 * m + 2 by ring]
    exact w

/-- **Cross-loss cycles.** The projected cross-loss digraph on ports (port `a` loses a head at the
deleted row `x`, whose own port is `b(x)`) has no cycle of `m` edges with `2 m ≤ q`. -/
theorem cross_cycle {m : ℕ} (c x : ℕ → ℕ) (free : QFree D V q) (cv : ∀ i, c i ∈ V)
    (xv : ∀ i, x i ∈ V) (out : ∀ i, D (c i) (x i) = true) (back : ∀ i, D (x i) (c (i+1)) = true)
    (close : c m = c 0) (pos : 1 ≤ m) (short : 2 * m ≤ q) : False := by
  have w := cross_walk c x cv xv out back m
  rw [close] at w
  exact free (c 0) (2 * m) (by omega) short w

/-- **Clone budget.** Survivors `W` with multiplicities `μ ≥ 1`, at most `q t - |W|` added copies
in total, every survivor paid in weight: impossible under `NoHost q t`. -/
theorem clone_budget {t : ℕ} {W : Finset ℕ} (none : NoHost q t) (free : QFree D V q)
    (wv : W ⊆ V) (live : W.Nonempty) (μ : ℕ → ℕ) (unit : ∀ v ∈ W, 1 ≤ μ v)
    (budget : ∑ v ∈ W, (μ v - 1) + W.card ≤ q * t)
    (paid : ∀ v ∈ W, t ≤ ∑ w ∈ outN D W v, μ w) : False := by
  obtain ⟨v, hv⟩ := live
  have mass := sum_excess (c := μ) (a := 1) unit
  exact WeightedJoint.weighted_exit none μ (free.mono_set wv) ⟨v, hv, unit v hv⟩ (by omega)
    (fun v hv _ => paid v hv)

/-! ### High columns -/

/-- **Cross count.** Forward reach from `A` into `B` is backward reach of `B` from `A`. -/
theorem cross_count {i : ℕ} {A B : Finset ℕ} (av : A ⊆ V) :
    ∑ u ∈ A, (ball D V u i ∩ B).card = ∑ w ∈ B, (reverseBall D V w i ∩ A).card := by
  classical
  have l : ∀ u, (ball D V u i ∩ B).card = ∑ w ∈ B, if w ∈ ball D V u i then 1 else 0 := by
    intro u
    rw [inter_comm, ← filter_mem_eq_inter, card_filter]
  have r : ∀ w, (reverseBall D V w i ∩ A).card = ∑ u ∈ A, if w ∈ ball D V u i then 1 else 0 := by
    intro w
    have e : reverseBall D V w i ∩ A = A.filter (fun u => w ∈ ball D V u i) := by
      ext u
      simp only [mem_inter, mem_filter, reverseBall]
      constructor
      · rintro ⟨⟨_, h⟩, ha⟩
        exact ⟨ha, h⟩
      · rintro ⟨ha, h⟩
        exact ⟨⟨av ha, h⟩, ha⟩
    rw [e, card_filter]
  rw [sum_congr rfl (fun u _ => l u), sum_congr rfl (fun w _ => r w)]
  exact sum_comm

/-- A high column sees all of `H`, counting itself twice. -/
theorem column_cover {i w : ℕ} {H : Finset ℕ} (hv : H ⊆ V) (wH : w ∈ H) :
    H.card + 1 ≤ (ball D V w i ∩ H).card + (reverseBall D V w i ∩ H).card
      + (gap D V i i w).card := by
  classical
  have wv := hv wH
  have cover : H ⊆ ((ball D V w i ∩ H) ∪ (reverseBall D V w i ∩ H)) ∪ gap D V i i w := by
    intro v vH
    by_cases f : v ∈ ball D V w i
    · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨f, vH⟩))
    by_cases b : w ∈ ball D V v i
    · exact mem_union_left _ (mem_union_right _
        (mem_inter.mpr ⟨mem_reverse.mpr ⟨hv vH, b⟩, vH⟩))
    · exact mem_union_right _ (mem_gap.mpr ⟨hv vH, f, b⟩)
  have both : w ∈ (ball D V w i ∩ H) ∩ (reverseBall D V w i ∩ H) :=
    mem_inter.mpr ⟨mem_inter.mpr ⟨self_mem_ball wv, wH⟩,
      mem_inter.mpr ⟨mem_reverse.mpr ⟨wv, self_mem_ball wv⟩, wH⟩⟩
  have c1 := card_le_card cover
  have c2 := card_union_le ((ball D V w i ∩ H) ∪ (reverseBall D V w i ∩ H)) (gap D V i i w)
  have c3 := card_union_add_card_inter (ball D V w i ∩ H) (reverseBall D V w i ∩ H)
  have c4 := card_pos.mpr ⟨w, both⟩
  omega

/-- **High columns.** Count, on the columns of `H`, the rows reaching them within `i`: the rows
off `H`, the pairs inside `H` (each comparable pair once, each incomparable pair as a gap) and the
forward balls of `H` fill at most `2 h (n + 1)`. -/
theorem high_columns {i : ℕ} {H : Finset ℕ} (free : QFree D V q) (hi : i + i ≤ q) (hv : H ⊆ V) :
    2 * ∑ u ∈ V \ H, (ball D V u i ∩ H).card + H.card * (H.card + 1)
      + ∑ w ∈ H, (gap D V i i w).card + 2 * ∑ w ∈ H, (ball D V w i).card
      ≤ 2 * (H.card * (V.card + 1)) := by
  classical
  have all := cross_count (D := D) (V := V) (i := i) (A := V) (B := H) (subset_refl V)
  have revV : ∀ w, reverseBall D V w i ∩ V = reverseBall D V w i := fun w =>
    inter_eq_left.mpr (filter_subset _ _)
  simp only [revV] at all
  rw [← sum_sdiff hv] at all
  have inner := cross_count (D := D) (V := V) (i := i) (A := H) (B := H) hv
  have rows : ∑ w ∈ H, ((ball D V w i).card + (reverseBall D V w i).card + (gap D V i i w).card)
      = ∑ _w ∈ H, (V.card + 1) := sum_congr rfl (fun w wH => row_ledger free hi (hv wH))
  simp only [sum_add_distrib, sum_const, smul_eq_mul] at rows
  have cov : ∑ _w ∈ H, (H.card + 1) ≤ ∑ w ∈ H, ((ball D V w i ∩ H).card
      + (reverseBall D V w i ∩ H).card + (gap D V i i w).card) :=
    sum_le_sum (fun w wH => column_cover hv wH)
  simp only [sum_add_distrib, sum_const, smul_eq_mul] at cov
  have m1 : H.card * (V.card + 1) = H.card * V.card + H.card := by ring
  have m2 : H.card * (H.card + 1) = H.card * H.card + H.card := by ring
  omega

/-- **Few highs.** Rows off `H` reaching at least `m` of `H` within `i`, columns of `H` with
balls of at least `a` labels. -/
theorem few_highs {i m a : ℕ} {H : Finset ℕ} (free : QFree D V q) (hi : i + i ≤ q) (hv : H ⊆ V)
    (reach : ∀ u ∈ V \ H, m ≤ (ball D V u i ∩ H).card) (high : ∀ w ∈ H, a ≤ (ball D V w i).card) :
    2 * ((V.card - H.card) * m) + H.card * (H.card + 1) + 2 * (H.card * a)
      ≤ 2 * (H.card * (V.card + 1)) := by
  have law := high_columns free hi hv
  have r1 : ∑ _u ∈ V \ H, m ≤ ∑ u ∈ V \ H, (ball D V u i ∩ H).card := sum_le_sum reach
  have r2 : ∑ _w ∈ H, a ≤ ∑ w ∈ H, (ball D V w i).card := sum_le_sum high
  rw [sum_const, smul_eq_mul, card_sdiff_of_subset hv] at r1
  rw [sum_const, smul_eq_mul] at r2
  omega

/-! ### Closed deletions -/

/-- One-unit deletion: every row outside `B` has at most one head in `B`. -/
def OneLoss (D : CH.Digraph) (V B : Finset ℕ) : Prop := ∀ u ∈ V \ B, (outN D B u).card ≤ 1

/-- **Closed exit.** A proper closed set of at least `n - q (r-1)` labels gives a host of degree
`r - 1`. -/
theorem closed_exit {r : ℕ} {B : Finset ℕ} (none : NoHost q (r-1)) (free : QFree D V q)
    (degree : ∀ v ∈ V, r ≤ (outN D V v).card) (sub : B ⊆ V) (closed : OneLoss D V B)
    (live : (V \ B).Nonempty) (big : V.card ≤ q*(r-1) + B.card) : False := by
  refine none D (V \ B) live ?_ (free.mono_set sdiff_subset) (fun u hu => ?_)
  · rw [card_sdiff_of_subset sub]
    omega
  · have split := card_outN_union (D := D) (show Disjoint B (V \ B) from disjoint_sdiff) u
    rw [union_sdiff_of_subset sub] at split
    have := degree u (mem_sdiff.mp hu).1
    have := closed u hu
    omega

/-- **Closed extension.** An outside label with no parent among the critical rows can join. -/
theorem closed_extend {B : Finset ℕ} {c : ℕ} (closed : OneLoss D V B)
    (orphan : ∀ u ∈ V \ B, (outN D B u).Nonempty → D u c ≠ true) :
    OneLoss D V (insert c B) := by
  intro u hu
  have hu' : u ∈ V \ B :=
    mem_sdiff.mpr ⟨(mem_sdiff.mp hu).1, fun h => (mem_sdiff.mp hu).2 (mem_insert_of_mem h)⟩
  by_cases uc : D u c = true
  · have empty : outN D B u = ∅ := by
      by_contra ne
      exact orphan u hu' (nonempty_iff_ne_empty.mpr ne) uc
    have sub : outN D (insert c B) u ⊆ {c} := by
      intro y hy
      obtain ⟨yB, uy⟩ := mem_outN.mp hy
      rcases mem_insert.mp yB with e | yB
      · exact mem_singleton.mpr e
      · have h : y ∈ outN D B u := mem_outN.mpr ⟨yB, uy⟩
        rw [empty] at h
        exact absurd h (notMem_empty y)
    exact (card_le_card sub).trans (card_singleton c).le
  · have sub : outN D (insert c B) u ⊆ outN D B u := by
      intro y hy
      obtain ⟨yB, uy⟩ := mem_outN.mp hy
      rcases mem_insert.mp yB with e | yB
      · rw [e] at uy
        exact absurd uy uc
      · exact mem_outN.mpr ⟨yB, uy⟩
    exact (card_le_card sub).trans (closed u hu')

/-- The critical rows of a deletion: outside rows with a head inside. -/
noncomputable def critical (D : CH.Digraph) (V B : Finset ℕ) : Finset ℕ :=
  (V \ B).filter (fun u => (outN D B u).Nonempty)

/-- **Maximal parent.** In a maximum proper closed set with at least two outside labels, every
outside label has a parent among the critical rows. -/
theorem maximal_parent {B : Finset ℕ} {c : ℕ} (sub : B ⊆ V) (closed : OneLoss D V B)
    (maximum : ∀ B' ⊆ V, OneLoss D V B' → (V \ B').Nonempty → B'.card ≤ B.card)
    (two : 2 ≤ (V \ B).card) (cc : c ∈ V \ B) :
    ∃ p ∈ critical D V B, D p c = true := by
  classical
  by_contra! none
  have ext := closed_extend (c := c) closed (fun u hu ne uc =>
    none u (mem_filter.mpr ⟨hu, ne⟩) uc)
  have cB : c ∉ B := (mem_sdiff.mp cc).2
  have sub' : insert c B ⊆ V := insert_subset (mem_sdiff.mp cc).1 sub
  have rest : (V \ insert c B).Nonempty := by
    have e : (V \ insert c B).card = (V \ B).card - 1 := by
      rw [card_sdiff_of_subset sub', card_insert_of_notMem cB, card_sdiff_of_subset sub]
      omega
    exact card_pos.mp (by omega)
  have le := maximum (insert c B) sub' ext rest
  rw [card_insert_of_notMem cB] at le
  omega

/-- **Source size.** The critical rows of a maximum proper closed set with at least two outside
labels number more than `q`. -/
theorem source_large {B : Finset ℕ} (free : QFree D V q) (sub : B ⊆ V) (closed : OneLoss D V B)
    (maximum : ∀ B' ⊆ V, OneLoss D V B' → (V \ B').Nonempty → B'.card ≤ B.card)
    (two : 2 ≤ (V \ B).card) (live : (critical D V B).Nonempty) :
    q < (critical D V B).card := by
  by_contra small
  have pv : critical D V B ⊆ V := (filter_subset _ _).trans sdiff_subset
  obtain ⟨s, hs, src⟩ := exists_source (free.mono_set pv) live (by omega)
  obtain ⟨p, pc, ps⟩ := maximal_parent sub closed maximum two (mem_filter.mp hs).1
  exact src p pc ps

/-- A walk from a set closed under arcs stays in it. -/
theorem walk_stays {Z R : Finset ℕ} (shut : ∀ z ∈ R, ∀ y ∈ Z, D z y = true → y ∈ R)
    {a b m : ℕ} (w : Walk D Z a b m) : a ∈ R → b ∈ R := by
  induction w with
  | refl a => exact id
  | step hb hab _ ih => exact fun ha => ih (shut _ ha _ hb hab)

/-- **Restored rows keep their successors.** A row of a critical set `Z` (disjoint from `B`) that
already loses a head to `B`, has degree at most `r`, and keeps `r - 1` heads on
`V \ (B ∪ (Z \ R))`, has all its `Z`-heads in `R`. -/
theorem restore_shut {r z : ℕ} {B Z R : Finset ℕ} (dis : Disjoint B Z)
    (exact : (outN D V z).card ≤ r) (lost : 1 ≤ (outN D B z).card)
    (keep : r - 1 ≤ (outN D (V \ (B ∪ (Z \ R))) z).card) (bv : B ⊆ V) (zv : Z ⊆ V) :
    ∀ y ∈ Z, D z y = true → y ∈ R := by
  classical
  intro y yZ zy
  by_contra yR
  have d1 : Disjoint (V \ (B ∪ (Z \ R))) B :=
    disjoint_left.mpr (fun x hx hb => (mem_sdiff.mp hx).2 (mem_union_left _ hb))
  have d2 : Disjoint (V \ (B ∪ (Z \ R)) ∪ B) (Z \ R) := by
    refine disjoint_left.mpr (fun x hx hz => ?_)
    rcases mem_union.mp hx with h | h
    · exact (mem_sdiff.mp h).2 (mem_union_right _ hz)
    · exact disjoint_left.mp dis h (mem_sdiff.mp hz).1
  have u1 := card_outN_union (D := D) d1 z
  have u2 := card_outN_union (D := D) d2 z
  have sub : outN D ((V \ (B ∪ (Z \ R)) ∪ B) ∪ (Z \ R)) z ⊆ outN D V z := by
    intro w hw
    obtain ⟨wm, zw⟩ := mem_outN.mp hw
    refine mem_outN.mpr ⟨?_, zw⟩
    rcases mem_union.mp wm with h | h
    · rcases mem_union.mp h with h | h
      · exact (mem_sdiff.mp h).1
      · exact bv h
    · exact zv (mem_sdiff.mp h).1
  have one : 0 < (outN D (Z \ R) z).card :=
    card_pos.mpr ⟨y, mem_outN.mpr ⟨mem_sdiff.mpr ⟨yZ, yR⟩, zy⟩⟩
  have c := card_le_card sub
  omega

/-- **Partial restoration.** A nonempty retained part `R` of a strongly connected critical set `Z`
whose rows all keep quota `r - 1` without new heads is all of `Z`. -/
theorem partial_restore {r : ℕ} {B Z R : Finset ℕ} (dis : Disjoint B Z) (bv : B ⊆ V) (zv : Z ⊆ V)
    (sub : R ⊆ Z) (live : R.Nonempty)
    (strong : ∀ a ∈ Z, ∀ b ∈ Z, ∃ m, Walk D Z a b m)
    (exact : ∀ z ∈ R, (outN D V z).card ≤ r) (lost : ∀ z ∈ R, 1 ≤ (outN D B z).card)
    (keep : ∀ z ∈ R, r - 1 ≤ (outN D (V \ (B ∪ (Z \ R))) z).card) : R = Z := by
  obtain ⟨a, aR⟩ := live
  refine subset_antisymm sub (fun b bZ => ?_)
  obtain ⟨m, w⟩ := strong a (sub aR) b bZ
  exact walk_stays (fun z zR => restore_shut dis (exact z zR) (lost z zR) (keep z zR) bv zv) w aR

/-! ### Attachment to a critical cycle -/

/-- Walk along a cycle `z` with arcs `z i → z (i+1)`. -/
theorem cycle_walk (z : ℕ → ℕ) (zv : ∀ i, z i ∈ V) (cyc : ∀ i, D (z i) (z (i+1)) = true) :
    ∀ m i, Walk D V (z i) (z (i+m)) m
  | 0, i => by simpa using Walk.refl (D := D) (W := V) (z i)
  | m+1, i => by
    have w := Walk.step (zv (i+1)) (cyc i) (cycle_walk z zv cyc m (i+1))
    rw [show i + 1 + m = i + (m+1) by omega] at w
    exact w

/-- **Attachment.** On a `(q+1)`-cycle `z` (period `q + 1`), an outside row with a tail `z i` has
heads only at `z (i+1)` and `z (i+2)`. -/
theorem attach (z : ℕ → ℕ) (free : QFree D V q) (hq : 2 ≤ q) (zv : ∀ i, z i ∈ V)
    (cyc : ∀ i, D (z i) (z (i+1)) = true) (period : ∀ i, z (i + (q+1)) = z i)
    (i m x : ℕ) (xv : x ∈ V) (into : D (z i) x = true) (outof : D x (z (i+m)) = true)
    (hm : m ≤ q) : m = 1 ∨ m = 2 := by
  have w1 : Walk D V (z i) (z (i+m)) 2 := .step xv into (.step (zv (i+m)) outof (.refl _))
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    simp only [Nat.add_zero] at w1
    exact (free (z i) 2 (by omega) hq w1).elim
  · by_contra hne
    have w2 := cycle_walk z zv cyc (q+1-m) (i+m)
    rw [show i + m + (q+1-m) = i + (q+1) by omega, period] at w2
    exact free (z i) (2 + (q+1-m)) (by omega) (by omega) (w1.append w2)

/-- **One tail.** At `3 ≤ q`, a row heading two consecutive labels `z (i+1)`, `z (i+2)` of a
critical `(q+1)`-cycle has no tail on the cycle other than `z i`. -/
theorem one_tail (z : ℕ → ℕ) (free : QFree D V q) (hq : 3 ≤ q) (zv : ∀ i, z i ∈ V)
    (cyc : ∀ i, D (z i) (z (i+1)) = true) (period : ∀ i, z (i + (q+1)) = z i)
    {i c x : ℕ} (xv : x ∈ V) (into : D (z (i + c)) x = true) (hc : 1 ≤ c) (hcq : c ≤ q)
    (h1 : D x (z (i+1)) = true) (h2 : D x (z (i+2)) = true) : False := by
  rcases Nat.lt_or_ge c 2 with h | h
  · have e : c = 1 := by omega
    subst e
    have a := attach z free (by omega) zv cyc period (i+1) 0 x xv into (by simpa using h1) (by omega)
    omega
  · have e1 : z (i + c + (q + 2 - c)) = z (i+1) := by
      rw [show i + c + (q+2-c) = (i+1) + (q+1) by omega, period]
    have a1 := attach z free (by omega) zv cyc period (i+c) (q+2-c) x xv into
      (by rw [e1]; exact h1) (by omega)
    have e2 : z (i + c + 3) = z (i+2) := by
      rw [show i + c + 3 = (i+2) + (q+1) by omega, period]
    have a2 := attach z free (by omega) zv cyc period (i+c) 3 x xv into
      (by rw [e2]; exact h2) (by omega)
    omega

/-! ### Fresh repair labels -/

theorem uncons {G : CH.Digraph} {U : Finset ℕ} {a c k : ℕ} (w : Walk G U a c (k+1)) :
    ∃ b, b ∈ U ∧ G a b = true ∧ Walk G U b c k := by
  cases w with
  | step hb hab rest => exact ⟨_, hb, hab, rest⟩

/-- **Lifting.** Old arcs inside `W`, no arcs between fresh labels, and each segment `u → i → b`
through a fresh label `i` replaced by an original walk of one or two arcs: every walk between
retained labels lifts to an original walk that is no longer, and positive when it was. -/
theorem lift_walk {G : CH.Digraph} {W N : Finset ℕ} (wv : W ⊆ V) (dis : Disjoint W N)
    (old : ∀ a ∈ W, ∀ b ∈ W, G a b = true → D a b = true)
    (apart : ∀ i ∈ N, ∀ j ∈ N, G i j ≠ true)
    (lift : ∀ u ∈ W, ∀ i ∈ N, ∀ b ∈ W, G u i = true → G i b = true →
      ∃ m, 1 ≤ m ∧ m ≤ 2 ∧ Walk D V u b m) :
    ∀ L x y, x ∈ W → y ∈ W → Walk G (W ∪ N) x y L →
      ∃ L', L' ≤ L ∧ (0 < L → 0 < L') ∧ Walk D V x y L' := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro x y xw yw w
    rcases Nat.eq_zero_or_pos L with h0 | hpos
    · subst h0
      cases w
      exact ⟨0, le_rfl, fun h => absurd h (lt_irrefl 0), .refl _⟩
    obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
    obtain ⟨b, bm, xb, rest⟩ := uncons w
    rcases mem_union.mp bm with bw | bn
    · obtain ⟨L', le, _, w'⟩ := ih k (by omega) b y bw yw rest
      exact ⟨L' + 1, by omega, fun _ => by omega, .step (wv bw) (old x xw b bw xb) w'⟩
    · rcases Nat.eq_zero_or_pos k with k0 | kpos
      · subst k0
        cases rest
        exact (disjoint_left.mp dis yw bn).elim
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      obtain ⟨c, cm, bc, rest'⟩ := uncons rest
      rcases mem_union.mp cm with cw | cn
      · obtain ⟨m, m1, m2, wm⟩ := lift x xw b bn c cw xb bc
        obtain ⟨L', le, _, w'⟩ := ih k' (by omega) c y cw yw rest'
        exact ⟨m + L', by omega, fun _ => by omega, wm.append w'⟩
      · exact absurd bc (apart b bn c cn)

/-- **Fresh lift.** Under the same conditions the repaired graph on `W ∪ N` is `q`-free. -/
theorem fresh_lift {G : CH.Digraph} {W N : Finset ℕ} (free : QFree D V q) (wv : W ⊆ V)
    (dis : Disjoint W N)
    (old : ∀ a ∈ W, ∀ b ∈ W, G a b = true → D a b = true)
    (apart : ∀ i ∈ N, ∀ j ∈ N, G i j ≠ true)
    (lift : ∀ u ∈ W, ∀ i ∈ N, ∀ b ∈ W, G u i = true → G i b = true →
      ∃ m, 1 ≤ m ∧ m ≤ 2 ∧ Walk D V u b m) :
    QFree G (W ∪ N) q := by
  intro a ℓ h1 hq w
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  obtain ⟨_, _, am, _⟩ := w.unsnoc
  rcases mem_union.mp am with aw | an
  · obtain ⟨L', le, pos, w'⟩ := lift_walk wv dis old apart lift (k+1) a a aw aw w
    exact free a L' (pos (by omega)) (by omega) w'
  · obtain ⟨b, bm, ab, rest⟩ := uncons w
    have bw : b ∈ W := by
      rcases mem_union.mp bm with h | h
      · exact h
      · exact absurd ab (apart a an b h)
    rcases Nat.eq_zero_or_pos k with k0 | kpos
    · subst k0
      cases rest
      exact disjoint_left.mp dis bw an
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨u, wu, _, ua⟩ := rest.unsnoc
    have uw : u ∈ W := by
      rcases wu.end_mem_or with e | h
      · rw [e]
        exact bw
      · rcases mem_union.mp h with h | h
        · exact h
        · exact absurd ua (apart u h a an)
    obtain ⟨m, m1, m2, wm⟩ := lift u uw a an b bw ua ab
    obtain ⟨L', le, _, w'⟩ := lift_walk wv dis old apart lift k' b u bw uw wu
    exact free b (L' + m) (by omega) (by omega) (w'.append wm)

/-- **Copies.** Fresh copies `N` of a set `K ⊆ V`: a retained row enters a copy only if it heads
some member of `K`, and a copy leaves only to labels every member of `K` heads. The graph with the
copies is `q`-free. -/
theorem copy_lift {G : CH.Digraph} {W N K : Finset ℕ} (free : QFree D V q) (wv : W ⊆ V)
    (kv : K ⊆ V) (dis : Disjoint W N)
    (old : ∀ a ∈ W, ∀ b ∈ W, G a b = true → D a b = true)
    (apart : ∀ i ∈ N, ∀ j ∈ N, G i j ≠ true)
    (enter : ∀ u ∈ W, ∀ i ∈ N, G u i = true → ∃ k ∈ K, D u k = true)
    (leave : ∀ i ∈ N, ∀ b ∈ W, G i b = true → ∀ k ∈ K, D k b = true) :
    QFree G (W ∪ N) q :=
  fresh_lift free wv dis old apart (fun u _ i iN b bw ui ib => by
    obtain ⟨k, kK, uk⟩ := enter u ‹u ∈ W› i iN ui
    exact ⟨2, by omega, le_rfl, .step (kv kK) uk (.step (wv bw) (leave i iN b bw ib k kK) (.refl b))⟩)

/-! ### The regime theorem -/

/-- A subgraph of a `q`-free digraph is `q`-free. -/
theorem free_sub {E : CH.Digraph} (free : QFree D V q) (sub : ∀ a b, E a b = true → D a b = true) :
    QFree E V q := by
  have move : ∀ {a b m}, Walk E V a b m → Walk D V a b m := by
    intro a b m w
    induction w with
    | refl a => exact .refl a
    | step hb hab _ ih => exact .step hb (sub _ _ hab) ih
  exact fun a l h1 h2 w => free a l h1 h2 (move w)

/-- **Thinning.** Minimum outdegree `r` contains exact outdegree `r`. -/
theorem thin {r : ℕ} (degree : ∀ v ∈ V, r ≤ (outN D V v).card) :
    ∃ E : CH.Digraph, (∀ a b, E a b = true → D a b = true) ∧ ∀ v ∈ V, (outN E V v).card = r := by
  classical
  have pick : ∀ v, ∃ S : Finset ℕ, S ⊆ outN D V v ∧ (v ∈ V → S.card = r) := by
    intro v
    by_cases vv : v ∈ V
    · obtain ⟨S, sub, card⟩ := exists_subset_card_eq (degree v vv)
      exact ⟨S, sub, fun _ => card⟩
    · exact ⟨∅, empty_subset _, fun h => absurd h vv⟩
  choose S sub card using pick
  refine ⟨fun a b => decide (b ∈ S a), fun a b h => ?_, fun v vv => ?_⟩
  · exact (mem_outN.mp (sub a (of_decide_eq_true h))).2
  · have e : outN (fun a b => decide (b ∈ S a)) V v = S v := by
      ext b
      simp only [mem_outN, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨(mem_outN.mp (sub v h)).1, h⟩⟩
    rw [e]
    exact card v vv

/-- **Pair deletion.** A pair with no common parent is closed. -/
theorem pair_closed {a b : ℕ} (none : ∀ u ∈ V, ¬ (D u a = true ∧ D u b = true)) :
    OneLoss D V {a, b} := by
  intro u hu
  rw [card_le_one]
  intro x hx y hy
  obtain ⟨xm, ux⟩ := mem_outN.mp hx
  obtain ⟨ym, uy⟩ := mem_outN.mp hy
  have uv := (mem_sdiff.mp hu).1
  rcases mem_insert.mp xm with ex | ex <;> rcases mem_insert.mp ym with ey | ey
  · rw [ex, ey]
  · rw [mem_singleton] at ey
    rw [ex] at ux
    rw [ey] at uy
    exact absurd ⟨ux, uy⟩ (none u uv)
  · rw [mem_singleton] at ex
    rw [ex] at ux
    rw [ey] at uy
    exact absurd ⟨uy, ux⟩ (none u uv)
  · rw [mem_singleton] at ex ey
    rw [ex, ey]

/-- **Pair regime.** No `q`-free digraph of minimum outdegree `r` on `n` labels exists when
`NoHost q (r-1)`, `2 ≤ r`, `1 ≤ q`, `n ≤ q (r-1) + 2` and `r (r-1) < n - 1`. Below
`q (r-1) + 2` a singleton is a closed deletion; at `q (r-1) + 2` every pair needs a common
parent, and `n` rows of exact degree `r` cover at most `n r (r-1)` ordered pairs. -/
theorem pair_regime {r n : ℕ} (free : QFree D V q) (degree : ∀ v ∈ V, r ≤ (outN D V v).card)
    (size : V.card = n) (lower : NoHost q (r - 1))
    (arith : 2 ≤ r ∧ 1 ≤ q ∧ n ≤ q * (r - 1) + 2 ∧ r * (r - 1) < n - 1) : False := by
  classical
  obtain ⟨hr, hq, top, count⟩ := arith
  obtain ⟨E, sub, exact⟩ := thin degree
  have freeE := free_sub free sub
  have degE : ∀ v ∈ V, r ≤ (outN E V v).card := fun v vv => (exact v vv).ge
  have rr : 2 ≤ r * (r - 1) := by
    have := Nat.mul_le_mul hr (show 1 ≤ r - 1 by omega)
    omega
  have common : ∀ a ∈ V, ∀ b ∈ V, a ≠ b → ∃ u ∈ V, E u a = true ∧ E u b = true := by
    intro a av b bv ne
    by_contra! none
    have closed := pair_closed (D := E) (V := V) (a := a) (b := b)
      (fun u uv h => none u uv h.1 h.2)
    have sub2 : ({a, b} : Finset ℕ) ⊆ V := insert_subset av (singleton_subset_iff.mpr bv)
    have two : ({a, b} : Finset ℕ).card = 2 := card_pair ne
    have rest : (V \ {a, b}).Nonempty := by
      have := card_sdiff_of_subset sub2
      exact card_pos.mp (by omega)
    exact closed_exit lower freeE degE sub2 closed rest (by omega)
  have cover : V.offDiag ⊆ V.biUnion (fun u => (outN E V u).offDiag) := by
    intro p hp
    obtain ⟨p1, p2, ne⟩ := mem_offDiag.mp hp
    obtain ⟨u, uv, ua, ub⟩ := common p.1 p1 p.2 p2 ne
    exact mem_biUnion.mpr ⟨u, uv, mem_offDiag.mpr ⟨mem_outN.mpr ⟨p1, ua⟩, mem_outN.mpr ⟨p2, ub⟩, ne⟩⟩
  have c1 := (card_le_card cover).trans card_biUnion_le
  rw [sum_congr rfl (fun u uv => by rw [offDiag_card, exact u uv]), sum_const, smul_eq_mul,
    offDiag_card, size] at c1
  have e1 : n * n - n = n * (n - 1) := (Nat.mul_sub_one n n).symm
  have e2 : r * r - r = r * (r - 1) := (Nat.mul_sub_one r r).symm
  rw [e1, e2] at c1
  have npos : 0 < n := by omega
  have := Nat.le_of_mul_le_mul_left c1 npos
  omega

#print axioms no_opposite
#print axioms common_head
#print axioms reach_successor
#print axioms heads_sub
#print axioms signature_sub
#print axioms signature_eq
#print axioms orphan
#print axioms forced_port
#print axioms port_cap
#print axioms port_avoid
#print axioms pair_one_head
#print axioms ordinary_loss
#print axioms cross_walk
#print axioms cross_cycle
#print axioms clone_budget
#print axioms cross_count
#print axioms column_cover
#print axioms high_columns
#print axioms few_highs
#print axioms closed_exit
#print axioms closed_extend
#print axioms maximal_parent
#print axioms source_large
#print axioms walk_stays
#print axioms restore_shut
#print axioms partial_restore
#print axioms cycle_walk
#print axioms attach
#print axioms one_tail
#print axioms uncons
#print axioms lift_walk
#print axioms fresh_lift
#print axioms copy_lift
#print axioms free_sub
#print axioms thin
#print axioms pair_closed
#print axioms pair_regime
end LeanCH.BR.SignatureRestoration
