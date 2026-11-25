import checkpoints.shen_extension.EqualLayers

/-!
# The order-`4r` count at cutoff four, degree `r` free

Setting: `QFree D V 4`, out-degree exactly `r` everywhere, `2 ≤ r`, `|V| = 4r`. Write
`w v = (layer D V 2 v).card`, `H` for the rows with `w ≥ r` and `T = V \ H`.

Hypotheses, each generic in `r`:
* (floor) `w ≥ r - 1` everywhere;
* (supply) a row with `w = r - 1` has at least `r - 1` heads in `H`;
* (cap) every row of `H` has in-degree at most `d`;
* (arith) `2 d + 4 < 3 r`.

`four_r`: these are contradictory. The pair budget at radii `(2, 2)` with the floor gives
`|H| ≤ 2r` (`high_le`); `EqualLayers.high_class` at `k = 2`, `c = p = r - 1` gives
`|H| ≥ 2r - 1`, `|L| ≥ (c + 1) h - h (h - 1) / 2`, and `r |L| + (r - 1) |T| ≤ |T| + d |H|`.
At `|H| = 2r`: `|L| ≥ r` and `3r - 4 ≤ 2d`. At `|H| = 2r - 1`: `|L| ≥ 2r - 1` and
`4r² - 4r - 2 ≤ (2r - 1) d`, which with `2d ≤ 3r - 5` would need `2r² + 5r - 9 ≤ 0`.

**Range.** The count closes for every `r ≥ 2` once (floor), (supply) and (cap) hold with
`2d + 4 < 3r`. Law A (`LawA.law_A`, cutoff `q ≥ 4`, `r ≤ 2q + 1`) supplies (supply) at
cutoff four only for `r ≤ 9` (`supply_of_lawA`; it does not need the floor). The two ranges
meet at `r = 9`, where the floor (`ThirtySix.no_seven`) and the cap `d = 11`
(`ThirtySix.indeg_wide`) are the order-36 facts: `no36_from_four_r`. For `r ≥ 10` all three
hypotheses remain open; nothing here proves them.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.FourR
open Finset BRq2 BRq3
open DotTwoPassShellTransport (layer)
open HostTwo (inN)
open ThirtySixClose (seen heads_seen out_seen)

variable {D : CH.Digraph} {V : Finset ℕ} {r : ℕ}

/-- **The pair budget at order `4r`.** With the floor, at most `2r` rows have `w ≥ r`. -/
theorem high_le (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (n : V.card = 4 * r) (floor : ∀ v ∈ V, r ≤ (layer D V 2 v).card + 1) :
    (V.filter (fun v => r ≤ (layer D V 2 v).card)).card ≤ 2 * r := by
  have L := ReachLedger.ledger (D := D) (V := V) (i := 2) (j := 2) free (by norm_num)
  have bb : ∀ v ∈ V, (ball D V v 2).card = (layer D V 2 v).card + (r + 1) := fun v hv => by
    have := (ThinSuppliers.balls_by_layers free (by norm_num) reg hv).2.1
    omega
  have e : ∑ v ∈ V, (ball D V v 2).card = ∑ v ∈ V, (layer D V 2 v).card + V.card * (r + 1) := by
    rw [sum_congr rfl bb, sum_add_distrib, sum_const, smul_eq_mul]
  have A : ∑ v ∈ V, (r + if r ≤ (layer D V 2 v).card then 1 else 0) ≤
      ∑ v ∈ V, ((layer D V 2 v).card + 1) :=
    sum_le_sum (fun v hv => by have := floor v hv; split_ifs <;> omega)
  rw [sum_add_distrib, sum_add_distrib, sum_const, sum_const, smul_eq_mul, smul_eq_mul] at A
  rw [card_filter]
  rw [e, n] at L
  rw [n] at A
  generalize ∑ v ∈ V, (layer D V 2 v).card = S at L A
  generalize ∑ v ∈ V, (ReachLedger.gap D V 2 2 v).card = G at L
  generalize ∑ v ∈ V, (if r ≤ (layer D V 2 v).card then 1 else 0) = h at A ⊢
  nlinarith

/-- **The order-`4r` count.** -/
theorem four_r (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = r) (hr : 2 ≤ r)
    (n : V.card = 4 * r) {d : ℕ}
    (floor : ∀ v ∈ V, r ≤ (layer D V 2 v).card + 1)
    (supply : ∀ u ∈ V, (layer D V 2 u).card + 1 = r →
      r ≤ ((V.filter (fun v => r ≤ (layer D V 2 v).card)).filter (fun v => D u v = true)).card + 1)
    (cap : ∀ v ∈ V, r ≤ (layer D V 2 v).card → (inN D V v).card ≤ d)
    (arith : 2 * d + 4 < 3 * r) : False := by
  classical
  set H := V.filter (fun v => r ≤ (layer D V 2 v).card) with hH
  set T := V \ H with hT
  have HV : H ⊆ V := filter_subset _ _
  have hle := high_le free reg n floor
  rw [← hH] at hle
  have Tc : T.card + H.card = 4 * r := by rw [hT, card_sdiff_add_card_eq_card HV, n]
  have sup : ∀ t ∈ T, r ≤ (H.filter (fun v => D t v = true)).card + 1 := by
    intro t ht
    obtain ⟨tV, tH⟩ := mem_sdiff.mp ht
    have : ¬ r ≤ (layer D V 2 t).card := fun h => tH (mem_filter.mpr ⟨tV, h⟩)
    exact supply t tV (by have := floor t tV; omega)
  have low : ∀ a ∈ H, r - 1 ≤ (seen D V H 2 a).card := by
    intro a aH
    have aV := HV aH
    by_cases ex : ∃ t ∈ T, D a t = true
    · obtain ⟨t, tT, hat⟩ := ex
      have := card_le_card (heads_seen free (by norm_num) le_rfl HV aV
        (mem_sdiff.mp tT).1 hat)
      have := sup t tT
      omega
    · have sub : outN D V a ⊆ H.filter (fun b => D a b = true) := by
        intro b hb
        obtain ⟨bV, ab⟩ := mem_outN.mp hb
        exact mem_filter.mpr ⟨by
          by_contra bH; exact ex ⟨b, mem_sdiff.mpr ⟨bV, bH⟩, ab⟩, ab⟩
      have := (card_le_card sub).trans
        (card_le_card (out_seen (k := 2) free (by norm_num) (by norm_num) HV aV))
      rw [reg a aV] at this
      omega
  obtain ⟨-, big, L, -, -, -, two, -, arcs⟩ :=
    EqualLayers.high_class (k := 2) (c := r - 1) (d := d) (p := r - 1)
    free (by norm_num) reg HV (fun u => H.filter (fun v => D u v = true)) low
    (fun u _ => filter_subset _ _)
    (fun u uT => by have := sup u uT; omega)
    (fun u uT a aH au => by
      have uV : u ∈ V := (mem_sdiff.mp uT).1
      have s := heads_seen (k := 2) free (by norm_num) le_rfl HV (HV aH) uV au
      exact ⟨fun y hy => (mem_filter.mp (s hy)).2.2,
        fun hy => (mem_filter.mp (s hy)).2.1 rfl⟩)
    (fun v vH => cap v (HV vH) (mem_filter.mp vH).2)
    (fun u uT => by have := sup u uT; omega)
  -- `H` is nonempty: otherwise a row of `T` would have `r - 1 ≥ 1` heads in the empty set
  have ne : H.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have : T.card = 4 * r := by rw [← Tc, hne, card_empty, add_zero]
    obtain ⟨t, ht⟩ := card_pos.mp (by omega : 0 < T.card)
    have := sup t ht
    rw [hne, filter_empty, card_empty] at this
    omega
  have hge := big ne
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at two arcs hge
  set l := L.card
  set t := T.card
  rcases (show H.card = 2 * s + 2 ∨ H.card = 2 * s + 1 by omega) with e | e
  · rw [e] at two arcs
    have te : t = 2 * s + 2 := by omega
    rw [te] at arcs
    have h1 : 2 * s + 2 - 1 = 2 * s + 1 := by omega
    rw [h1] at two
    have hl : s + 1 ≤ l := by nlinarith
    have hd : 2 * d + 2 ≤ 3 * s := by omega
    nlinarith [Nat.mul_le_mul_right (s + 1) hl, Nat.mul_le_mul_left (s + 1) hd]
  · rw [e] at two arcs
    have te : t = 2 * s + 3 := by omega
    rw [te] at arcs
    have h1 : 2 * s + 1 - 1 = 2 * s := by omega
    rw [h1] at two
    have hl : 2 * s + 1 ≤ l := by nlinarith
    have hd : 2 * d + 2 ≤ 3 * s := by omega
    nlinarith [Nat.mul_le_mul_right (s + 1) hl, Nat.mul_le_mul_left (2 * s + 1) hd]

/-- **(supply) from Law A**, at any cutoff `q ≥ 4` with `r ≤ 2q + 1`: a root with `w = r - 1`
has at least `r - 1` heads with `w ≥ r`. (No floor is needed.) -/
theorem supply_of_lawA {q : ℕ} (free : QFree D V q) (hq : 4 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = r) (hr : r ≤ 2 * q + 1) {u : ℕ} (hu : u ∈ V)
    (thin : (layer D V 2 u).card + 1 = r) :
    r ≤ ((V.filter (fun v => r ≤ (layer D V 2 v).card)).filter (fun v => D u v = true)).card + 1 := by
  classical
  have la := LawA.law_A free hq reg hu thin hr
  have sub : (outN D V u).filter (fun x => ¬ ((layer D V 2 x).card + 1 ≤ r)) ⊆
      (V.filter (fun v => r ≤ (layer D V 2 v).card)).filter (fun v => D u v = true) := by
    intro x hx
    obtain ⟨xo, xw⟩ := mem_filter.mp hx
    obtain ⟨xV, ux⟩ := mem_outN.mp xo
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨xV, by omega⟩, ux⟩
  have split := card_filter_add_card_filter_not (s := outN D V u)
    (fun x => (layer D V 2 x).card + 1 ≤ r)
  rw [reg u hu] at split
  have := card_le_card sub
  omega

/-- **Order 36 from the order-`4r` count**: `r = 9`, `d = 11`; the floor is
`ThirtySix.no_seven`, the supply `supply_of_lawA`, the cap `ThirtySix.indeg_wide`. -/
theorem no36_from_four_r (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 36) : False := by
  have lawA : ThirtySix.LawA D V := fun u hu h => LawA.law_A_4_9 free reg hu h
  have eight := ThirtySix.no_seven free reg n lawA
  exact four_r (r := 9) (d := 11) free reg (by norm_num) (by rw [n])
    (fun v hv => by have := eight v hv; omega)
    (fun u hu thin => supply_of_lawA free le_rfl reg (by norm_num) hu thin)
    (fun v hv h => ThirtySix.indeg_wide free reg n hv h)
    (by norm_num)

#print axioms high_le
#print axioms four_r
#print axioms supply_of_lawA
#print axioms no36_from_four_r
end LeanCH.BR.FourR
