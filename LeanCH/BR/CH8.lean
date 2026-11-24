import LeanCH.BR.CH8Local
import LeanCH.BR.Reg24

/-!
# CH(8) on at most 24 vertices (Lean 4.35.0)

Paper sources: `checkpoints/boundary_20261111/Z8_attempt_subagent.md`, Corollary 7, Lemma 2 and Theorem 3 (audited in
`Z8_audit_subagent.md`), and `BR38_attempt_subagent.md` (Lemmas 5, 7, 12, Prop 10(c), Prop 16; audited in
`BR38_audit_subagent.md`).

**`ch_eight`.** Every loopless digraph on `n` labels, `0 < n ≤ 24`, with minimum out-degree 8 has a directed cycle of
length at most 3.

Route (Corollary 7 of the Z8 note):
1. Pad a counterexample with sources up to 24 labels (`Boundary.pad`), then saturate it (`no_ce24`, induction on
   non-arcs as in `BR36Disc.br_of_sat`).
2. Add a source `24` heading all of the saturated 24-vertex graph `Q` (`addSrc`). This is a saturated boundary graph
   `D` at `s = 8`; `BR(3,1..7)` gives the strict cap (`StrictCap.strict_cap`), so every vertex of `Q` has
   `in_D ≤ 10`, and `in_D = 10` forces `out_D = 8` (a depth-2 root).
3. `padded_regular`: every vertex of `Q` is a `(9,8)`-vertex of `D`, i.e. `Q` is 8-regular.
4. `Reg24.no_regular_24` (Theorem 3) kills the 8-regular `Q`.

**Departure from the paper in step 3 (economical form of Prop 16 in the padded case).** Write `Z₂` for the number
of depth-2 roots (`(in_D, out_D) = (10, 8)`) in `Q`. Since `D` has the source `24` with excess 24 and `|Q| = 24`, the
degree sum and the cap give exactly
  `Z₂ = Σ_{v ∈ Q, E(v) ≥ 0} (E(v) + 1)`,   with `E = out_D − in_D`
(the step `pos_sum`: `Σ_{v<24} ((out v + 1) − in v) = Z₂`, truncated subtraction). In the paper's terms, the source
receives one R1 unit per root and keeps `#{v ∈ Q : E(v) ≥ 0}` units unused. So it suffices that the depth-2 roots
send 2 units each to vertices `v ∈ Q`, each `v` receiving at most `E(v) + 1`. The `+1` absorbs the one-unit deficit of
the family bound (Lemma 7 with all depths 2), so the equality analysis of Lemma 11 (with the audit's `k = 8` patch),
the full-partner rule R2, all depth-1 rules (R3) and Prop 17 are not needed. Each depth-2 root `u` with
`h_Q(u) := |H(u) ∖ {24}|` sends
* 1 to each `w ∈ H(u) ∖ {24}` (rule R1 restricted to `Q`), and
* `(2 − h_Q(u))⁺` to each `x ∈ K(u)` of out-degree 8 (rule R4, weak form; one such `x` exists by `low_K`).
Receiving bounds: an `H`-receiver has out-degree `≥ 9`, so it gets no `K`-charge, and gets at most `E + 1` by
`SatHyp.H_recv` (the family bound for depth-2 families). A `K`-receiver gets charge from one root only (`K_priv`) and
has `in_D ≤ 7 + h_Q(u)` (`K_in`, `K_out`, no digon in `O(u)`). Hence `2 Z₂ ≤ Z₂`, so `Z₂ = 0`; then the sum above
is 0, so `in_D ≥ out_D + 1` on `Q`, and with `in_D ≤ 9` (no depth-2 root) every vertex of `Q` is `(9, 8)`.
Lemma 4(a) (`ν ≥ 1`) and Lemma 8 (three low vertices) are not used: one low `K`-vertex suffices.
-/

namespace LeanCH.BR.CH8

open CH Compose.Boundary Compose.FloorSix
open LeanCH.BR.BR35 hiding V Hyp Root root_of
open LeanCH.BR.BR36

theorem brs8 : ∀ t, 1 ≤ t → t < 8 → BoundaryRegular 3 t := fun t h1 h2 => by
  rcases (by omega : t < 7 ∨ t = 7) with h | rfl
  · exact LeanCH.BR.BR37.brs7 t h1 h
  · exact LeanCH.BR.BR37.br_seven

/-- The charge sent by `u` to `v`: one unit if `v ∈ H(u) ∖ {24}`, and `(2 − h_Q(u))⁺` if `v ∈ K(u)` has
out-degree 8. -/
def chg (G : CH.Digraph) (u v : Nat) : Nat :=
  (if v ∈ (HS G 8 u).erase 24 then 1 else 0) +
    (if v ∈ KS G 8 u ∧ oc G (VS 8) v = 8 then 2 - ((HS G 8 u).erase 24).card else 0)

theorem VS8 : VS 8 = Finset.range 25 := rfl

/-- **The padded count.** In a saturated boundary graph at `s = 8` with the strict cap, in which the label `24` heads
every other label, every label `v < 24` has in-degree 9 and out-degree 8. -/
theorem padded_regular {G : CH.Digraph} (H : SatHyp 8 G)
    (cap : ∀ v, v < 3 * 8 + 1 → 8 ≤ ic G (VS 8) v →
      3 * (ic G (VS 8) v - 8) + 2 * (oc G (VS 8) v - 8) + 2 ≤ 8)
    (src : ∀ v, v < 24 → G 24 v = true) :
    ∀ v, v < 24 → ic G (VS 8) v = 9 ∧ oc G (VS 8) v = 8 := by
  classical
  -- degree facts from the cap
  have hcap : ∀ v, v < 25 → ic G (VS 8) v ≤ 10 ∧ (ic G (VS 8) v = 10 → oc G (VS 8) v = 8) ∧
      ic G (VS 8) v ≤ oc G (VS 8) v + 2 := by
    intro v hv
    have ho := H.out (show v < 3 * 8 + 1 by omega)
    by_cases h8 : 8 ≤ ic G (VS 8) v
    · have := cap v (by omega) h8
      omega
    · omega
  have to24 : ∀ v, v < 24 → G v 24 = false := fun v hv => H.back (by omega) (by omega) (src v hv)
  -- the source `24`
  have in24 : ic G (VS 8) 24 = 0 := by
    apply ic_eq_zero
    intro v hv
    have hv' := mem_VS.mp hv
    by_cases h : v = 24
    · rw [h]; exact H.loopless 24 (by omega)
    · exact to24 v (by omega)
  have out24 : oc G (VS 8) 24 = 24 := by
    unfold oc
    have : (VS 8).filter (fun w => G 24 w = true) = Finset.range 24 := by
      ext y
      simp only [Finset.mem_filter, mem_VS, Finset.mem_range]
      constructor
      · rintro ⟨hy, hG⟩
        by_contra hy'
        have : y = 24 := by omega
        rw [this, H.loopless 24 (by omega)] at hG
        exact Bool.false_ne_true hG
      · intro hy
        exact ⟨by omega, src y hy⟩
    rw [this, Finset.card_range]
  -- the degree sum over `Q = range 24`
  have hsumQ : ∑ v ∈ Finset.range 24, ic G (VS 8) v = ∑ v ∈ Finset.range 24, oc G (VS 8) v + 24 := by
    have hsum : ∑ v ∈ VS 8, oc G (VS 8) v = ∑ v ∈ VS 8, ic G (VS 8) v :=
      Compose.ThinRigid.sum_out_eq_sum_in G (VS 8)
    have e1 : ∑ v ∈ VS 8, oc G (VS 8) v = ∑ v ∈ Finset.range 24, oc G (VS 8) v + oc G (VS 8) 24 :=
      Finset.sum_range_succ (fun v => oc G (VS 8) v) 24
    have e2 : ∑ v ∈ VS 8, ic G (VS 8) v = ∑ v ∈ Finset.range 24, ic G (VS 8) v + ic G (VS 8) 24 :=
      Finset.sum_range_succ (fun v => ic G (VS 8) v) 24
    omega
  -- depth-2 roots
  set Z := (Finset.range 24).filter (fun u => ic G (VS 8) u = 10) with hZ
  have memZ : ∀ u, u ∈ Z ↔ u < 24 ∧ ic G (VS 8) u = 10 := fun u => by
    rw [hZ, Finset.mem_filter, Finset.mem_range]
  have Zout : ∀ u ∈ Z, oc G (VS 8) u = 8 := fun u hu => by
    obtain ⟨h1, h2⟩ := (memZ u).mp hu
    exact (hcap u (by omega)).2.1 h2
  have ZM : ∀ u ∈ Z, (MM G 8 u).card = 6 := fun u hu => by
    obtain ⟨h1, h2⟩ := (memZ u).mp hu
    have := H.cM (show u < 3 * 8 + 1 by omega)
    have := Zout u hu
    omega
  have src_H : ∀ u, u < 24 → 24 ∈ HS G 8 u := by
    intro u hu
    refine Finset.mem_filter.mpr ⟨mem_II.mpr ⟨by omega, src u hu⟩, fun x hx => ?_⟩
    have hx' := mem_OO.mp hx
    have hx24 : x ≠ 24 := by
      rintro rfl; rw [to24 u hu] at hx'; exact Bool.false_ne_true hx'.2
    exact src x (by omega)
  have Hcard : ∀ u, u < 24 → (HS G 8 u).card = ((HS G 8 u).erase 24).card + 1 := by
    intro u hu
    rw [Finset.card_erase_of_mem (src_H u hu)]
    have := Finset.card_pos.mpr ⟨24, src_H u hu⟩
    omega
  -- each depth-2 root sends at least 2
  have sent : ∀ u ∈ Z, 2 ≤ ∑ v ∈ Finset.range 24, chg G u v := by
    intro u hu
    obtain ⟨hu24, hu10⟩ := (memZ u).mp hu
    have hu' : u < 3 * 8 + 1 := by omega
    obtain ⟨x, hxK, hx8⟩ := H.low_K hu' (by rw [ZM u hu]) (Zout u hu) (by norm_num)
    have hx24 : x < 24 := by
      have hx' := mem_OO.mp (KS_sub hxK)
      by_contra h
      have : x = 24 := by omega
      rw [this, to24 u hu24] at hx'
      exact Bool.false_ne_true hx'.2
    unfold chg
    rw [Finset.sum_add_distrib]
    have hHsub : (HS G 8 u).erase 24 ⊆ Finset.range 24 := by
      intro y hy
      obtain ⟨hy1, hy2⟩ := Finset.mem_erase.mp hy
      have := H.ltI (HS_sub hy2)
      exact Finset.mem_range.mpr (by omega)
    have e1 : ∑ v ∈ Finset.range 24, (if v ∈ (HS G 8 u).erase 24 then 1 else 0) =
        ((HS G 8 u).erase 24).card := by
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hHsub]
    have e2 := Finset.single_le_sum
      (f := fun v => if v ∈ KS G 8 u ∧ oc G (VS 8) v = 8 then 2 - ((HS G 8 u).erase 24).card else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hx24)
    simp only [hxK, hx8, and_self, ite_true] at e2
    omega
  -- each `v ∈ Q` receives at most `(out v + 1) − in v`
  have recv : ∀ v ∈ Finset.range 24, ∑ u ∈ Z, chg G u v ≤ (oc G (VS 8) v + 1) - ic G (VS 8) v := by
    intro v hv
    have hv24 := Finset.mem_range.mp hv
    have hv' : v < 3 * 8 + 1 := by omega
    by_cases hA : ∃ u ∈ Z, v ∈ HS G 8 u
    · -- `H`-receiver
      obtain ⟨u1, hu1, hvH⟩ := hA
      have hv9 : 9 ≤ oc G (VS 8) v := by
        have := H.H_out (show u1 < 3 * 8 + 1 by have := ((memZ u1).mp hu1).1; omega) hvH
        rw [Zout u1 hu1] at this
        exact this
      have e : ∀ u ∈ Z, chg G u v = if v ∈ HS G 8 u then 1 else 0 := by
        intro u _
        unfold chg
        have hK : ¬ (v ∈ KS G 8 u ∧ oc G (VS 8) v = 8) := fun h => by have := h.2; omega
        have hv24' : v ≠ 24 := by omega
        rw [ite_eq_right hK, Nat.add_zero]
        by_cases hvH' : v ∈ HS G 8 u
        · rw [ite_eq_left (Finset.mem_erase.mpr ⟨hv24', hvH'⟩), ite_eq_left hvH']
        · rw [ite_eq_right (fun h => hvH' (Finset.mem_of_mem_erase h)), ite_eq_right hvH']
      rw [Finset.sum_congr rfl e, ← Finset.card_filter]
      have hU := H.H_recv (η := v) (d := 2) (U := Z.filter (fun u => v ∈ HS G 8 u)) hv'
        ⟨u1, Finset.mem_filter.mpr ⟨hu1, hvH⟩⟩ (by
          intro u hu
          obtain ⟨huZ, hvu⟩ := Finset.mem_filter.mp hu
          have := ((memZ u).mp huZ).1
          exact ⟨by omega, hvu, (hcap u (by omega)).2.2⟩)
      omega
    · push Not at hA
      by_cases hB : ∃ u ∈ Z, v ∈ KS G 8 u ∧ oc G (VS 8) v = 8
      · -- `K`-receiver of exactly one root
        obtain ⟨u0, hu0, hvK, hv8⟩ := hB
        obtain ⟨hu024, hu010⟩ := (memZ u0).mp hu0
        have hu0' : u0 < 3 * 8 + 1 := by omega
        rw [Finset.sum_eq_single_of_mem u0 hu0 (fun u hu hne => by
          unfold chg
          have hvH : v ∉ (HS G 8 u).erase 24 := fun h => hA u hu (Finset.mem_of_mem_erase h)
          have hvK' : ¬ (v ∈ KS G 8 u ∧ oc G (VS 8) v = 8) := by
            rintro ⟨hvKu, _⟩
            exact H.K_priv (show u < 3 * 8 + 1 by have := ((memZ u).mp hu).1; omega) hu0' hne
              (by rw [Zout u hu, Zout u0 hu0]) hvKu hvK
          rw [ite_eq_right hvH, ite_eq_right hvK']
          rfl)]
        unfold chg
        have hvH : v ∉ (HS G 8 u0).erase 24 := fun h => hA u0 hu0 (Finset.mem_of_mem_erase h)
        rw [ite_eq_right hvH, ite_eq_left ⟨hvK, hv8⟩]
        have k1 := H.K_in hu0' hvK
        have k2 := H.K_out hu0' hvK
        have k3 := oc_ic_le_mem H.loopless H.noShort H.subO (KS_sub hvK)
        rw [card_OO, Zout u0 hu0] at k3
        have k4 := ZM u0 hu0
        have k5 := Hcard u0 hu024
        omega
      · -- receives nothing
        push Not at hB
        rw [Finset.sum_eq_zero (fun u hu => by
          unfold chg
          have hvH : v ∉ (HS G 8 u).erase 24 := fun h => hA u hu (Finset.mem_of_mem_erase h)
          have hvK' : ¬ (v ∈ KS G 8 u ∧ oc G (VS 8) v = 8) := fun h => hB u hu h.1 h.2
          rw [ite_eq_right hvH, ite_eq_right hvK']
          rfl)]
        exact Nat.zero_le _
  -- `Σ_{v<24} ((out v + 1) − in v) = Z₂`
  have pos_sum : ∑ v ∈ Finset.range 24, ((oc G (VS 8) v + 1) - ic G (VS 8) v) = Z.card := by
    have pw : ∀ v ∈ Finset.range 24, ((oc G (VS 8) v + 1) - ic G (VS 8) v) + ic G (VS 8) v =
        (oc G (VS 8) v + 1) + (if ic G (VS 8) v = 10 then 1 else 0) := by
      intro v hv
      have hv24 := Finset.mem_range.mp hv
      have h := hcap v (by omega)
      have ho := H.out (show v < 3 * 8 + 1 by omega)
      split_ifs with h10
      · have := h.2.1 h10; omega
      · omega
    have S := Finset.sum_congr rfl pw
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, smul_eq_mul, mul_one, ← Finset.card_filter] at S
    rw [hZ]
    omega
  -- double counting
  have S1 : Z.card * 2 ≤ ∑ u ∈ Z, ∑ v ∈ Finset.range 24, chg G u v := card_mul_le_sum sent
  rw [Finset.sum_comm] at S1
  have S2 := Finset.sum_le_sum recv
  rw [pos_sum] at S2
  have hZ0 : Z.card = 0 := by omega
  have hpos0 : ∀ v ∈ Finset.range 24, (oc G (VS 8) v + 1) - ic G (VS 8) v = 0 :=
    (Finset.sum_eq_zero_iff.mp (by rw [pos_sum, hZ0]))
  intro v hv
  have h0 := hpos0 v (Finset.mem_range.mpr hv)
  have hvZ : v ∉ Z := by rw [Finset.card_eq_zero.mp hZ0]; exact Finset.notMem_empty v
  have hne : ic G (VS 8) v ≠ 10 := fun h => hvZ ((memZ v).mpr ⟨hv, h⟩)
  have h := hcap v (by omega)
  have ho := H.out (show v < 3 * 8 + 1 by omega)
  omega

/-! ### The source over a 24-vertex graph -/

/-- `Q` plus a source `24` heading every label `< 24`. -/
def addSrc (G : CH.Digraph) : CH.Digraph :=
  fun a b => if a < 24 then (if b < 24 then G a b else false) else decide (b < 24)

theorem addSrc_lt {G : CH.Digraph} {a b : Nat} (ha : a < 24) (hb : b < 24) : addSrc G a b = G a b := by
  simp [addSrc, ha, hb]

theorem addSrc_src {G : CH.Digraph} {b : Nat} (hb : b < 24) : addSrc G 24 b = true := by
  simp [addSrc, hb]

theorem addSrc_tgt {G : CH.Digraph} {a b : Nat} (h : addSrc G a b = true) : b < 24 := by
  unfold addSrc at h
  by_cases h1 : a < 24
  · rw [ite_eq_left h1] at h
    by_cases h2 : b < 24
    · exact h2
    · rw [ite_eq_right h2] at h; exact absurd h Bool.false_ne_true
  · rw [ite_eq_right h1] at h; exact of_decide_eq_true h

theorem addSrc_out {G : CH.Digraph} {v : Nat} (hv : v < 24) :
    oc (addSrc G) (VS 8) v = ((Finset.range 24).filter (fun w => G v w = true)).card := by
  unfold oc
  congr 1
  ext w
  simp only [Finset.mem_filter, mem_VS, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩
    have hw := addSrc_tgt h
    rw [addSrc_lt hv hw] at h
    exact ⟨hw, h⟩
  · rintro ⟨hw, h⟩
    exact ⟨by omega, by rw [addSrc_lt hv hw]; exact h⟩

theorem addSrc_in {G : CH.Digraph} {v : Nat} (hv : v < 24) :
    ic (addSrc G) (VS 8) v = (par G 24 v).card + 1 := by
  unfold ic
  have : (VS 8).filter (fun u => addSrc G u v = true) = insert 24 (par G 24 v) := by
    ext u
    simp only [Finset.mem_filter, mem_VS, Finset.mem_insert, par, Finset.mem_range]
    constructor
    · rintro ⟨hu, h⟩
      by_cases h24 : u = 24
      · exact Or.inl h24
      · right
        have hu' : u < 24 := by omega
        rw [addSrc_lt hu' hv] at h
        exact ⟨hu', h⟩
    · rintro (rfl | ⟨hu, h⟩)
      · exact ⟨by omega, addSrc_src hv⟩
      · exact ⟨by omega, by rw [addSrc_lt hu hv]; exact h⟩
  rw [this, Finset.card_insert_of_notMem (by simp [par])]

/-- **No saturated counterexample on 24 labels.** -/
theorem no_sat24 {G : CH.Digraph} (loopless : CH.Loopless G 24) (deg : CH.MinOutdegreeAtLeast G 24 8)
    (noShort : ¬ CH.HasDirectedCycleAtMost G 24 3)
    (sat : ∀ a b, a < 24 → b < 24 → a ≠ b → G a b = false → G b a = false →
      ∃ z, z < 24 ∧ G a z = true ∧ G z b = true) : False := by
  have N2 := fun {a b : Nat} => @no2 G 24 loopless noShort a b
  have N3 := fun {a b c : Nat} => @no3 G 24 loopless noShort a b c
  have H : SatHyp 8 (addSrc G) :=
    { loopless := by
        intro a ha
        by_cases h : a < 24
        · rw [addSrc_lt h h]; exact loopless a h
        · simp [addSrc, h]
      deg := by
        intro v hv
        by_cases h : v < 24
        · obtain ⟨l, hlen, hnd, hmem⟩ := deg v h
          refine ⟨l, hlen, hnd, fun w hw => ?_⟩
          obtain ⟨hw24, hG⟩ := hmem w hw
          exact ⟨by omega, by rw [addSrc_lt h hw24]; exact hG⟩
        · have hv24 : v = 24 := by omega
          subst hv24
          refine ⟨List.range 8, List.length_range, List.nodup_range, fun w hw => ?_⟩
          have hw8 := List.mem_range.mp hw
          exact ⟨by omega, addSrc_src (by omega)⟩
      noShort := by
        apply LeanCH.BR.BR36.noShort_of
        · intro a b _ _ e1 e2
          have ha := addSrc_tgt e2
          have hb := addSrc_tgt e1
          rw [addSrc_lt ha hb] at e1
          rw [addSrc_lt hb ha] at e2
          exact N2 ha hb e1 e2
        · intro a b c _ _ _ e1 e2 e3
          have ha := addSrc_tgt e3
          have hb := addSrc_tgt e1
          have hc := addSrc_tgt e2
          rw [addSrc_lt ha hb] at e1
          rw [addSrc_lt hb hc] at e2
          rw [addSrc_lt hc ha] at e3
          exact N3 ha hb hc e1 e2 e3
      sat := by
        intro a b ha hb hab e1 e2
        have ha24 : a < 24 := by
          by_contra h
          have : a = 24 := by omega
          subst this
          rw [addSrc_src (by omega)] at e1
          exact Bool.false_ne_true e1.symm
        have hb24 : b < 24 := by
          by_contra h
          have : b = 24 := by omega
          subst this
          rw [addSrc_src (by omega)] at e2
          exact Bool.false_ne_true e2.symm
        rw [addSrc_lt ha24 hb24] at e1
        rw [addSrc_lt hb24 ha24] at e2
        obtain ⟨z, hz, g1, g2⟩ := sat a b ha24 hb24 hab e1 e2
        exact ⟨z, by omega, by rw [addSrc_lt ha24 hz]; exact g1, by rw [addSrc_lt hz hb24]; exact g2⟩ }
  have reg := padded_regular H
    (fun v hv hin => LeanCH.BR.StrictCap.strict_cap (s := 8) (by norm_num) brs8 H.loopless H.deg H.noShort
      hv hin)
    (fun v hv => addSrc_src hv)
  apply LeanCH.BR.Reg24.no_regular_24 G loopless _ _ noShort
  · intro v hv
    have := (reg v hv).2
    rw [addSrc_out hv] at this
    exact this
  · intro v hv
    have := (reg v hv).1
    rw [addSrc_in hv] at this
    omega

/-- **Saturation.** No counterexample on 24 labels: induction on the number of non-arcs, adding an arc `b → a`
whenever `a, b` are non-adjacent with no path `a → z → b` (as in `BR36Disc.br_of_sat`). -/
theorem no_ce24 : ∀ (k : Nat) (G : CH.Digraph), LeanCH.BR.Reduce.miss G 24 = k →
    CH.Loopless G 24 → CH.MinOutdegreeAtLeast G 24 8 → ¬ CH.HasDirectedCycleAtMost G 24 3 → False := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro G hk loopless deg noShort
  by_cases hsat : ∀ a b, a < 24 → b < 24 → a ≠ b → G a b = false → G b a = false →
      ∃ z, z < 24 ∧ G a z = true ∧ G z b = true
  · exact no_sat24 loopless deg noShort hsat
  · push Not at hsat
    obtain ⟨a, b, ha, hb, hab, gab, gba, hno⟩ := hsat
    have hno' : ∀ z, z < 24 → G a z = true → G z b = false := fun z hz h => by simpa using hno z hz h
    set G' := LeanCH.BR.Reduce.addArc G b a with hG'
    have arc : ∀ x y, G' x y = true → (x = b ∧ y = a) ∨ G x y = true := by
      intro x y h
      simp only [hG', LeanCH.BR.Reduce.addArc] at h
      split_ifs at h with hxy
      · exact Or.inl hxy
      · exact Or.inr h
    have N2 := fun {x y : Nat} => @no2 G 24 loopless noShort x y
    have N3 := fun {x y z : Nat} => @no3 G 24 loopless noShort x y z
    have loop' : CH.Loopless G' 24 := by
      intro w hw
      have : ¬ (w = b ∧ w = a) := fun h => hab (h.2.symm.trans h.1)
      simp only [hG', LeanCH.BR.Reduce.addArc, this]; exact loopless w hw
    have short' : ¬ CH.HasDirectedCycleAtMost G' 24 3 := by
      apply LeanCH.BR.BR36.noShort_of
      · intro x y hx hy e1 e2
        rcases arc x y e1 with ⟨h1, h2⟩ | e1
        · rw [h1, h2] at e2
          rcases arc a b e2 with ⟨h, _⟩ | e2
          · exact hab h
          · rw [gab] at e2; exact Bool.false_ne_true e2
        · rcases arc y x e2 with ⟨h1, h2⟩ | e2
          · rw [h1, h2, gab] at e1; exact Bool.false_ne_true e1
          · exact N2 hx hy e1 e2
      · intro x y z hx hy hz e1 e2 e3
        rcases arc x y e1 with ⟨h1, h2⟩ | e1
        · rw [h2] at e2
          rw [h1] at e3
          have e2' : G a z = true := by
            rcases arc a z e2 with ⟨h, _⟩ | e2
            · exact absurd h hab
            · exact e2
          have e3' : G z b = true := by
            rcases arc z b e3 with ⟨_, h⟩ | e3
            · exact absurd h.symm hab
            · exact e3
          rw [hno' z hz e2'] at e3'; exact Bool.false_ne_true e3'
        · rcases arc y z e2 with ⟨h1, h2⟩ | e2
          · rw [h2] at e3
            rw [h1] at e1
            have e3' : G a x = true := by
              rcases arc a x e3 with ⟨h, _⟩ | e3
              · exact absurd h hab
              · exact e3
            rw [hno' x hx e3'] at e1; exact Bool.false_ne_true e1
          · rcases arc z x e3 with ⟨h1, h2⟩ | e3
            · rw [h2] at e1
              rw [h1] at e2
              rw [hno' y hy e1] at e2; exact Bool.false_ne_true e2
            · exact N3 hx hy hz e1 e2 e3
    have deg' := LeanCH.BR.BR36.minOut_mono (LeanCH.BR.Reduce.addArc_ge G b a) deg
    have hlt := LeanCH.BR.Reduce.miss_lt hb ha (Ne.symm hab) gba
    exact IH _ (hk ▸ hlt) G' rfl loop' deg' short'

/-- **CH(8) on at most 24 vertices.** Every loopless digraph on `n` labels, `0 < n ≤ 24`, with minimum out-degree
at least 8 has a directed cycle of length at most 3. (`n = 0` is excluded: there the degree hypothesis is vacuous
and no cycle exists, `CH.noDirectedCycleAtOrderZero`.) -/
theorem ch_eight : ∀ n, 0 < n → n ≤ 24 → ∀ G : CH.Digraph, CH.Loopless G n →
    CH.MinOutdegreeAtLeast G n 8 → CH.HasDirectedCycleAtMost G n 3 := by
  classical
  intro n hn hn24 G loopless deg
  by_contra noShort
  -- `8 < n`: vertex 0 has 8 distinct out-neighbours in `range n`, none equal to 0
  have hsn : 8 < n := by
    obtain ⟨nbrs, hlen, hnd, hmem⟩ := deg 0 hn
    have hsub : nbrs.toFinset ⊆ (Finset.range n).erase 0 := by
      intro w hw
      obtain ⟨hwn, hG⟩ := hmem w (List.mem_toFinset.mp hw)
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr hwn⟩
      rintro rfl; rw [loopless 0 hn] at hG; exact Bool.false_ne_true hG
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, hlen, Finset.card_erase_of_mem (by simp [hn]),
      Finset.card_range] at this
    omega
  -- pad with sources up to 24 labels; the new labels point to `0, …, 7`
  have ploop : CH.Loopless (pad G n 8) 24 := by
    intro a ha
    by_cases han : a < n
    · simp [pad, han, loopless a han]
    · simp [pad, han]; omega
  have pdeg : CH.MinOutdegreeAtLeast (pad G n 8) 24 8 := by
    intro a ha
    by_cases han : a < n
    · obtain ⟨nbrs, hlen, hnd, hmem⟩ := deg a han
      refine ⟨nbrs, hlen, hnd, fun w hw => ?_⟩
      obtain ⟨hwn, hG⟩ := hmem w hw
      exact ⟨by omega, by simp [pad, han, hwn, hG]⟩
    · refine ⟨List.range 8, List.length_range, List.nodup_range, fun w hw => ?_⟩
      have hws : w < 8 := List.mem_range.mp hw
      exact ⟨by omega, by simp [pad, han, hws]⟩
  have pshort : ¬ CH.HasDirectedCycleAtMost (pad G n 8) 24 3 := by
    rintro ⟨l, cyc, len⟩
    apply noShort
    refine ⟨l, ?_, len⟩
    cases l with
    | nil => exact cyc.elim
    | cons first rest =>
      obtain ⟨restNe, nodup, _, edges, closing⟩ := cyc
      have restLt := edges_lt (le_of_lt hsn) first rest edges
      have firstLt : first < n := pad_target_lt (le_of_lt hsn) closing
      have allLt : ∀ w ∈ first :: rest, w < n := by
        intro w hw; rcases List.mem_cons.mp hw with rfl | hw
        · exact firstLt
        · exact restLt w hw
      have lastLt : rest.getLastD first < n := allLt _ List.getLastD_mem_cons
      refine ⟨restNe, nodup, allLt, edges_transfer first rest firstLt restLt edges, ?_⟩
      have c2 : pad G n 8 (rest.getLastD first) first = true := closing
      unfold pad at c2
      rw [ite_eq_left lastLt, ite_eq_left firstLt] at c2
      exact c2
  exact no_ce24 _ _ rfl ploop pdeg pshort

end LeanCH.BR.CH8
