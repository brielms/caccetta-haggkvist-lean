import checkpoints.shen_extension.LawA
import checkpoints.shen_extension.ThirtySix

/-!
# Order 36 at degree nine, cutoff four, unconditionally

No `4`-free digraph with every out-degree at least `9` has `36` labels.

Write `w v = |layer 2 v|`, `T` for the rows with `w ≤ 8` and `H = V \ T` (the rows with
`w ≥ 9`), `h = |H|`. Inputs: Law A (`LawA.law_A_4_9`), hence `ThirtySix.no_seven` (`w ≥ 8`),
`ThirtySix.supply` (a row of `T` has at least `8` heads in `H`), `ThirtySix.high_count`
(`h ≥ 16`), `ThirtySix.indeg_wide` (in-degree `≤ 11` on `H`) and `ThirtySix.budget8`.

Generic part (any `D`, `V`, any `H ⊆ V`, any radius `k` with `QFree D V q`, `2k ≤ q`):

* `seen D V H k a`: the rows of `H` other than `a` within `k` steps of `a`;
  `blind D V H k a`: the rows `b ≠ a` of `H` with `b ∉ ball a k` and `a ∉ ball b k`.
* `mutual_eq`: two labels within `k` steps of each other are equal.
* `pair_count`: `2 ∑_{a ∈ H} |seen a| + ∑_{a ∈ H} |blind a| = |H| (|H| - 1)`.
* `heads_seen`: if `a → t`, the heads of `t` in `H` are seen from `a` (`2 ≤ k`, `2 ≤ q`).
* `shared_head`: two distinct rows `a`, `b` of `H`, not a blind pair, with `|seen a|, |seen b| ≤ c`,
  cannot both see a common set of `c` rows.

The count (`no36_regular`):

1. `|seen a| ≥ 8` on `H`: through a head in `T` (`supply`, `heads_seen`), else all nine heads.
2. `pair_count` at `k = 2`: `16 h ≤ h (h - 1)`, so `h ≥ 17`; `budget8`: `h ≤ 18`.
3. No blind pair in `H`: at `h = 17` by the count, at `h = 18` because `budget8` leaves no gap.
   Then `L = {a ∈ H : |seen a| = 8}` has `|L| ≥ 9 h - h (h - 1) / 2`.
4. `shared_head` with `c = 8`: each row of `T` has at most one parent in `L`.
5. Arcs: `9 |L| ≤ |T| + e(H, H) ≤ |T| + 11 h - 8 |T|`, false at `h = 17` and at `h = 18`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.ThirtySixClose
open Finset BRq2 BRq3 FifthStripAll RigidHost LoopCollar CHRuleCatalog
open DotTwoPassShellTransport (layer)
open HostTwo (inN)

variable {D : CH.Digraph} {V : Finset ℕ} {q : ℕ}

/-! ### Generic: seen rows, blind pairs, the pair count, the shared-head lemma -/

/-- The rows of `H` other than `a` within `k` steps of `a`. -/
noncomputable def seen (D : CH.Digraph) (V H : Finset ℕ) (k a : ℕ) : Finset ℕ :=
  H.filter (fun b => b ≠ a ∧ b ∈ ball D V a k)

/-- The rows `b ≠ a` of `H` that neither see `a` nor are seen from `a` within `k` steps. -/
noncomputable def blind (D : CH.Digraph) (V H : Finset ℕ) (k a : ℕ) : Finset ℕ :=
  H.filter (fun b => b ≠ a ∧ b ∉ ball D V a k ∧ a ∉ ball D V b k)

/-- Two labels within `k` steps of each other are equal (`2k ≤ q`). -/
theorem mutual_eq {k a b : ℕ} (free : QFree D V q) (hk : 2 * k ≤ q) (aV : a ∈ V)
    (ab : b ∈ ball D V a k) (ba : a ∈ ball D V b k) : b = a := by
  have e := ReachLedger.ball_inter_reverse (i := k) (j := k) free (by omega) aV
  have m : b ∈ ball D V a k ∩ reverseBall D V a k :=
    mem_inter.mpr ⟨ab, ReachLedger.mem_reverse.mpr ⟨(mem_ball.mp ab).1, ba⟩⟩
  rw [e] at m
  exact mem_singleton.mp m

/-- One row of the pair count: the other rows of `H` are seen from `a`, see `a`, or are blind. -/
theorem row_split {H : Finset ℕ} {k a : ℕ} (free : QFree D V q) (hk : 2 * k ≤ q) (HV : H ⊆ V)
    (aH : a ∈ H) :
    (seen D V H k a).card + (H.filter (fun b => b ≠ a ∧ a ∈ ball D V b k)).card +
      (blind D V H k a).card = H.card - 1 := by
  classical
  set E := H.filter (fun b => b ≠ a) with hE
  have Ec : E.card = H.card - 1 := by
    rw [hE, filter_ne', card_erase_of_mem aH]
  have s1 := card_filter_add_card_filter_not (s := E) (fun b => b ∈ ball D V a k)
  have s2 := card_filter_add_card_filter_not (s := E.filter (fun b => ¬ b ∈ ball D V a k))
    (fun b => a ∈ ball D V b k)
  have e1 : E.filter (fun b => b ∈ ball D V a k) = seen D V H k a := by
    ext b
    simp only [hE, seen, mem_filter]
    tauto
  have e2 : (E.filter (fun b => ¬ b ∈ ball D V a k)).filter (fun b => a ∈ ball D V b k) =
      H.filter (fun b => b ≠ a ∧ a ∈ ball D V b k) := by
    ext b
    simp only [hE, mem_filter]
    constructor
    · rintro ⟨⟨⟨bH, ne⟩, _⟩, r⟩
      exact ⟨bH, ne, r⟩
    · rintro ⟨bH, ne, r⟩
      exact ⟨⟨⟨bH, ne⟩, fun ab => ne (mutual_eq free hk (HV aH) ab r)⟩, r⟩
  have e3 : (E.filter (fun b => ¬ b ∈ ball D V a k)).filter (fun b => ¬ a ∈ ball D V b k) =
      blind D V H k a := by
    ext b
    simp only [hE, blind, mem_filter]
    tauto
  rw [e1] at s1
  rw [e2, e3] at s2
  omega

/-- **The pair count.** `2 ∑ |seen a| + ∑ |blind a| = |H| (|H| - 1)`. -/
theorem pair_count {H : Finset ℕ} {k : ℕ} (free : QFree D V q) (hk : 2 * k ≤ q) (HV : H ⊆ V) :
    2 * ∑ a ∈ H, (seen D V H k a).card + ∑ a ∈ H, (blind D V H k a).card =
      H.card * (H.card - 1) := by
  classical
  have rows : ∑ a ∈ H, ((seen D V H k a).card +
      (H.filter (fun b => b ≠ a ∧ a ∈ ball D V b k)).card + (blind D V H k a).card) =
      ∑ _a ∈ H, (H.card - 1) := sum_congr rfl (fun a aH => row_split free hk HV aH)
  rw [sum_add_distrib, sum_add_distrib, sum_const, smul_eq_mul] at rows
  have swap : ∑ a ∈ H, (H.filter (fun b => b ≠ a ∧ a ∈ ball D V b k)).card =
      ∑ a ∈ H, (seen D V H k a).card := by
    simp only [seen, card_filter]
    rw [sum_comm]
    refine sum_congr rfl (fun x _ => sum_congr rfl (fun y _ => ?_))
    exact if_congr ⟨fun ⟨h1, h2⟩ => ⟨Ne.symm h1, h2⟩, fun ⟨h1, h2⟩ => ⟨Ne.symm h1, h2⟩⟩ rfl rfl
  rw [swap] at rows
  omega

/-- If `a → t`, the heads of `t` in `H` are seen from `a` (`2 ≤ k`). -/
theorem heads_seen {H : Finset ℕ} {k a t : ℕ} (free : QFree D V q) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (HV : H ⊆ V) (aV : a ∈ V) (tV : t ∈ V) (hat : D a t = true) :
    H.filter (fun b => D t b = true) ⊆ seen D V H k a := by
  intro b hb
  obtain ⟨bH, tb⟩ := mem_filter.mp hb
  refine mem_filter.mpr ⟨bH, fun e => ?_, ball_mono_radius (by omega : 0 + 1 + 1 ≤ k)
    (ball_step (ball_step (self_mem_ball (k := 0) aV) tV hat) (HV bH) tb)⟩
  rw [e] at tb
  exact digonfree free hq aV tV hat tb

/-- The heads of `a` in `H` are seen from `a` (`1 ≤ k`, `1 ≤ q`). -/
theorem out_seen {H : Finset ℕ} {k a : ℕ} (free : QFree D V q) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (HV : H ⊆ V) (aV : a ∈ V) : H.filter (fun b => D a b = true) ⊆ seen D V H k a := by
  intro b hb
  obtain ⟨bH, ab⟩ := mem_filter.mp hb
  refine mem_filter.mpr ⟨bH, fun e => ?_, ball_mono_radius (by omega : 0 + 1 ≤ k)
    (ball_step (self_mem_ball (k := 0) aV) (HV bH) ab)⟩
  rw [e] at ab
  exact loopfree free hq aV ab

/-- **The shared-head lemma.** Two distinct rows `a`, `b` of `H`, not a blind pair, each seeing
at most `c` rows, cannot both see a common set `P` of at least `c` rows. -/
theorem shared_head {H P : Finset ℕ} {c k a b : ℕ} (aH : a ∈ H) (bH : b ∈ H) (ne : a ≠ b)
    (see : b ∈ ball D V a k ∨ a ∈ ball D V b k)
    (Pa : P ⊆ seen D V H k a) (Pb : P ⊆ seen D V H k b) (Pc : c ≤ P.card)
    (ca : (seen D V H k a).card ≤ c) (cb : (seen D V H k b).card ≤ c) : False := by
  have ea := eq_of_subset_of_card_le Pa (by omega)
  have eb := eq_of_subset_of_card_le Pb (by omega)
  rcases see with s | s
  · have m : b ∈ seen D V H k a := mem_filter.mpr ⟨bH, Ne.symm ne, s⟩
    rw [← ea, eb] at m
    exact (mem_filter.mp m).2.1 rfl
  · have m : a ∈ seen D V H k b := mem_filter.mpr ⟨aH, ne, s⟩
    rw [← eb, ea] at m
    exact (mem_filter.mp m).2.1 rfl

/-! ### Order 36 at degree nine -/

/-- **Order 36, out-regular.** No `4`-free digraph with every out-degree `9` has `36` labels. -/
theorem no36_regular (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 36) : False := by
  classical
  have lawA : ThirtySix.LawA D V := fun u hu h => LawA.law_A_4_9 free reg hu h
  have eight := ThirtySix.no_seven free reg n lawA
  have b8 := ThirtySix.budget8 free reg n eight
  have high := ThirtySix.high_count free reg n lawA
  set T := V.filter (fun v => (layer D V 2 v).card ≤ 8) with hT
  set H := V \ T with hH
  have TV : T ⊆ V := filter_subset _ _
  have HV : H ⊆ V := sdiff_subset
  have memH : ∀ v, v ∈ H ↔ v ∈ V ∧ 9 ≤ (layer D V 2 v).card := by
    intro v
    rw [hH, hT, ThirtySix.high_eq, mem_filter]
  have Hc' : (V.filter (fun v => 9 ≤ (layer D V 2 v).card)).card = H.card := by
    rw [hH, hT, ThirtySix.high_eq]
  have Tc : H.card + T.card = 36 := by
    have := card_sdiff_add_card_eq_card TV
    rw [← hH, n] at this
    exact this
  have sup : ∀ t ∈ T, 8 ≤ (H.filter (fun v => D t v = true)).card :=
    fun t ht => ThirtySix.supply free reg lawA (mem_filter.mp ht).1 (mem_filter.mp ht).2
  -- (1) every high row sees at least eight other high rows within two steps
  have S8 : ∀ a ∈ H, 8 ≤ (seen D V H 2 a).card := by
    intro a aH
    have aV := HV aH
    by_cases ex : ∃ t ∈ T, D a t = true
    · obtain ⟨t, tT, hat⟩ := ex
      exact (sup t tT).trans
        (card_le_card (heads_seen free (by norm_num) le_rfl HV aV (TV tT) hat))
    · have sub : outN D V a ⊆ H.filter (fun b => D a b = true) := by
        intro b hb
        obtain ⟨bV, ab⟩ := mem_outN.mp hb
        exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨bV, fun bT => ex ⟨b, bT, ab⟩⟩, ab⟩
      have := (card_le_card sub).trans
        (card_le_card (out_seen (k := 2) free (by norm_num) (by norm_num) HV aV))
      rw [reg a aV] at this
      omega
  -- (2) the pair count, (3) `17 ≤ h ≤ 18`
  have pc := pair_count (k := 2) free (by norm_num) HV
  have sumS : ∑ _a ∈ H, 8 ≤ ∑ a ∈ H, (seen D V H 2 a).card := sum_le_sum S8
  rw [sum_const, smul_eq_mul] at sumS
  have h18 : H.card ≤ 18 := by omega
  have h17 : 17 ≤ H.card := by
    by_contra lt
    have e : H.card = 16 := by omega
    rw [e] at pc sumS
    omega
  -- no blind pair inside `H`
  have Ble : ∑ a ∈ H, (blind D V H 2 a).card ≤ ∑ v ∈ V, (ReachLedger.gap D V 2 2 v).card := by
    refine le_trans (sum_le_sum (fun a _ => card_le_card (fun b hb => ?_)))
      (sum_le_sum_of_subset HV)
    obtain ⟨bH, -, s1, s2⟩ := mem_filter.mp hb
    exact ReachLedger.mem_gap.mpr ⟨HV bH, s1, s2⟩
  have B0 : ∑ a ∈ H, (blind D V H 2 a).card = 0 := by
    rcases (show H.card = 17 ∨ H.card = 18 by omega) with e | e
    · rw [e] at pc sumS
      omega
    · omega
  have SS : 2 * ∑ a ∈ H, (seen D V H 2 a).card = H.card * (H.card - 1) := by omega
  -- (4) the rows seeing exactly eight
  set L := H.filter (fun a => (seen D V H 2 a).card = 8) with hL
  have LH : L ⊆ H := filter_subset _ _
  have Lb : ∑ _a ∈ H, 9 ≤ ∑ a ∈ H, ((seen D V H 2 a).card +
      if (seen D V H 2 a).card = 8 then 1 else 0) :=
    sum_le_sum (fun a aH => by have := S8 a aH; split_ifs <;> omega)
  rw [sum_add_distrib, ← card_filter, ← hL, sum_const, smul_eq_mul] at Lb
  -- (5) each tight row has at most one parent in `L`
  have oneL : ∀ t ∈ T, (L.filter (fun a => D a t = true)).card ≤ 1 := by
    intro t tT
    refine card_le_one.mpr (fun a ha b hb => ?_)
    by_contra ne
    obtain ⟨aL, hat⟩ := mem_filter.mp ha
    obtain ⟨bL, hbt⟩ := mem_filter.mp hb
    obtain ⟨aH, a8⟩ := mem_filter.mp aL
    obtain ⟨bH, b8'⟩ := mem_filter.mp bL
    have see : b ∈ ball D V a 2 ∨ a ∈ ball D V b 2 := by
      by_contra no
      have m : b ∈ blind D V H 2 a :=
        mem_filter.mpr ⟨bH, Ne.symm ne, fun h => no (Or.inl h), fun h => no (Or.inr h)⟩
      have pos := card_pos.mpr ⟨b, m⟩
      have le : (blind D V H 2 a).card ≤ ∑ a ∈ H, (blind D V H 2 a).card :=
        single_le_sum (f := fun a => (blind D V H 2 a).card) (fun _ _ => Nat.zero_le _) aH
      omega
    exact shared_head aH bH ne see
      (heads_seen free (by norm_num) le_rfl HV (HV aH) (TV tT) hat)
      (heads_seen free (by norm_num) le_rfl HV (HV bH) (TV tT) hbt)
      (sup t tT) a8.le b8'.le
  -- (6) the arc count
  have outSplit : ∀ a ∈ V, (T.filter (fun v => D a v = true)).card +
      (H.filter (fun v => D a v = true)).card = 9 := by
    intro a aV
    have split := card_filter_add_card_filter_not (s := outN D V a) (fun v => v ∈ T)
    have e1 : (outN D V a).filter (fun v => v ∈ T) = T.filter (fun v => D a v = true) := by
      ext v
      simp only [mem_filter, mem_outN]
      exact ⟨fun ⟨⟨_, x⟩, y⟩ => ⟨y, x⟩, fun ⟨y, x⟩ => ⟨⟨TV y, x⟩, y⟩⟩
    have e2 : (outN D V a).filter (fun v => v ∉ T) = H.filter (fun v => D a v = true) := by
      ext v
      simp only [mem_filter, mem_outN, hH, mem_sdiff]
      tauto
    rw [e1, e2, reg a aV] at split
    exact split
  have outL : ∑ a ∈ L, (T.filter (fun v => D a v = true)).card +
      ∑ a ∈ L, (H.filter (fun v => D a v = true)).card = 9 * L.card := by
    rw [← sum_add_distrib, sum_congr rfl (fun a aL => outSplit a (HV (LH aL))), sum_const,
      smul_eq_mul, mul_comm]
  have LT : ∑ a ∈ L, (T.filter (fun v => D a v = true)).card ≤ T.card := by
    rw [HostTwo.arcs_between (D := D) L T]
    have := sum_le_sum oneL
    simpa using this
  have LHH : ∑ a ∈ L, (H.filter (fun v => D a v = true)).card ≤
      ∑ v ∈ H, (H.filter (fun u => D u v = true)).card := by
    rw [← HostTwo.arcs_between (D := D) H H]
    exact sum_le_sum_of_subset LH
  have TH : T.card * 8 ≤ ∑ v ∈ H, (T.filter (fun u => D u v = true)).card := by
    rw [← HostTwo.arcs_between (D := D) T H]
    have := sum_le_sum sup
    rw [sum_const, smul_eq_mul] at this
    exact this
  have inH : ∀ v ∈ H, (H.filter (fun u => D u v = true)).card +
      (T.filter (fun u => D u v = true)).card ≤ 11 := by
    intro v vH
    obtain ⟨vV, v9⟩ := (memH v).mp vH
    have disj : Disjoint (H.filter (fun u => D u v = true)) (T.filter (fun u => D u v = true)) :=
      disjoint_filter_filter sdiff_disjoint
    have sub : H.filter (fun u => D u v = true) ∪ T.filter (fun u => D u v = true) ⊆
        inN D V v := by
      intro u hu
      rcases mem_union.mp hu with hu | hu
      · exact mem_filter.mpr ⟨HV (mem_filter.mp hu).1, (mem_filter.mp hu).2⟩
      · exact mem_filter.mpr ⟨TV (mem_filter.mp hu).1, (mem_filter.mp hu).2⟩
    have c := card_le_card sub
    rw [card_union_of_disjoint disj] at c
    have := ThirtySix.indeg_wide free reg n vV v9
    omega
  have sumIn := sum_le_sum inH
  rw [sum_add_distrib, sum_const, smul_eq_mul] at sumIn
  rcases (show H.card = 17 ∨ H.card = 18 by omega) with e | e
  · rw [e] at SS Lb sumIn
    omega
  · rw [e] at SS Lb sumIn
    omega

/-- **Order 36.** No `4`-free digraph of minimum out-degree `9` has `36` labels. -/
theorem no_36 (free : QFree D V 4) (deg : ∀ v ∈ V, 9 ≤ (outN D V v).card) (n : V.card = 36) :
    False := by
  obtain ⟨E, freeE, regE⟩ := CollarBound.exists_regular free deg
  exact no36_regular freeE regE n

/-- No counterexample at degree `9`, cutoff `4` has `36` labels. -/
theorem excluded_36 {p : Input} (bad : Bad p) (hs : p.s = 9) (hc : cutoff p = 4) :
    p.n ≠ 36 := by
  intro hn
  have free : QFree p.D (range p.n) (cutoff p) := qfree_of_noShort bad.loopless bad.missing
  rw [hc] at free
  have deg : ∀ v ∈ range p.n, 9 ≤ (outN p.D (range p.n) v).card := fun v hv => by
    rw [← hs]
    exact Compose.FloorSix.out_card bad.degree (mem_range.mp hv)
  exact no_36 free deg (by rw [card_range, hn])

#print axioms mutual_eq
#print axioms row_split
#print axioms pair_count
#print axioms heads_seen
#print axioms out_seen
#print axioms shared_head
#print axioms no36_regular
#print axioms no_36
#print axioms excluded_36
end LeanCH.BR.ThirtySixClose
