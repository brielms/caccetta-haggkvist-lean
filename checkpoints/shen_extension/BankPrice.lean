import checkpoints.shen_extension.FullRow
import checkpoints.shen_extension.RowBanks

/-!
# Bank prices on the row `r = 9`, `q = 7` and `q = 8`

`Chain D V r A B C E`: pairwise disjoint `A, B, C, E` (`A, B, C ⊆ V`), rows of `A, B, C` of
out-degree `r` in `V`, rows of `A` with heads in `A ∪ B`, of `B` in `A ∪ B ∪ C`, of `C` in
`A ∪ B ∪ C ∪ E`.

* Q1 `a1` (`q = 7`, `r = 9`, `|A| = 8`): `40 ≤ 2 (|B| + |C|) + |E|`.
  Steps: `|B| ≥ 8` (`keep_two`); `|B| = 8` makes `A` a loop complete to `B`
  (`TopRowFat.loop_complete`), so `B` keeps its heads in `B ∪ C` and `|C| ≥ 8`; `|B| ≥ 9` gives
  `|B| + |C| ≥ 17` (`FragmentBudget.fragment_budget` at radii `(3, 4)` on `A ∪ B`:
  `80 ≤ (17 + t)(2 - t)` fails); `|B| = |C| = 8` makes `B` a loop complete to `C`, `C` keeps its
  heads in `C ∪ E`, `|E| ≥ 8`; otherwise `a1_tail`: `|B| + |C| = 16 + l`, `l ≥ 1`, budget at
  `(3, 4)` on `A ∪ B ∪ C` with `t = 2l`: `160 ≤ (24 + l)(9 - 3l)` fails (`150` at `l = 1`).
* Q2 `b1` (`q = 8`, `r = 9`, `|A| = 8`): `9 ≤ |B|`, `17 ≤ |B| + |C|`, `25 ≤ |B| + |C| + |E|`.
  The last step uses P1 (`FullRow.full_row`, `r + 5 = 14 ≤ 2q = 16`): with
  `|B| + |C| = 17 + t`, the pair budget at radius four on `A ∪ B ∪ C` reads
  `204 ≤ (25 + t)(8 - t)`, false (`200` at `t = 0`).
* Banks (`Bank D V K A`): every row of `K` has exactly one head in `K`, all other heads in `A`,
  `A ∩ K = ∅`, and points to all of `A`.
  Q3 (generic in `q`): `exit_walk`, `no_return` (no row within `j` of a bank row, `j + 1 ≤ q`,
  outside `K`, points into `K`), `ext_one` (`L_1(x) \ K = A`), `ext_heads`, `bank_chain` (the
  exterior layers `L_j(x) \ K`, `j = 1 … 4`, form a chain when `4 ≤ q`), `bank_ball`
  (`|B_k(x)| ≥ (k + 1) + ∑_{j ≤ k} |L_j(x) \ K|`, `k ≤ q`).
* Q4 `a2_bank` (`q = 7`, `r = 9`, `|A| = 8`): `65 ≤ |B_3(x)| + |B_4(x)|`.
* Q5 `b1_bank` (`q = 8`, `r = 9`, `|A| = 8`): `38 ≤ |B_4(x)|`; `b1_thin`: a thin root
  (`|L_2(u)| ≤ 8`) has `43 ≤ |B_5(u)|` (`RowBanks.thin_loop`, `RowBanks.transfer_exact`).
* Q6 `thin_no_return`, `thin_chain`, `a3_thin` (`q = 7`, `r = 9`, `|L_2(u)| = 8`): no arc from
  layers `2 … 5` into `{u} ∪ X` (`Supplier54.no_back_x_g`, `no_back_u_g`), so the layers
  `2 … 5` form a chain and `76 ≤ |B_4(u)| + |B_5(u)|`.
No size of `K` is needed in Q4, Q5.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.BankPrice
open Finset BRq2 BRq3
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)
open Profile54 (reach)

variable {D : CH.Digraph} {q : ℕ} {V : Finset ℕ}

/-- The chain hypothesis. -/
structure Chain (D : CH.Digraph) (V : Finset ℕ) (r : ℕ) (A B C E : Finset ℕ) : Prop where
  AV : A ⊆ V
  BV : B ⊆ V
  CV : C ⊆ V
  dAB : Disjoint A B
  dAC : Disjoint A C
  dAE : Disjoint A E
  dBC : Disjoint B C
  dBE : Disjoint B E
  dCE : Disjoint C E
  degA : ∀ v ∈ A, (outN D V v).card = r
  degB : ∀ v ∈ B, (outN D V v).card = r
  degC : ∀ v ∈ C, (outN D V v).card = r
  kA : ∀ v ∈ A, outN D V v ⊆ A ∪ B
  kB : ∀ v ∈ B, outN D V v ⊆ A ∪ B ∪ C
  kC : ∀ v ∈ C, outN D V v ⊆ A ∪ B ∪ C ∪ E

/-! ### Helpers -/

/-- Rows of `S` of out-degree `r` with heads in `S ∪ T`, `|T| + 2 ≤ r`: `2q + 1 ≤ |S|`. -/
theorem keep_two {S T : Finset ℕ} {r : ℕ} (free : QFree D V q) (hq : 1 ≤ q) (SV : S ⊆ V)
    (ne : S.Nonempty) (deg : ∀ v ∈ S, (outN D V v).card = r)
    (keep : ∀ v ∈ S, outN D V v ⊆ S ∪ T) (hT : T.card + 2 ≤ r) : 2 * q + 1 ≤ S.card :=
  Profile54.two_order (free.mono_set SV) hq ne (fun v hv => by
    have := FragmentBudget.keep_le (keep v hv)
    rw [deg v hv] at this
    omega)

/-- A nonempty set of at most `q` rows of out-degree `r` with heads in `S ∪ T` has a sink in `S`:
`r ≤ |T|`. -/
theorem sink_heads {S T : Finset ℕ} {r : ℕ} (free : QFree D V q) (SV : S ⊆ V) (ne : S.Nonempty)
    (hS : S.card ≤ q) (deg : ∀ v ∈ S, (outN D V v).card = r)
    (keep : ∀ v ∈ S, outN D V v ⊆ S ∪ T) : r ≤ T.card := by
  by_contra h
  have d1 : ∀ v ∈ S, 1 ≤ (outN D S v).card := fun v hv => by
    have := FragmentBudget.keep_le (keep v hv)
    rw [deg v hv] at this
    omega
  obtain ⟨x, hx⟩ := ne
  have g := LoopCollar.ball_grow (free.mono_set SV) d1 hx q le_rfl
  have := card_le_card (ball_subset (D := D) (W := S) (u := x) (k := q))
  omega

/-- Out-rows kept inside the fragment. -/
theorem keep_out {F : Finset ℕ} (FV : F ⊆ V) {v : ℕ} (keep : outN D V v ⊆ F) :
    outN D F v = outN D V v := Profile54.out_restrict FV keep

/-! ### Q1 -/

/-- **Q1, the last step.** `|A| = 8`, `|B| ≥ 8`, `|B| + |C| ≥ 17` (`q = 7`, `r = 9`).
With `|B| + |C| = 16 + l` and `|E| ≤ 7 - 2l` the fragment `A ∪ B ∪ C` (`24 + l` labels, at
least `16` full rows, minimum `2 + 2l`) breaks the budget at radii `(3, 4)`:
`160 ≤ (24 + l)(9 - 3l)`, false for `l ≥ 1` (`150` at `l = 1`). -/
theorem a1_tail {A B C E : Finset ℕ} (free : QFree D V 7) (ch : Chain D V 9 A B C E)
    (hA : A.card = 8) (hB : 8 ≤ B.card) (h17 : 17 ≤ B.card + C.card) :
    40 ≤ 2 * (B.card + C.card) + E.card := by
  classical
  by_contra hlt
  obtain ⟨l, hl⟩ : ∃ l, B.card + C.card = 16 + l := ⟨B.card + C.card - 16, by omega⟩
  have l1 : 1 ≤ l := by omega
  have hE : E.card + 2 * l ≤ 7 := by omega
  have FV : A ∪ B ∪ C ⊆ V := union_subset (union_subset ch.AV ch.BV) ch.CV
  have dABC : Disjoint (A ∪ B) C := disjoint_union_left.mpr ⟨ch.dAC, ch.dBC⟩
  have ABc : (A ∪ B).card = 8 + B.card := by rw [card_union_of_disjoint ch.dAB, hA]
  have Fc : (A ∪ B ∪ C).card = 24 + l := by rw [card_union_of_disjoint dABC]; omega
  have fullA : ∀ v ∈ A, outN D (A ∪ B ∪ C) v = outN D V v := fun v hv =>
    keep_out FV (fun w hw => mem_union_left _ (ch.kA v hv hw))
  have fullB : ∀ v ∈ B, outN D (A ∪ B ∪ C) v = outN D V v := fun v hv => keep_out FV (ch.kB v hv)
  have full : ∀ v ∈ A ∪ B, (outN D (A ∪ B ∪ C) v).card = 9 := by
    intro v hv
    rcases mem_union.mp hv with h | h
    · rw [fullA v h, ch.degA v h]
    · rw [fullB v h, ch.degB v h]
  have deg : ∀ v ∈ A ∪ B ∪ C, 2 + 2 * l ≤ (outN D (A ∪ B ∪ C) v).card := by
    intro v hv
    rcases mem_union.mp hv with h | h
    · rw [full v h]; omega
    · have := FragmentBudget.keep_le (ch.kC v h)
      rw [ch.degC v h] at this
      omega
  have fb := FragmentBudget.fragment_budget (i := 3) (j := 4) (r := 9) (t := 2 * l)
    (Fs := A ∪ B) (free.mono_set FV) deg subset_union_left full (by norm_num)
    (by rw [Fc]; omega) le_rfl (by norm_num) (by norm_num)
  have e : (9 : ℕ) + 3 - (3 + 4) = 5 := by norm_num
  rw [Fc, e, show 24 + l - 1 = 23 + l by omega] at fb
  have AB : 16 ≤ (A ∪ B).card := by omega
  nlinarith [fb, AB, l1]

/-- **Q1 (A1).** `q = 7`, `r = 9`, a chain with `|A| = 8`: `40 ≤ 2 (|B| + |C|) + |E|`. -/
theorem a1 {A B C E : Finset ℕ} (free : QFree D V 7) (ch : Chain D V 9 A B C E)
    (hA : A.card = 8) : 40 ≤ 2 * (B.card + C.card) + E.card := by
  classical
  have Ane : A.Nonempty := card_pos.mp (by omega)
  have hB : 8 ≤ B.card := by
    by_contra h
    have := keep_two free (by norm_num) ch.AV Ane ch.degA ch.kA (by omega)
    omega
  by_cases B8 : B.card = 8
  · have LA := TopRowFat.loop_complete free (by norm_num) ch.AV (by rw [hA]) ch.dAB (by omega)
      ch.degA ch.kA
    have noBA : ∀ b ∈ B, ∀ a ∈ A, ¬ D b a = true := fun b hb a ha ba =>
      digonfree free (by norm_num) (ch.AV ha) (ch.BV hb) (mem_outN.mp ((LA a ha).2.1 hb)).2 ba
    have kB' : ∀ b ∈ B, outN D V b ⊆ B ∪ C := fun b hb w hw => by
      rcases mem_union.mp (ch.kB b hb hw) with h | h
      · rcases mem_union.mp h with h | h
        · exact absurd (mem_outN.mp hw).2 (noBA b hb w h)
        · exact mem_union_left _ h
      · exact mem_union_right _ h
    have Bne : B.Nonempty := card_pos.mp (by omega)
    have hC : 8 ≤ C.card := by
      by_contra h
      have := keep_two free (by norm_num) ch.BV Bne ch.degB kB' (by omega)
      omega
    by_cases C8 : C.card = 8
    · have LB := TopRowFat.loop_complete free (by norm_num) ch.BV (by rw [B8]) ch.dBC (by omega)
        ch.degB kB'
      obtain ⟨b0, hb0⟩ := Bne
      have noC : ∀ c ∈ C, ∀ w ∈ A ∪ B, ¬ D c w = true := by
        intro c hc w hw cw
        rcases mem_union.mp hw with wa | wb
        · have wb0 := (mem_outN.mp ((LA w wa).2.1 hb0)).2
          have b0c := (mem_outN.mp ((LB b0 hb0).2.1 hc)).2
          exact free w 3 (by norm_num) (by norm_num)
            (.step (ch.BV hb0) wb0 (.step (ch.CV hc) b0c (.step (ch.AV wa) cw (.refl w))))
        · exact digonfree free (by norm_num) (ch.BV wb) (ch.CV hc)
            (mem_outN.mp ((LB w wb).2.1 hc)).2 cw
      have kC' : ∀ c ∈ C, outN D V c ⊆ C ∪ E := fun c hc w hw => by
        rcases mem_union.mp (ch.kC c hc hw) with h | h
        · rcases mem_union.mp h with h | h
          · exact absurd (mem_outN.mp hw).2 (noC c hc w h)
          · exact mem_union_left _ h
        · exact mem_union_right _ h
      have hE : 8 ≤ E.card := by
        by_contra h
        have := keep_two free (by norm_num) ch.CV (card_pos.mp (by omega)) ch.degC kC' (by omega)
        omega
      omega
    · exact a1_tail free ch hA hB (by omega)
  · have h17 : 17 ≤ B.card + C.card := by
      by_contra h
      obtain ⟨t, ht⟩ : ∃ t, B.card = 9 + t := ⟨B.card - 9, by omega⟩
      have FV : A ∪ B ⊆ V := union_subset ch.AV ch.BV
      have Fc : (A ∪ B).card = 17 + t := by rw [card_union_of_disjoint ch.dAB]; omega
      have fullA : ∀ v ∈ A, (outN D (A ∪ B) v).card = 9 := fun v hv => by
        rw [keep_out FV (ch.kA v hv), ch.degA v hv]
      have deg : ∀ v ∈ A ∪ B, 2 + t ≤ (outN D (A ∪ B) v).card := by
        intro v hv
        rcases mem_union.mp hv with h' | h'
        · rw [fullA v h']; omega
        · have := FragmentBudget.keep_le (ch.kB v h')
          rw [ch.degB v h'] at this
          omega
      have fb := FragmentBudget.fragment_budget (i := 3) (j := 4) (r := 9) (t := t) (Fs := A)
        (free.mono_set FV) deg subset_union_left fullA (by norm_num) (by rw [Fc]; omega) le_rfl
        (by norm_num) (by norm_num)
      have e : (9 : ℕ) + 3 - (3 + 4) = 5 := by norm_num
      rw [Fc, hA, e, show 17 + t - 1 = 16 + t by omega] at fb
      nlinarith [fb]
    exact a1_tail free ch hA hB h17

/-! ### Q2 -/

/-- **Q2 (B1).** `q = 8`, `r = 9`, a chain with `|A| = 8`:
`9 ≤ |B|`, `17 ≤ |B| + |C|`, `25 ≤ |B| + |C| + |E|`. The last bound uses P1 at radius four
(`r + 5 = 14 ≤ 16 = 2q`); its margin is `204` against `200`. -/
theorem b1 {A B C E : Finset ℕ} (free : QFree D V 8) (ch : Chain D V 9 A B C E)
    (hA : A.card = 8) :
    9 ≤ B.card ∧ 17 ≤ B.card + C.card ∧ 25 ≤ B.card + C.card + E.card := by
  classical
  have Ane : A.Nonempty := card_pos.mp (by omega)
  have hB : 9 ≤ B.card := sink_heads free ch.AV Ane (by omega) ch.degA ch.kA
  have h17 : 17 ≤ B.card + C.card := by
    by_contra h
    obtain ⟨t, ht⟩ : ∃ t, B.card = 9 + t := ⟨B.card - 9, by omega⟩
    have FV : A ∪ B ⊆ V := union_subset ch.AV ch.BV
    have Fc : (A ∪ B).card = 17 + t := by rw [card_union_of_disjoint ch.dAB]; omega
    have fullA : ∀ v ∈ A, (outN D (A ∪ B) v).card = 9 := fun v hv => by
      rw [keep_out FV (ch.kA v hv), ch.degA v hv]
    have deg : ∀ v ∈ A ∪ B, 2 + t ≤ (outN D (A ∪ B) v).card := by
      intro v hv
      rcases mem_union.mp hv with h' | h'
      · rw [fullA v h']; omega
      · have := FragmentBudget.keep_le (ch.kB v h')
        rw [ch.degB v h'] at this
        omega
    have fb := FragmentBudget.fragment_budget (i := 4) (j := 4) (r := 9) (t := t) (Fs := A)
      (free.mono_set FV) deg subset_union_left fullA (by norm_num) (by rw [Fc]; omega)
      (by norm_num) (by norm_num) (by norm_num)
    have e : (9 : ℕ) + 3 - (4 + 4) = 4 := by norm_num
    rw [Fc, hA, e, show 17 + t - 1 = 16 + t by omega] at fb
    nlinarith [fb]
  refine ⟨hB, h17, ?_⟩
  by_contra hlt
  obtain ⟨t, ht⟩ : ∃ t, B.card + C.card = 17 + t := ⟨B.card + C.card - 17, by omega⟩
  have hE : E.card + t ≤ 7 := by omega
  have FV : A ∪ B ∪ C ⊆ V := union_subset (union_subset ch.AV ch.BV) ch.CV
  have dABC : Disjoint (A ∪ B) C := disjoint_union_left.mpr ⟨ch.dAC, ch.dBC⟩
  have ABc : (A ∪ B).card = 8 + B.card := by rw [card_union_of_disjoint ch.dAB, hA]
  have Fc : (A ∪ B ∪ C).card = 25 + t := by rw [card_union_of_disjoint dABC]; omega
  have fr : QFree D (A ∪ B ∪ C) 8 := free.mono_set FV
  have full : ∀ v ∈ A ∪ B, (outN D (A ∪ B ∪ C) v).card = 9 := by
    intro v hv
    rcases mem_union.mp hv with h | h
    · rw [keep_out FV (fun w hw => mem_union_left _ (ch.kA v h hw)), ch.degA v h]
    · rw [keep_out FV (ch.kB v h), ch.degB v h]
  have deg : ∀ v ∈ A ∪ B ∪ C, 2 + t ≤ (outN D (A ∪ B ∪ C) v).card := by
    intro v hv
    rcases mem_union.mp hv with h | h
    · rw [full v h]; omega
    · have := FragmentBudget.keep_le (ch.kC v h)
      rw [ch.degC v h] at this
      omega
  have fs := FragmentBudget.floor_sum
    (c := fun v => reach D (A ∪ B ∪ C) 4 v + reach D (A ∪ B ∪ C) 4 v)
    (base := 2 * (8 + t)) (e := 12) (S := A ∪ B) subset_union_left
    (fun v hv => by
      have := FragmentBudget.ordinary_floor (i := 4) fr (by norm_num) (by norm_num) deg hv
      omega)
    (fun v hv => by
      have := FullRow.full_row (i := 4) (r := 9) (t := t) fr le_rfl (by norm_num)
        (by rw [Fc]; omega) deg (subset_union_left hv) (full v hv)
      omega)
    (FragmentBudget.mixed_budget (i := 4) (j := 4) fr (by norm_num))
  rw [Fc, show 25 + t - 1 = 24 + t by omega] at fs
  have AB : 17 ≤ (A ∪ B).card := by omega
  nlinarith [fs, AB]

/-! ### Banks: Q3 -/

/-- A bank: rows of `K` have exactly one head in `K`, all other heads in `A`, `K ∩ A = ∅`, and
every row of `K` points to all of `A`. -/
structure Bank (D : CH.Digraph) (V K A : Finset ℕ) : Prop where
  KV : K ⊆ V
  dis : Disjoint K A
  one : ∀ k ∈ K, (outN D K k).card = 1
  keep : ∀ k ∈ K, outN D V k ⊆ K ∪ A
  full : ∀ k ∈ K, A ⊆ outN D V k

/-- **Exit.** If rows of `K` keep their heads in `K ∪ A`, a walk from `K` to a label outside `K`
passes through `A`: the label is reached from some `a ∈ A` in fewer steps. -/
theorem exit_walk {K A : Finset ℕ} (keep : ∀ k ∈ K, outN D V k ⊆ K ∪ A) :
    ∀ n s y, s ∈ K → y ∉ K → Walk D V s y n → ∃ a ∈ A, ∃ m, m + 1 ≤ n ∧ Walk D V a y m := by
  intro n
  induction n with
  | zero =>
    intro s y hs hy w
    cases w
    exact absurd hs hy
  | succ n ih =>
    intro s y hs hy w
    cases w with
    | step bV sb rest =>
      rcases mem_union.mp (keep s hs (mem_outN.mpr ⟨bV, sb⟩)) with bK | bA
      · obtain ⟨a, ha, m, hm, w'⟩ := ih _ y bK hy rest
        exact ⟨a, ha, m, by omega, w'⟩
      · exact ⟨_, bA, n, le_rfl, rest⟩

/-- **Q3: no exterior return** (generic). A row within `j` of a bank row `x`, `j + 1 ≤ q`, outside
`K`, points to no row of `K`: from its entry `a ∈ A`, `a ⇝ y → k → a` has length `≤ j + 1`. -/
theorem no_return {K A : Finset ℕ} (free : QFree D V q) (bank : Bank D V K A) {x : ℕ}
    (hx : x ∈ K) {j : ℕ} (hj : j + 1 ≤ q) {y : ℕ} (hy : y ∈ ball D V x j) (yK : y ∉ K)
    {k : ℕ} (hk : k ∈ K) : ¬ D y k = true := by
  intro yk
  obtain ⟨-, n, hn, w⟩ := mem_ball.mp hy
  obtain ⟨a, ha, m, hm, wa⟩ := exit_walk bank.keep n x y hx yK w
  have ka := mem_outN.mp (bank.full k hk ha)
  exact free a (m + 1 + 1) (by omega) (by omega) ((wa.snoc (bank.KV hk) yk).snoc ka.1 ka.2)

/-- A label within `m` of `u` and not within `k` lies in a layer `i`, `k < i ≤ m`. -/
theorem layer_between {u m k w : ℕ} (hw : w ∈ ball D V u m) (hk : w ∉ ball D V u k) :
    ∃ i, k < i ∧ i ≤ m ∧ w ∈ layer D V i u := by
  induction m with
  | zero => exact absurd (ball_mono_radius (Nat.zero_le k) hw) hk
  | succ m ih =>
    by_cases h : w ∈ ball D V u m
    · obtain ⟨i, h1, h2, h3⟩ := ih h
      exact ⟨i, h1, by omega, h3⟩
    · refine ⟨m + 1, ?_, le_rfl, mem_layer.mpr ⟨hw, by rw [Nat.add_sub_cancel]; exact h⟩⟩
      by_contra hc
      exact hk (ball_mono_radius (by omega) hw)

/-- **Q3, `E_1 = A`.** The first layer of a bank row outside `K` is `A` (`1 ≤ q`). -/
theorem ext_one {K A : Finset ℕ} (free : QFree D V q) (hq : 1 ≤ q) (bank : Bank D V K A)
    {x : ℕ} (hx : x ∈ K) : layer D V 1 x \ K = A := by
  rw [ShapeClimbRoot.layer_one free hq (bank.KV hx)]
  ext w
  constructor
  · intro h
    obtain ⟨hw, wK⟩ := mem_sdiff.mp h
    exact (mem_union.mp (bank.keep x hx hw)).resolve_left wK
  · intro h
    exact mem_sdiff.mpr ⟨bank.full x hx h, disjoint_right.mp bank.dis h⟩

/-- **Q3, heads of exterior rows** (generic, `j + 1 ≤ q`). A head of a row of `L_j(x) \ K` lies in
some `L_i(x) \ K`, `1 ≤ i ≤ j + 1`. -/
theorem ext_heads {K A : Finset ℕ} (free : QFree D V q) (bank : Bank D V K A) {x : ℕ}
    (hx : x ∈ K) {j : ℕ} (hj : j + 1 ≤ q) {v : ℕ} (hv : v ∈ layer D V j x \ K) {w : ℕ}
    (hw : w ∈ outN D V v) : ∃ i, 1 ≤ i ∧ i ≤ j + 1 ∧ w ∈ layer D V i x \ K := by
  obtain ⟨hvl, vK⟩ := mem_sdiff.mp hv
  obtain ⟨wV, vw⟩ := mem_outN.mp hw
  have vb : v ∈ ball D V x j := (mem_layer.mp hvl).1
  have wb := ball_step vb wV vw
  have wK : w ∉ K := fun h => no_return free bank hx hj vb vK h vw
  have w0 : w ∉ ball D V x 0 := by
    intro h
    obtain ⟨-, n, hn, wk⟩ := mem_ball.mp h
    obtain rfl : n = 0 := by omega
    cases wk
    exact wK hx
  obtain ⟨i, h1, h2, h3⟩ := layer_between wb w0
  exact ⟨i, h1, h2, mem_sdiff.mpr ⟨h3, wK⟩⟩

theorem ext_disj {K : Finset ℕ} {x i j : ℕ} (h : i < j) :
    Disjoint (layer D V i x \ K) (layer D V j x \ K) :=
  Disjoint.mono sdiff_subset sdiff_subset (FragmentBudget.layer_disj h)

/-- **Q3, the exterior chain** (generic, `4 ≤ q`). The exterior layers `L_1(x) \ K = A`, …,
`L_4(x) \ K` of a bank row form a chain. -/
theorem bank_chain {K A : Finset ℕ} {r : ℕ} (free : QFree D V q) (hq : 4 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = r) (bank : Bank D V K A) {x : ℕ} (hx : x ∈ K) :
    Chain D V r (layer D V 1 x \ K) (layer D V 2 x \ K) (layer D V 3 x \ K)
      (layer D V 4 x \ K) where
  AV := fun _ hv => layer_subset (mem_sdiff.mp hv).1
  BV := fun _ hv => layer_subset (mem_sdiff.mp hv).1
  CV := fun _ hv => layer_subset (mem_sdiff.mp hv).1
  dAB := ext_disj (by norm_num)
  dAC := ext_disj (by norm_num)
  dAE := ext_disj (by norm_num)
  dBC := ext_disj (by norm_num)
  dBE := ext_disj (by norm_num)
  dCE := ext_disj (by norm_num)
  degA := fun v hv => reg v (layer_subset (mem_sdiff.mp hv).1)
  degB := fun v hv => reg v (layer_subset (mem_sdiff.mp hv).1)
  degC := fun v hv => reg v (layer_subset (mem_sdiff.mp hv).1)
  kA := fun v hv w hw => by
    obtain ⟨i, h1, h2, h3⟩ := ext_heads free bank hx (j := 1) (by omega) hv hw
    interval_cases i <;> (simp only [mem_union]; tauto)
  kB := fun v hv w hw => by
    obtain ⟨i, h1, h2, h3⟩ := ext_heads free bank hx (j := 2) (by omega) hv hw
    interval_cases i <;> (simp only [mem_union]; tauto)
  kC := fun v hv w hw => by
    obtain ⟨i, h1, h2, h3⟩ := ext_heads free bank hx (j := 3) (by omega) hv hw
    interval_cases i <;> (simp only [mem_union]; tauto)

/-- **Q3, the ball of a bank row** (generic, `k ≤ q`):
`(k + 1) + ∑_{t < k} |L_{t+1}(x) \ K| ≤ |B_k(x)|` (its own walk along `K`, and the exterior). -/
theorem bank_ball {K A : Finset ℕ} (free : QFree D V q) (bank : Bank D V K A) {x : ℕ}
    (hx : x ∈ K) {k : ℕ} (hk : k ≤ q) :
    (k + 1) + ∑ t ∈ range k, (layer D V (t + 1) x \ K).card ≤ (ball D V x k).card := by
  classical
  have A1 := LoopCollar.ball_grow (free.mono_set bank.KV) (fun v hv => (bank.one v hv).ge) hx k hk
  have cU : ((range k).biUnion (fun t => layer D V (t + 1) x \ K)).card =
      ∑ t ∈ range k, (layer D V (t + 1) x \ K).card := by
    apply card_biUnion
    intro t _ t' _ ne
    show Disjoint (layer D V (t + 1) x \ K) (layer D V (t' + 1) x \ K)
    rcases lt_or_gt_of_ne ne with h | h
    · exact ext_disj (by omega)
    · exact (ext_disj (by omega)).symm
  have dis : Disjoint (ball D K x k) ((range k).biUnion (fun t => layer D V (t + 1) x \ K)) := by
    rw [disjoint_left]
    intro v hv hvU
    obtain ⟨t, -, ht⟩ := mem_biUnion.mp hvU
    exact (mem_sdiff.mp ht).2 (ball_subset hv)
  have sub : ball D K x k ∪ (range k).biUnion (fun t => layer D V (t + 1) x \ K) ⊆
      ball D V x k := by
    refine union_subset (FragmentBudget.ball_mono_set bank.KV) (fun v hv => ?_)
    obtain ⟨t, ht, hv'⟩ := mem_biUnion.mp hv
    rw [mem_range] at ht
    exact ball_mono_radius (by omega) (mem_layer.mp (mem_sdiff.mp hv').1).1
  have := card_le_card sub
  rw [card_union_of_disjoint dis, cU] at this
  omega

/-! ### Q4, Q5 -/

/-- **Q4 (A2).** `q = 7`, `r = 9`, a bank with `|A| = 8`: every bank row has
`65 ≤ |B_3(x)| + |B_4(x)|` (`4 + 5 + 2·8 + 2(|E_2| + |E_3|) + |E_4|`, Q1 on `A, E_2, E_3, E_4`). -/
theorem a2_bank {K A : Finset ℕ} (free : QFree D V 7) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (bank : Bank D V K A) (hA : A.card = 8) {x : ℕ} (hx : x ∈ K) :
    65 ≤ (ball D V x 3).card + (ball D V x 4).card := by
  have ch := bank_chain free (by norm_num) reg bank hx
  have c1 : (layer D V 1 x \ K).card = 8 := by rw [ext_one free (by norm_num) bank hx, hA]
  have q1 := a1 free ch c1
  have b3 := bank_ball free bank hx (k := 3) (by norm_num)
  have b4 := bank_ball free bank hx (k := 4) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.reduceAdd] at b3 b4
  omega

/-- **Q5.** `q = 8`, `r = 9`, a bank with `|A| = 8`: every bank row has `38 ≤ |B_4(x)|`
(`5 + 8 + 25`, Q2 on `A, E_2, E_3, E_4`). -/
theorem b1_bank {K A : Finset ℕ} (free : QFree D V 8) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (bank : Bank D V K A) (hA : A.card = 8) {x : ℕ} (hx : x ∈ K) :
    38 ≤ (ball D V x 4).card := by
  have ch := bank_chain free (by norm_num) reg bank hx
  have c1 : (layer D V 1 x \ K).card = 8 := by rw [ext_one free (by norm_num) bank hx, hA]
  have q2 := (b1 free ch c1).2.2
  have b4 := bank_ball free bank hx (k := 4) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.reduceAdd] at b4
  omega

/-- **Q5, thin root.** `q = 8`, `r = 9`, `|L_2(u)| ≤ 8`: the heads of `u` are a bank with
`A = L_2(u)` (`RowBanks.thin_loop`), so `43 ≤ |B_5(u)|` (`RowBanks.transfer_exact` at `i = 4`). -/
theorem b1_thin (free : QFree D V 8) (reg : ∀ v ∈ V, (outN D V v).card = 9) {u : ℕ}
    (hu : u ∈ V) (thin : (layer D V 2 u).card ≤ 8) : 43 ≤ (ball D V u 5).card := by
  obtain ⟨w2, hX⟩ := RowBanks.thin_loop free (by norm_num) reg hu thin
  obtain ⟨x, hx⟩ : (outN D V u).Nonempty := card_pos.mp (by rw [reg u hu]; norm_num)
  have bank : Bank D V (outN D V u) (layer D V 2 u) :=
    { KV := outN_subset
      dis := Supplier54.heads_disj hu le_rfl
      one := fun k hk => (hX k hk).1
      keep := LoopCollar.head_keep free (by norm_num) hu
      full := fun k hk => (hX k hk).2.1 }
  have b := b1_bank free reg bank w2 hx
  have te : (ball D V x 4).card + 9 = (ball D V u 5).card + 4 :=
    RowBanks.transfer_exact free (by norm_num) reg hu thin hx (i := 4) (by norm_num)
  omega

/-! ### Q6: the thin root at `q = 7` -/

/-- **Q6, no return** (`q = 7`, `r = 9`, `|L_2(u)| = 8`). No row of layers `2 … 5` points into
`B_1(u) = {u} ∪ X`. -/
theorem thin_no_return (free : QFree D V 7) (reg : ∀ v ∈ V, (outN D V v).card = 9) {u : ℕ}
    (hu : u ∈ V) (thin : (layer D V 2 u).card = 8) {j : ℕ} (hj2 : 2 ≤ j) (hj5 : j ≤ 5) {v : ℕ}
    (hv : v ∈ layer D V j u) {w : ℕ} (hw : w ∈ ball D V u 1) : ¬ D v w = true := by
  rcases (mem_ball_one hu).mp hw with rfl | hx
  · exact Supplier54.no_back_u_g free hu (by omega) hv
  · exact Supplier54.no_back_x_g free (by norm_num) reg hu
      (by unfold ThinSuppliers.Thin; omega) (by norm_num) (by norm_num) hj2 (by omega) hv hx

/-- Heads of rows of layers `2 … 5` lie in layers `2 … j + 1`. -/
theorem thin_heads (free : QFree D V 7) (reg : ∀ v ∈ V, (outN D V v).card = 9) {u : ℕ}
    (hu : u ∈ V) (thin : (layer D V 2 u).card = 8) {j : ℕ} (hj2 : 2 ≤ j) (hj5 : j ≤ 5) {v : ℕ}
    (hv : v ∈ layer D V j u) {w : ℕ} (hw : w ∈ outN D V v) :
    ∃ i, 1 < i ∧ i ≤ j + 1 ∧ w ∈ layer D V i u := by
  obtain ⟨wV, vw⟩ := mem_outN.mp hw
  have wb := ball_step (mem_layer.mp hv).1 wV vw
  have w1 : w ∉ ball D V u 1 := fun h => thin_no_return free reg hu thin hj2 hj5 hv h vw
  exact layer_between wb w1

/-- **Q6, the chain.** Layers `2, 3, 4, 5` of a thin root at `q = 7`, `r = 9` form a chain. -/
theorem thin_chain (free : QFree D V 7) (reg : ∀ v ∈ V, (outN D V v).card = 9) {u : ℕ}
    (hu : u ∈ V) (thin : (layer D V 2 u).card = 8) :
    Chain D V 9 (layer D V 2 u) (layer D V 3 u) (layer D V 4 u) (layer D V 5 u) where
  AV := layer_subset
  BV := layer_subset
  CV := layer_subset
  dAB := FragmentBudget.layer_disj (by norm_num)
  dAC := FragmentBudget.layer_disj (by norm_num)
  dAE := FragmentBudget.layer_disj (by norm_num)
  dBC := FragmentBudget.layer_disj (by norm_num)
  dBE := FragmentBudget.layer_disj (by norm_num)
  dCE := FragmentBudget.layer_disj (by norm_num)
  degA := fun v hv => reg v (layer_subset hv)
  degB := fun v hv => reg v (layer_subset hv)
  degC := fun v hv => reg v (layer_subset hv)
  kA := fun v hv w hw => by
    obtain ⟨i, h1, h2, h3⟩ := thin_heads free reg hu thin (j := 2) le_rfl (by norm_num) hv hw
    interval_cases i <;> (simp only [mem_union]; tauto)
  kB := fun v hv w hw => by
    obtain ⟨i, h1, h2, h3⟩ := thin_heads free reg hu thin (j := 3) (by norm_num) (by norm_num) hv hw
    interval_cases i <;> (simp only [mem_union]; tauto)
  kC := fun v hv w hw => by
    obtain ⟨i, h1, h2, h3⟩ := thin_heads free reg hu thin (j := 4) (by norm_num) (by norm_num) hv hw
    interval_cases i <;> (simp only [mem_union]; tauto)

/-- **Q6 (A3).** `q = 7`, `r = 9`, a thin root (`|L_2(u)| = 8`):
`76 ≤ |B_4(u)| + |B_5(u)|` (`36 + 2(|L_3| + |L_4|) + |L_5|`, Q1 on the layers `2 … 5`). -/
theorem a3_thin (free : QFree D V 7) (reg : ∀ v ∈ V, (outN D V v).card = 9) {u : ℕ}
    (hu : u ∈ V) (thin : (layer D V 2 u).card = 8) :
    76 ≤ (ball D V u 4).card + (ball D V u 5).card := by
  have q1 := a1 free (thin_chain free reg hu thin) thin
  have l1 := ShapeClimbRoot.layer_one_card free (by norm_num) hu (reg u hu)
  have s4 := ShapeClimbRoot.card_ball_sum (D := D) hu 4
  have s5 := ShapeClimbRoot.card_ball_sum (D := D) hu 5
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.reduceAdd] at s4 s5
  omega

#print axioms keep_two
#print axioms sink_heads
#print axioms a1_tail
#print axioms a1
#print axioms b1
#print axioms exit_walk
#print axioms no_return
#print axioms layer_between
#print axioms ext_one
#print axioms ext_heads
#print axioms bank_chain
#print axioms bank_ball
#print axioms a2_bank
#print axioms b1_bank
#print axioms b1_thin
#print axioms thin_no_return
#print axioms thin_chain
#print axioms a3_thin

end LeanCH.BR.BankPrice
