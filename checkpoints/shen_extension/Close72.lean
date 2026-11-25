import checkpoints.shen_extension.BankPrice
import checkpoints.shen_extension.Close54Final

/-!
# Order 72 at degree nine, cutoff eight: the closing count

Setting: `free : QFree D V 8`, every out-degree `9`, `|V| = 72`. For a root `u`:
`X = outN D V u`, `Y = layer 2`, `Z = layer 3`, `W = layer 4`; `|B_3| = 10 + |Y| + |Z|`,
`|B_4| = |B_3| + |W|`. A *saver* is a row with `|B_4| ≤ 36`.

Generic part (free `q`, no degree):
* `walk_inside`: a walk all of whose intermediate labels and whose end lie in `P` is a walk in
  `P`.
* `ball_back`: an arc `a → b` gives `|B_k(b)| + 1 ≤ |B_{k+1}(a)|` (`k + 1 ≤ q`).
* `x_floor` (`4 ≤ q`): a head `x` of `u` has `|B_3(x)| ≤ reach_P 4 x + 1 + |W|`, where
  `P = B_3(u) \ {u}` (a path of length `≤ 3` from `X` stays in `P` except at its end).
* `z_extra` (`4 ≤ q`): in a `q`-free `P` of minimum out-degree two with `P ⊆ F ∪ Z`, rows of `F`
  with `n` heads (`n + 2 ≤ 2q`), `2 ≤ |Z| ≤ 2q`: two rows of `Z` with `reach 4 ≥ n + 4` and
  `≥ n + 3`.
* `extra_sum`, `floor_mul`: sums of floors.

Instance `q = 8`, `r = 9` (Part 1, pointwise):
* `xy_budget` (`fragment_budget` at radii `(4, 4)` on `X ∪ Y`, `|Z| ≤ 7`):
  `(9 + |Y|)(16 + 2(7 - |Z|)) + 72 ≤ (9 + |Y|)(8 + |Y|)`; `xy_arith` refutes it in E1 and E2.
* E1 `floor27`: `|B_3| ≥ 27` at every root (thin: a sink of `Y`, `|Z| ≥ 9`).
* E2 `e2`: `|Y| + |Z| = 17 ⇒ |Y| ≤ 9`, `|Y| + |Z| = 18 ⇒ |Y| ≤ 10`.
* E3/E4 `p_close`: `|B_3| + |W| ≤ 36 ⇒ |B_3| ≤ 28 ∧ |W| ≥ 8` (pair budget at radius `4` on
  `P = X ∪ Y ∪ Z`; floors `26 - |W|` on `X`, `full_row` on `Y`, `ordinary_rows` /
  `ordinary_floor` on `Z`, and `z_extra` at `|B_3| = 29`).
* E5 `thin_b4`: a thin root has `|B_4| ≥ 35`.
* E6 `saver`: a saver is of type `t ∈ {0, 1, 2}` (`Spec`): layer `t + 1` is a bank of `9` rows
  complete to layer `t + 2` of `8` labels, `|B_t| = 9t + 1`, `|B_4| ≥ 35`. Type `1` is P0,
  type `2` is PI, and PII excludes `(10, 8, 8)`; these three are the fields of `Profiles72`.

Part 2/3: `no72_of_profiles`: `Close54.payment` with `Close54.ledger_split` at `(4, 4)`; classes
are `(type, bank)`; a class of `m` roots has `m (m - 1)` gap incidences (`Close54.class_gap`) and
deficit at most `3m < m(m - 1) + 9`; the payers are the `9` bank rows at rate `1`, each with
`|B_4| ≥ 38` (`BankPrice.b1_bank`), surplus `3`, in at most one bank of each type
(`RowBanks.banks_meet`).
-/

set_option linter.style.longLine false
namespace LeanCH.BR.Close72
open Finset BRq2 BRq3
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)
open Profile54 (reach)
open ReachLedger (gap mem_gap)

variable {D : CH.Digraph} {V : Finset ℕ} {q : ℕ}

/-! ### Arithmetic -/

/-- E1/E2 arithmetic: `N (16 + 2t) + 72 ≤ N (N - 1)` with `N ≤ t + c`, `c ≤ 20`, is false. -/
theorem xy_arith {N t c : ℕ} (h : N * (16 + 2 * t) + 72 ≤ N * (N - 1)) (ht : N ≤ t + c)
    (hc : c ≤ 20) : False := by
  by_cases hN : N ≤ 17 + 2 * t
  · have := Nat.mul_le_mul_left N (show N - 1 ≤ 16 + 2 * t by omega)
    omega
  · have t2 : t ≤ 2 := by omega
    have N22 : N ≤ 22 := by omega
    have N18 : 18 ≤ N := by omega
    interval_cases t <;> interval_cases N <;> omega

/-- E3 arithmetic, `f_3 = 29 + s`, `0 ≤ s ≤ t ≤ 6`:
`2 (9 (20 + t) + |Y| (15 + t) + |Z| (11 + t)) > N (N - 1)`. -/
theorem ord_arith {N t y z : ℕ} (hN : N = 9 + y + z) (hy : 8 ≤ y) (h29 : 29 ≤ N)
    (hNt : N ≤ 29 + t) (ht : t ≤ 6)
    (h : 2 * (9 * (20 + t) + y * (15 + t) + z * (11 + t)) ≤ N * (N - 1)) : False := by
  have N35 : N ≤ 35 := by omega
  interval_cases t <;> interval_cases N <;> omega

/-- The bill of a class: `3 m < m (m - 1) + 9`. -/
theorem bill_arith (m : ℕ) : 3 * m < m * (m - 1) + 9 := by
  rcases Nat.lt_or_ge m 5 with h | h
  · interval_cases m <;> omega
  · have := Nat.mul_le_mul_left m (show 4 ≤ m - 1 by omega)
    omega

/-! ### Generic helpers -/

theorem floor_mul {S : Finset ℕ} {f : ℕ → ℕ} {a : ℕ} (h : ∀ v ∈ S, a ≤ f v) :
    S.card * a ≤ ∑ v ∈ S, f v := by
  rw [← smul_eq_mul]
  exact card_nsmul_le_sum _ _ _ h

/-- Two rows above the floor. -/
theorem extra_sum {Z : Finset ℕ} {f : ℕ → ℕ} {a b c z0 z1 : ℕ} (hz0 : z0 ∈ Z) (hz1 : z1 ∈ Z)
    (ne : z0 ≠ z1) (low : ∀ z ∈ Z, a ≤ f z) (h0 : a + b ≤ f z0) (h1 : a + c ≤ f z1) :
    Z.card * a + b + c ≤ ∑ z ∈ Z, f z := by
  have hz1' : z1 ∈ Z.erase z0 := mem_erase.mpr ⟨Ne.symm ne, hz1⟩
  have e1 := add_sum_erase Z f hz0
  have e2 := add_sum_erase (Z.erase z0) f hz1'
  have s3 : ((Z.erase z0).erase z1).card * a ≤ ∑ z ∈ (Z.erase z0).erase z1, f z :=
    floor_mul (fun z hz => low z (mem_of_mem_erase (mem_of_mem_erase hz)))
  rw [card_erase_of_mem hz1', card_erase_of_mem hz0] at s3
  have c2 : 2 ≤ Z.card := by
    have := card_le_card (show ({z0, z1} : Finset ℕ) ⊆ Z from
      insert_subset hz0 (singleton_subset_iff.mpr hz1))
    rwa [card_pair ne] at this
  have e3 : (Z.card - 1 - 1) * a + 2 * a = Z.card * a := by
    rw [← add_mul]
    congr 1
    omega
  omega

/-- **Restriction of a walk.** A walk whose intermediate labels (reached in fewer than `k` steps)
and whose end lie in `P` is a walk inside `P`. -/
theorem walk_inside {P : Finset ℕ} {a b k : ℕ} (w : Walk D V a b k) :
    (∀ i < k, ∀ v, Walk D V a v i → v ∈ P) → b ∈ P → Walk D P a b k := by
  induction w with
  | refl a => intro _ _; exact .refl a
  | @step a m c n mV am rest ih =>
    intro hP hc
    have mP : m ∈ P := by
      rcases Nat.eq_zero_or_pos n with rfl | npos
      · cases rest
        exact hc
      · exact hP 1 (by omega) m (.step mV am (.refl m))
    exact .step mP am (ih (fun i hi v wv => hP (i + 1) (by omega) v (.step mV am wv)) hc)

/-- **Back step** (generic, `k + 1 ≤ q`). An arc `a → b` gives `|B_k(b)| + 1 ≤ |B_{k+1}(a)|`. -/
theorem ball_back {W : Finset ℕ} (free : QFree D W q) {a b k : ℕ} (ha : a ∈ W) (hb : b ∈ W)
    (ab : D a b = true) (hk : k + 1 ≤ q) :
    (ball D W b k).card + 1 ≤ (ball D W a (k + 1)).card := by
  have notin : a ∉ ball D W b k := by
    intro h
    obtain ⟨-, j, hj, w⟩ := mem_ball.mp h
    exact free b (j + 1) (by omega) (by omega) (w.snoc hb ab)
  have sub : insert a (ball D W b k) ⊆ ball D W a (k + 1) := by
    intro z hz
    rcases mem_insert.mp hz with e | hz
    · rw [e]; exact self_mem_ball ha
    · obtain ⟨zW, j, hj, w⟩ := mem_ball.mp hz
      exact mem_ball.mpr ⟨zW, j + 1, by omega, Walk.step hb ab w⟩
  have := card_le_card sub
  rw [card_insert_of_notMem notin] at this
  exact this

/-- **The floor of a head inside `B_3(u) \ {u}`** (generic, `4 ≤ q`). For a head `x` of `u`:
`|B_3(x)| ≤ reach_P 4 x + 1 + |W|`, `P = B_3(u) \ {u}`, `W` the fourth layer. A walk of length
`≤ 3` from `x` stays in layers `1 … 3` before its end (never at `u`: a closed walk of length
`≤ 4`), and its end is in `P` or in `W`. -/
theorem x_floor (free : QFree D V q) (hq : 4 ≤ q) {u x : ℕ} (hu : u ∈ V)
    (hx : x ∈ outN D V u) :
    (ball D V x 3).card ≤ reach D ((ball D V u 3).erase u) 4 x + 1 + (layer D V 4 u).card := by
  classical
  obtain ⟨xV, ux⟩ := mem_outN.mp hx
  have inB : ∀ i v, Walk D V x v i → v ∈ ball D V u (i + 1) := by
    intro i v w
    have w' : Walk D V u v (i + 1) := .step xV ux w
    obtain ⟨_, _, vV, _⟩ := Walk.unsnoc w'
    exact mem_ball.mpr ⟨vV, i + 1, le_rfl, w'⟩
  have notU : ∀ i v, Walk D V x v i → i + 1 ≤ q → v ≠ u := by
    intro i v w hi e
    rw [e] at w
    exact free u (i + 1) (by omega) hi (.step xV ux w)
  have sub : ball D V x 3 ⊆ ball D ((ball D V u 3).erase u) x 3 ∪ layer D V 4 u := by
    intro y hy
    obtain ⟨-, j, hj, w⟩ := mem_ball.mp hy
    have yb : y ∈ ball D V u 4 := ball_mono_radius (by omega) (inB j y w)
    have yu : y ≠ u := notU j y w (by omega)
    by_cases y3 : y ∈ ball D V u 3
    · refine mem_union_left _ (mem_ball.mpr ⟨mem_erase.mpr ⟨yu, y3⟩, j, hj, ?_⟩)
      exact walk_inside w (fun i hi v wv => mem_erase.mpr ⟨notU i v wv (by omega),
        ball_mono_radius (by omega) (inB i v wv)⟩) (mem_erase.mpr ⟨yu, y3⟩)
    · exact mem_union_right _ (mem_layer.mpr ⟨yb, y3⟩)
  have c := (card_le_card sub).trans (card_union_le _ _)
  have m := card_le_card (ball_mono_radius (D := D) (W := (ball D V u 3).erase u) (u := x)
    (show 3 ≤ 4 by omega))
  have xu : x ≠ u := by
    rintro rfl
    exact loopfree free (by omega) hu ux
  have xP : x ∈ (ball D V u 3).erase u :=
    mem_erase.mpr ⟨xu, ball_mono_radius (by omega) ((mem_ball_one hu).mpr (Or.inr hx))⟩
  have e := Profile54.card_ball_erase (D := D) (W := (ball D V u 3).erase u) (k := 4) xP
  unfold reach
  omega

/-- **Two extra rows** (generic, `4 ≤ q`). `P` is `q`-free of minimum out-degree two,
`P ⊆ F ∪ Z`, every row of `F` has `n` heads in `P` (`n + 2 ≤ 2q`), `2 ≤ |Z| ≤ 2q`. Some row
`z₀ ∈ Z` points into `F` (else `Z` keeps minimum out-degree two on `≤ 2q` labels) and has
`reach 4 ≥ n + 4`; some other row `z₁ ∈ Z` points into `F ∪ {z₀}` (else `Z \ {z₀}` does) and has
`reach 4 ≥ n + 3`. -/
theorem z_extra {P F Z : Finset ℕ} (free : QFree D P q) (hq : 4 ≤ q)
    (deg : ∀ v ∈ P, 2 ≤ (outN D P v).card) (FP : F ⊆ P) (ZP : Z ⊆ P)
    (cover : ∀ v ∈ P, v ∈ F ∨ v ∈ Z) {n : ℕ} (full : ∀ f ∈ F, (outN D P f).card = n)
    (hn : n + 2 ≤ 2 * q) (hZ : 2 ≤ Z.card) (hZq : Z.card ≤ 2 * q) :
    ∃ z0 ∈ Z, ∃ z1 ∈ Z, z0 ≠ z1 ∧ n + 4 ≤ reach D P 4 z0 ∧ n + 3 ≤ reach D P 4 z1 := by
  classical
  have r1 : ∀ a ∈ P, ∀ f ∈ F, D a f = true → n + 4 ≤ reach D P 4 a := by
    intro a ha f hf af
    have bb : (ball D P f 3).card + 1 ≤ (ball D P a 4).card :=
      ball_back free ha (FP hf) af (k := 3) (by omega)
    have h3 := Profile54.head_third free (by omega) (FP hf) (by rw [full f hf]; exact hn) deg
    rw [full f hf] at h3
    have := Profile54.card_ball_erase (D := D) (W := P) (k := 4) ha
    unfold reach
    omega
  have r2 : ∀ a ∈ P, ∀ b ∈ P, ∀ f ∈ F, D a b = true → D b f = true →
      n + 3 ≤ reach D P 4 a := by
    intro a ha b hb f hf ab bf
    have bb1 : (ball D P b 3).card + 1 ≤ (ball D P a 4).card :=
      ball_back free ha hb ab (k := 3) (by omega)
    have bb2 : (ball D P f 2).card + 1 ≤ (ball D P b 3).card :=
      ball_back free hb (FP hf) bf (k := 2) (by omega)
    have h2 := Profile54.head_second free (by omega) (FP hf) (by rw [full f hf]; omega) deg
    rw [full f hf] at h2
    have := Profile54.card_ball_erase (D := D) (W := P) (k := 4) ha
    unfold reach
    omega
  have stuck : ∀ S ⊆ Z, S.Nonempty → S.card ≤ 2 * q →
      ∃ s ∈ S, ∃ w, D s w = true ∧ w ∈ P ∧ w ∉ S := by
    intro S SZ ne hS
    by_contra h
    have SP : S ⊆ P := SZ.trans ZP
    have := Profile54.two_order (free.mono_set SP) (by omega) ne (fun v hv => by
      rw [Profile54.out_restrict SP (fun w hw => by
        by_contra wS
        exact h ⟨v, hv, w, (mem_outN.mp hw).2, (mem_outN.mp hw).1, wS⟩)]
      exact deg v (SP hv))
    omega
  obtain ⟨z0, hz0, w0, zw0, w0P, w0Z⟩ := stuck Z subset_rfl (card_pos.mp (by omega)) hZq
  have w0F : w0 ∈ F := (cover w0 w0P).resolve_right w0Z
  have Zne : (Z.erase z0).Nonempty := card_pos.mp (by rw [card_erase_of_mem hz0]; omega)
  obtain ⟨z1, hz1, w1, zw1, w1P, w1Z⟩ := stuck (Z.erase z0) (erase_subset _ _) Zne
    (by rw [card_erase_of_mem hz0]; omega)
  obtain ⟨z1z0, z1Z⟩ := mem_erase.mp hz1
  refine ⟨z0, hz0, z1, z1Z, Ne.symm z1z0, r1 z0 (ZP hz0) w0 w0F zw0, ?_⟩
  rcases cover w1 w1P with w1F | w1Zin
  · have := r1 z1 (ZP z1Z) w1 w1F zw1
    omega
  · have e : w1 = z0 := by
      by_contra e
      exact w1Z (mem_erase.mpr ⟨e, w1Zin⟩)
    rw [e] at zw1
    exact r2 z1 (ZP z1Z) z0 (ZP hz0) w0 w0F zw1 zw0

/-! ### Part 1 at `q = 8`, `r = 9` -/

/-- **E5.** A thin root (`|Y| ≤ 8`) has `|B_4| ≥ 35`: its heads are a bank complete to `Y`
(`RowBanks.thin_loop`); for a head `x`, `|B_3(x)| ≥ 4 + 8 + 17` (`BankPrice.b1` on the exterior
chain) and `|B_3(x)| + 9 = |B_4(u)| + 3` (`RowBanks.transfer_exact`). -/
theorem thin_b4 (free : QFree D V 8) (reg : ∀ v ∈ V, (outN D V v).card = 9) {u : ℕ}
    (hu : u ∈ V) (thin : (layer D V 2 u).card ≤ 8) : 35 ≤ (ball D V u 4).card := by
  obtain ⟨w2, hX⟩ := RowBanks.thin_loop free (by norm_num) reg hu thin
  obtain ⟨x, hx⟩ : (outN D V u).Nonempty := card_pos.mp (by rw [reg u hu]; norm_num)
  have bank : BankPrice.Bank D V (outN D V u) (layer D V 2 u) :=
    { KV := outN_subset
      dis := Supplier54.heads_disj hu le_rfl
      one := fun k hk => (hX k hk).1
      keep := LoopCollar.head_keep free (by norm_num) hu
      full := fun k hk => (hX k hk).2.1 }
  have ch := BankPrice.bank_chain free (by norm_num) reg bank hx
  have c1 : (layer D V 1 x \ outN D V u).card = 8 := by
    rw [BankPrice.ext_one free (by norm_num) bank hx, w2]
  have q2 := (BankPrice.b1 free ch c1).2.1
  have b3 := BankPrice.bank_ball free bank hx (k := 3) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.reduceAdd] at b3
  have te : (ball D V x 3).card + 9 = (ball D V u 4).card + 3 :=
    RowBanks.transfer_exact free (by norm_num) reg hu thin hx (i := 3) (by norm_num)
  omega

/-- **The budget on `X ∪ Y`** (`|Z| ≤ 7`). `fragment_budget` at radii `(4, 4)` (`i + j = 8 = q`),
`r = 9`, slack `t = 7 - |Z|` (rows of `Y` keep `9 - |Z|` heads), nine full rows `X`:
`(9 + |Y|)(16 + 2t) + 72 ≤ (9 + |Y|)(8 + |Y|)` (`72 = 2 · 9 · (9 + 3 - 8)`). -/
theorem xy_budget (free : QFree D V 8) (reg : ∀ v ∈ V, (outN D V v).card = 9) {u : ℕ}
    (hu : u ∈ V) (hz : (layer D V 3 u).card ≤ 7) :
    (9 + (layer D V 2 u).card) * (16 + 2 * (7 - (layer D V 3 u).card)) + 72 ≤
      (9 + (layer D V 2 u).card) * (9 + (layer D V 2 u).card - 1) := by
  have w2 := ThinSuppliers.second_wide free (by norm_num) reg hu (by norm_num)
  have Fc : (Profile54.inner D V u).card = 9 + (layer D V 2 u).card := Profile54.inner_card hu reg
  have XF : outN D V u ⊆ Profile54.inner D V u := fun _ h => mem_union_left _ h
  have deg : ∀ v ∈ Profile54.inner D V u,
      2 + (7 - (layer D V 3 u).card) ≤ (outN D (Profile54.inner D V u) v).card := by
    intro v hv
    rcases mem_union.mp hv with hx | hy
    · rw [Profile54.x_keep free (by norm_num) hu hx, reg v (outN_subset hx)]
      omega
    · have := Profile54.y_keep free (by norm_num) reg hu hy
      omega
  have fb := FragmentBudget.fragment_budget (i := 4) (j := 4) (r := 9)
    (t := 7 - (layer D V 3 u).card) (Fs := outN D V u)
    (free.mono_set Profile54.inner_subset) deg XF
    (fun x hx => by rw [Profile54.x_keep free (by norm_num) hu hx, reg x (outN_subset hx)])
    (by norm_num) (by rw [Fc]; omega) (by norm_num) (by norm_num) (by norm_num)
  rw [Fc, reg u hu] at fb
  exact fb

/-- **E1.** Every root has `|B_3| ≥ 27`. Thin: rows of `Y` (`8 ≤ q` of them) keep their heads in
`Y ∪ Z`, so a sink of `Y` has its nine heads in `Z`. Not thin: `xy_budget`, `xy_arith` with
`c = 18`. -/
theorem floor27 (free : QFree D V 8) (reg : ∀ v ∈ V, (outN D V v).card = 9) {u : ℕ}
    (hu : u ∈ V) : 27 ≤ (ball D V u 3).card := by
  have L := (ThinSuppliers.balls_by_layers free (by norm_num) reg hu).2.2
  have w2 := ThinSuppliers.second_wide free (by norm_num) reg hu (by norm_num)
  by_cases thin : (layer D V 2 u).card ≤ 8
  · have th : ThinSuppliers.Thin D V 9 u := by unfold ThinSuppliers.Thin; omega
    have keep := ThinSuppliers.y_keep_r free (by norm_num) reg hu th (by norm_num)
    have := BankPrice.sink_heads free layer_subset (card_pos.mp (by omega)) thin
      (fun v hv => reg v (layer_subset hv)) keep
    omega
  · by_contra h
    exact xy_arith (xy_budget free reg hu (by omega)) (c := 18) (by omega) (by norm_num)

/-- **E2.** `|Y| + |Z| = 17 ⇒ |Y| ≤ 9` and `|Y| + |Z| = 18 ⇒ |Y| ≤ 10`. -/
theorem e2 (free : QFree D V 8) (reg : ∀ v ∈ V, (outN D V v).card = 9) {u : ℕ} (hu : u ∈ V) :
    ((layer D V 2 u).card + (layer D V 3 u).card = 17 → (layer D V 2 u).card ≤ 9) ∧
    ((layer D V 2 u).card + (layer D V 3 u).card = 18 → (layer D V 2 u).card ≤ 10) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hy
    exact xy_arith (xy_budget free reg hu (by omega)) (c := 19) (by omega) (by norm_num)
  · by_contra hy
    exact xy_arith (xy_budget free reg hu (by omega)) (c := 20) (by omega) (by norm_num)

/-- **E3 and E4.** `|B_3| + |W| ≤ 36` (`f_4 ≤ 35`) gives `|B_3| ≤ 28` and `|W| ≥ 8`.
Pair budget at radius four on `P = B_3(u) \ {u}` (`N = |B_3| - 1` labels; `2 Σ reach 4 ≤ N(N-1)`).
Floors: `X`: `26 - |W|` (`x_floor`, E1 at the head); `Y`: full rows (`full_row`); `Z`:
`ordinary_rows` / `ordinary_floor`.
* `|B_3| ≥ 30`: `|W| ≤ 6`, every row keeps `3 + t`, `t = 6 - |W|`: `ord_arith`.
* `|B_3| ∈ {27, 28}` with `|W| ≤ 7`: `2(9·19 + 14|Y| + 8|Z|) > N(N - 1)`.
* `|B_3| = 29`, `|W| ≤ 7`: `|Y| ≤ 9`, so `10 ≤ |Z| ≤ 11`, and `z_extra` adds `5 + 4`:
  `2(171 + 14|Y| + 8|Z| + 9) = 664 + 12|Y| > 756`. -/
theorem p_close (free : QFree D V 8) (reg : ∀ v ∈ V, (outN D V v).card = 9) {u : ℕ}
    (hu : u ∈ V) (h36 : (ball D V u 3).card + (layer D V 4 u).card ≤ 36) :
    (ball D V u 3).card ≤ 28 ∧ 8 ≤ (layer D V 4 u).card := by
  classical
  have L := (ThinSuppliers.balls_by_layers free (by norm_num) reg hu).2.2
  have w2 := ThinSuppliers.second_wide free (by norm_num) reg hu (by norm_num)
  have low := floor27 free reg hu
  have cX : (outN D V u).card = 9 := reg u hu
  have xu : ∀ x ∈ outN D V u, x ≠ u := fun x hx e => by
    have ux := (mem_outN.mp hx).2
    rw [e] at ux
    exact loopfree free (by norm_num) hu ux
  have XF2 : outN D V u ⊆ (ball D V u 2).erase u := fun x hx =>
    mem_erase.mpr ⟨xu x hx, ball_mono_radius (by norm_num) ((mem_ball_one hu).mpr (Or.inr hx))⟩
  have YF2 : layer D V 2 u ⊆ (ball D V u 2).erase u := fun y hy =>
    mem_erase.mpr ⟨fun e => (mem_layer.mp hy).2 (by rw [e]; exact self_mem_ball hu),
      (mem_layer.mp hy).1⟩
  have ZP : layer D V 3 u ⊆ (ball D V u 3).erase u := fun z hz =>
    mem_erase.mpr ⟨fun e => (mem_layer.mp hz).2 (by rw [e]; exact self_mem_ball hu),
      (mem_layer.mp hz).1⟩
  have F2P : (ball D V u 2).erase u ⊆ (ball D V u 3).erase u :=
    erase_subset_erase u (ball_mono_radius (by norm_num))
  have PV : (ball D V u 3).erase u ⊆ V := (erase_subset _ _).trans ball_subset
  have cP : ((ball D V u 3).erase u).card + 1 = (ball D V u 3).card :=
    card_erase_add_one (self_mem_ball hu)
  have keepPW : ∀ v ∈ (ball D V u 3).erase u,
      outN D V v ⊆ (ball D V u 3).erase u ∪ layer D V 4 u := by
    intro v hv w hw
    obtain ⟨wV, vw⟩ := mem_outN.mp hw
    have vb := mem_of_mem_erase hv
    have wu : w ≠ u := by
      intro e
      rw [e] at vw
      exact no_back_arc free hu vb (by norm_num) vw
    by_cases w3 : w ∈ ball D V u 3
    · exact mem_union_left _ (mem_erase.mpr ⟨wu, w3⟩)
    · exact mem_union_right _ (mem_layer.mpr ⟨ball_step vb wV vw, w3⟩)
  have keepF2 : ∀ v ∈ (ball D V u 2).erase u, outN D V v ⊆ (ball D V u 3).erase u := by
    intro v hv w hw
    obtain ⟨wV, vw⟩ := mem_outN.mp hw
    have vb := mem_of_mem_erase hv
    have wu : w ≠ u := by
      intro e
      rw [e] at vw
      exact no_back_arc free hu vb (by norm_num) vw
    exact mem_erase.mpr ⟨wu, ball_step vb wV vw⟩
  have xfl0 : ∀ x ∈ outN D V u, (ball D V x 3).card ≤
      reach D ((ball D V u 3).erase u) 4 x + 1 + (layer D V 4 u).card :=
    fun x hx => x_floor free (by norm_num) hu hx
  have dXY : Disjoint (outN D V u) (layer D V 2 u) := Supplier54.heads_disj hu le_rfl
  have dXZ : Disjoint (outN D V u) (layer D V 3 u) := Supplier54.heads_disj hu (by norm_num)
  have dYZ : Disjoint (layer D V 2 u) (layer D V 3 u) := FragmentBudget.layer_disj (by norm_num)
  have cover : ∀ v ∈ (ball D V u 3).erase u, v ∈ (ball D V u 2).erase u ∨ v ∈ layer D V 3 u := by
    intro v hv
    obtain ⟨vu, vb⟩ := mem_erase.mp hv
    by_cases v2 : v ∈ ball D V u 2
    · exact Or.inl (mem_erase.mpr ⟨vu, v2⟩)
    · exact Or.inr (mem_layer.mpr ⟨vb, v2⟩)
  set P := (ball D V u 3).erase u with hP
  set F2 := (ball D V u 2).erase u with hF2
  set X := outN D V u with hX
  set Y := layer D V 2 u with hY
  set Z := layer D V 3 u with hZ
  set Wl := layer D V 4 u with hWl
  have frP : QFree D P 8 := free.mono_set PV
  have keepP : ∀ v ∈ P, 9 ≤ (outN D P v).card + Wl.card := fun v hv => by
    have := FragmentBudget.keep_le (keepPW v hv)
    rw [reg v (PV hv)] at this
    exact this
  have fullP : ∀ v ∈ F2, (outN D P v).card = 9 := fun v hv => by
    rw [BankPrice.keep_out PV (keepF2 v hv), reg v (PV (F2P hv))]
  have xfl : ∀ x ∈ X, 26 ≤ reach D P 4 x + Wl.card := fun x hx => by
    have h1 := xfl0 x hx
    have h2 := floor27 free reg (outN_subset hx)
    omega
  have budget : 2 * ∑ v ∈ P, reach D P 4 v ≤ P.card * (P.card - 1) :=
    Profile54.pair_budget (k := 4) frP (by norm_num)
  have split : ∑ v ∈ X, reach D P 4 v + ∑ v ∈ Y, reach D P 4 v + ∑ v ∈ Z, reach D P 4 v ≤
      ∑ v ∈ P, reach D P 4 v := by
    rw [← sum_union dXY, ← sum_union (disjoint_union_left.mpr ⟨dXZ, dYZ⟩)]
    exact sum_le_sum_of_subset (union_subset (union_subset (XF2.trans F2P) (YF2.trans F2P)) ZP)
  have hPc : P.card = 9 + Y.card + Z.card := by omega
  by_cases big : 30 ≤ (ball D V u 3).card
  · exfalso
    obtain ⟨t, ht⟩ : ∃ t, t + Wl.card = 6 := ⟨6 - Wl.card, by omega⟩
    have deg3 : ∀ v ∈ P, 3 + t ≤ (outN D P v).card := fun v hv => by
      have := keepP v hv
      omega
    have deg2 : ∀ v ∈ P, 2 + (1 + t) ≤ (outN D P v).card := fun v hv => by
      have := deg3 v hv
      omega
    have sX : X.card * (20 + t) ≤ ∑ v ∈ X, reach D P 4 v :=
      floor_mul (fun x hx => by have := xfl x hx; omega)
    have sY : Y.card * (15 + t) ≤ ∑ v ∈ Y, reach D P 4 v := floor_mul (fun y hy => by
      have := FullRow.full_row (i := 4) (r := 9) (t := 1 + t) frP le_rfl (by norm_num)
        (by omega) deg2 (F2P (YF2 hy)) (fullP y (YF2 hy))
      omega)
    have sZ : Z.card * (11 + t) ≤ ∑ v ∈ Z, reach D P 4 v :=
      floor_mul (fun z hz => (FullRow.ordinary_rows frP (by norm_num) deg3 (ZP hz)).2)
    rw [cX] at sX
    exact ord_arith (N := P.card) (t := t) (y := Y.card) (z := Z.card) hPc (by omega) (by omega)
      (by omega) (by omega) (by omega)
  · by_contra hc
    have e7 : Wl.card ≤ 7 := by omega
    have deg2 : ∀ v ∈ P, 2 ≤ (outN D P v).card := fun v hv => by
      have := keepP v hv
      omega
    have deg20 : ∀ v ∈ P, 2 + 0 ≤ (outN D P v).card := deg2
    have sX : X.card * 19 ≤ ∑ v ∈ X, reach D P 4 v :=
      floor_mul (fun x hx => by have := xfl x hx; omega)
    have sY : Y.card * 14 ≤ ∑ v ∈ Y, reach D P 4 v := floor_mul (fun y hy => by
      have := FullRow.full_row (i := 4) (r := 9) (t := 0) frP le_rfl (by norm_num)
        (by omega) deg20 (F2P (YF2 hy)) (fullP y (YF2 hy))
      omega)
    have zfl : ∀ z ∈ Z, 8 ≤ reach D P 4 z := fun z hz => by
      have := FragmentBudget.ordinary_floor (i := 4) (t := 0) frP (by norm_num) (by norm_num)
        deg20 (ZP hz)
      omega
    have sZ : Z.card * 8 ≤ ∑ v ∈ Z, reach D P 4 v := floor_mul zfl
    rw [cX] at sX
    obtain ⟨N, hN⟩ : ∃ N, P.card = N := ⟨_, rfl⟩
    rw [hN] at budget
    have N26 : 26 ≤ N := by omega
    have N28 : N ≤ 28 := by omega
    by_cases h28 : N = 28
    · subst h28
      have y9 : Y.card ≤ 9 := by omega
      obtain ⟨z0, hz0, z1, hz1, ne, r0, r1⟩ := z_extra (n := 9) frP (by norm_num) deg2 F2P ZP
        cover fullP (by norm_num) (by omega) (by omega)
      have sZ' := extra_sum hz0 hz1 ne zfl (show 8 + 5 ≤ reach D P 4 z0 by omega)
        (show 8 + 4 ≤ reach D P 4 z1 by omega)
      omega
    · rcases (show N = 26 ∨ N = 27 by omega) with rfl | rfl <;> omega

/-! ### The three profiles, and the savers -/

/-- The three profile theorems at `q = 8`, `r = 9` used here (P0, PI, PII). -/
structure Profiles72 (D : CH.Digraph) (V : Finset ℕ) : Prop where
  /-- P0: layers `(9, 8)`: `Y` is a bank complete to `Z`. -/
  p0 : ∀ u ∈ V, (layer D V 2 u).card = 9 → (layer D V 3 u).card = 8 →
    BankPrice.Bank D V (layer D V 2 u) (layer D V 3 u)
  /-- PI: layers `(9, 9, 8)`: `Z` is a bank complete to `W`. -/
  p1 : ∀ u ∈ V, (layer D V 2 u).card = 9 → (layer D V 3 u).card = 9 →
    (layer D V 4 u).card = 8 → BankPrice.Bank D V (layer D V 3 u) (layer D V 4 u)
  /-- PII: layers `(10, 8, 8)` do not occur. -/
  p2 : ∀ u ∈ V, (layer D V 2 u).card = 10 → (layer D V 3 u).card = 8 →
    (layer D V 4 u).card = 8 → False

/-- A saver of type `t`: layer `t + 1` is a bank of `9` rows complete to layer `t + 2` of `8`
labels, `|B_t| = 9t + 1`, `|B_4| ≥ 35`. -/
def Spec (D : CH.Digraph) (V : Finset ℕ) (t v : ℕ) : Prop :=
  BankPrice.Bank D V (layer D V (t + 1) v) (layer D V (t + 2) v) ∧
    (layer D V (t + 1) v).card = 9 ∧ (layer D V (t + 2) v).card = 8 ∧
    (ball D V v t).card = 9 * t + 1 ∧ 35 ≤ (ball D V v 4).card

/-- **E6: the savers.** A row with `|B_4| ≤ 36` is of type `0` (thin, bank `X`), type `1`
(`(9, 8, ·)`, bank `Y`, P0) or type `2` (`(9, 9, 8)`, bank `Z`, PI); `(10, 8, 8)` is PII. -/
theorem saver (free : QFree D V 8) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (pr : Profiles72 D V) {u : ℕ} (hu : u ∈ V) (low : (ball D V u 4).card ≤ 36) :
    ∃ t, t ≤ 2 ∧ Spec D V t u := by
  obtain ⟨L1, L2, L3⟩ := ThinSuppliers.balls_by_layers free (by norm_num) reg hu
  have b4 : (ball D V u 4).card = (layer D V 4 u).card + (ball D V u 3).card :=
    ShapeClimbRoot.card_ball_succ 3
  have w2 := ThinSuppliers.second_wide free (by norm_num) reg hu (by norm_num)
  have f27 := floor27 free reg hu
  by_cases thin : (layer D V 2 u).card ≤ 8
  · obtain ⟨y8, hX⟩ := RowBanks.thin_loop free (by norm_num) reg hu thin
    have bank : BankPrice.Bank D V (outN D V u) (layer D V 2 u) :=
      { KV := outN_subset
        dis := Supplier54.heads_disj hu le_rfl
        one := fun k hk => (hX k hk).1
        keep := LoopCollar.head_keep free (by norm_num) hu
        full := fun k hk => (hX k hk).2.1 }
    refine ⟨0, by norm_num, ?_⟩
    show BankPrice.Bank D V (layer D V 1 u) (layer D V 2 u) ∧ (layer D V 1 u).card = 9 ∧
      (layer D V 2 u).card = 8 ∧ (ball D V u 0).card = 9 * 0 + 1 ∧ 35 ≤ (ball D V u 4).card
    rw [ShapeClimbRoot.layer_one free (by norm_num) hu, ShapeClimbRoot.ball_zero_eq hu]
    exact ⟨bank, reg u hu, y8, by simp, thin_b4 free reg hu thin⟩
  · have pc := p_close free reg hu (by omega)
    have E2 := e2 free reg hu
    rcases (show (ball D V u 3).card = 27 ∨ (ball D V u 3).card = 28 by omega) with h27 | h28
    · have y9 : (layer D V 2 u).card = 9 := by
        have := E2.1 (by omega)
        omega
      have z8 : (layer D V 3 u).card = 8 := by omega
      refine ⟨1, by norm_num, ?_⟩
      show BankPrice.Bank D V (layer D V 2 u) (layer D V 3 u) ∧ (layer D V 2 u).card = 9 ∧
        (layer D V 3 u).card = 8 ∧ (ball D V u 1).card = 9 * 1 + 1 ∧ 35 ≤ (ball D V u 4).card
      exact ⟨pr.p0 u hu y9 z8, y9, z8, by omega, by omega⟩
    · have w8 : (layer D V 4 u).card = 8 := by omega
      have y10 := E2.2 (by omega)
      by_cases y9 : (layer D V 2 u).card = 9
      · have z9 : (layer D V 3 u).card = 9 := by omega
        refine ⟨2, le_rfl, ?_⟩
        show BankPrice.Bank D V (layer D V 3 u) (layer D V 4 u) ∧ (layer D V 3 u).card = 9 ∧
          (layer D V 4 u).card = 8 ∧ (ball D V u 2).card = 9 * 2 + 1 ∧
          35 ≤ (ball D V u 4).card
        exact ⟨pr.p1 u hu y9 z9 w8, z9, w8, by omega, by omega⟩
      · exact (pr.p2 u hu (by omega) (by omega) w8).elim

open Classical in
/-- The type of a saver. -/
noncomputable def typ72 (D : CH.Digraph) (V : Finset ℕ) (v : ℕ) : ℕ :=
  if h : ∃ t, t ≤ 2 ∧ Spec D V t v then h.choose else 0

theorem typ72_spec {v : ℕ} (h : ∃ t, t ≤ 2 ∧ Spec D V t v) :
    typ72 D V v ≤ 2 ∧ Spec D V (typ72 D V v) v := by
  classical
  unfold typ72
  rw [dif_pos h]
  exact h.choose_spec

/-- The class key: the type and the bank. -/
noncomputable def key72 (D : CH.Digraph) (V : Finset ℕ) (v : ℕ) : ℕ × Finset ℕ :=
  (typ72 D V v, layer D V (typ72 D V v + 1) v)

/-! ### Part 3: the payment -/

/-- **Order 72 from the three profiles.** -/
theorem no72_of_profiles (free : QFree D V 8) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 72) (pr : Profiles72 D V) : False := by
  classical
  set R := V.filter (fun v => (ball D V v 4).card ≤ 36) with hR
  set P := V.filter (fun v => ¬ (ball D V v 4).card ≤ 36) with hP
  have RV : R ⊆ V := filter_subset _ _
  have sp : ∀ v ∈ R, typ72 D V v ≤ 2 ∧ Spec D V (typ72 D V v) v := fun v hv =>
    typ72_spec (saver free reg pr (RV hv) (mem_filter.mp hv).2)
  -- the ledger at radii `(4, 4)`
  have led := Close54.ledger_split (D := D) (V := V) (i := 4) (i' := 4) free (by norm_num)
  rw [n] at led
  have splitS := sum_filter_add_sum_filter_not V (fun v => (ball D V v 4).card ≤ 36)
    (fun v => (ball D V v 4).card + (ball D V v 4).card - (72 + 1))
  have splitD := sum_filter_add_sum_filter_not V (fun v => (ball D V v 4).card ≤ 36)
    (fun v => (72 + 1) - ((ball D V v 4).card + (ball D V v 4).card))
  rw [← hP, ← hR] at splitS splitD
  have zS : ∑ v ∈ R, ((ball D V v 4).card + (ball D V v 4).card - (72 + 1)) = 0 :=
    sum_eq_zero (fun v hv => by have := (mem_filter.mp hv).2; omega)
  have zD : ∑ v ∈ P, ((72 + 1) - ((ball D V v 4).card + (ball D V v 4).card)) = 0 :=
    sum_eq_zero (fun v hv => by have := (mem_filter.mp hv).2; omega)
  have capE : ∑ x ∈ P, (2 * (ball D V x 4).card - 73) =
      ∑ v ∈ P, ((ball D V v 4).card + (ball D V v 4).card - (72 + 1)) :=
    sum_congr rfl (fun v _ => by omega)
  have dfcE : ∑ v ∈ R, (73 - 2 * (ball D V v 4).card) =
      ∑ v ∈ R, ((72 + 1) - ((ball D V v 4).card + (ball D V v 4).card)) :=
    sum_congr rfl (fun v _ => by omega)
  have tot : ∑ x ∈ P, (2 * (ball D V x 4).card - 73) + ∑ v ∈ V, (gap D V 4 4 v).card =
      ∑ v ∈ R, (73 - 2 * (ball D V v 4).card) := by omega
  -- a saver exists
  have Rne : R.Nonempty := by
    by_contra e
    rw [not_nonempty_iff_eq_empty] at e
    obtain ⟨v, hv⟩ : V.Nonempty := card_pos.mp (by omega)
    have vP : v ∈ P := by
      by_contra nP
      have : v ∈ R := mem_filter.mpr ⟨hv, by
        by_contra h
        exact nP (mem_filter.mpr ⟨hv, h⟩)⟩
      rw [e] at this
      simp at this
    have one := single_le_sum (f := fun x => 2 * (ball D V x 4).card - 73)
      (fun _ _ => Nat.zero_le _) vP
    have := (mem_filter.mp vP).2
    rw [e, sum_empty] at tot
    omega
  refine Close54.payment (R := R) (P := P) (key72 D V) (fun v => 73 - 2 * (ball D V v 4).card)
    (fun x => 2 * (ball D V x 4).card - 73)
    (fun K => ∑ w ∈ R.filter (fun v => key72 D V v = K),
      ((R.filter (fun v => key72 D V v = K)).filter (fun x => x ∈ gap D V 4 4 w)).card)
    (fun _ => 1) (fun K => K.2) (∑ v ∈ V, (gap D V 4 4 v).card) ?_ ?_ ?_ ?_ Rne tot.le
  · -- pair credit
    calc ∑ K ∈ R.image (key72 D V), ∑ w ∈ R.filter (fun v => key72 D V v = K),
          ((R.filter (fun v => key72 D V v = K)).filter (fun x => x ∈ gap D V 4 4 w)).card
        ≤ ∑ K ∈ R.image (key72 D V), ∑ w ∈ R.filter (fun v => key72 D V v = K),
            (gap D V 4 4 w).card :=
          sum_le_sum (fun K _ => sum_le_sum (fun w _ => card_le_card
            (fun x hx => (mem_filter.mp hx).2)))
      _ = ∑ w ∈ R, (gap D V 4 4 w).card :=
          sum_fiberwise_of_maps_to (fun v hv => mem_image_of_mem _ hv) _
      _ ≤ ∑ v ∈ V, (gap D V 4 4 v).card := sum_le_sum_of_subset RV
  · -- each class
    intro K hK
    obtain ⟨u, uR, rfl⟩ := mem_image.mp hK
    obtain ⟨tu, su⟩ := sp u uR
    set C := R.filter (fun v => key72 D V v = key72 D V u) with hC
    have mem : ∀ v ∈ C, v ∈ R ∧ typ72 D V v = typ72 D V u ∧
        layer D V (typ72 D V u + 1) v = layer D V (typ72 D V u + 1) u := by
      intro v hv
      obtain ⟨vR, kv⟩ := mem_filter.mp hv
      unfold key72 at kv
      obtain ⟨e1, e2⟩ := Prod.mk.inj kv
      rw [e1] at e2
      exact ⟨vR, e1, e2⟩
    have cg := Close54.class_gap (j := typ72 D V u + 1) (i := 4) (i' := 4)
      (s := 9 * typ72 D V u + 1) (Λ := layer D V (typ72 D V u + 1) u) (K₁ := C) (K₂ := ∅)
      free (by omega) (by omega) (by norm_num) (by norm_num)
      (fun v hv => RV (mem v hv).1) (empty_subset _) (disjoint_empty_right _)
      (fun v hv => (mem v hv).2.2) (fun v hv => absurd hv (notMem_empty v))
      (fun v hv => by
        rw [Nat.add_sub_cancel, ← (mem v hv).2.1]
        exact (sp v (mem v hv).1).2.2.2.2.1)
      (fun v hv => absurd hv (notMem_empty v))
    rw [union_empty, card_empty, mul_zero, add_zero] at cg
    have dle : ∑ v ∈ C, (73 - 2 * (ball D V v 4).card) ≤ C.card * 3 := by
      calc ∑ v ∈ C, (73 - 2 * (ball D V v 4).card) ≤ ∑ _v ∈ C, 3 :=
            sum_le_sum (fun v hv => by have := (sp v (mem v hv).1).2.2.2.2.2; omega)
        _ = C.card * 3 := by rw [sum_const, smul_eq_mul]
    have c9 : (key72 D V u).2.card = 9 := su.2.1
    have bill := bill_arith C.card
    show ∑ v ∈ C, (73 - 2 * (ball D V v 4).card) <
      ∑ w ∈ C, (C.filter (fun x => x ∈ gap D V 4 4 w)).card + 1 * (key72 D V u).2.card
    rw [c9]
    omega
  · -- the payers are bank rows, above the level
    intro K hK x hx
    obtain ⟨u, uR, rfl⟩ := mem_image.mp hK
    obtain ⟨-, su⟩ := sp u uR
    have hx' : x ∈ layer D V (typ72 D V u + 1) u := hx
    have b38 := BankPrice.b1_bank free reg su.1 su.2.2.1 hx'
    exact mem_filter.mpr ⟨su.1.KV hx', by omega⟩
  · -- capacities: one bank of each type
    intro x hx
    obtain ⟨xV, -⟩ := mem_filter.mp hx
    show ∑ K ∈ (R.image (key72 D V)).filter (fun K => x ∈ K.2), 1 ≤
      2 * (ball D V x 4).card - 73
    rw [sum_const, smul_eq_mul, mul_one]
    have mem : ∀ K ∈ (R.image (key72 D V)).filter (fun K => x ∈ K.2),
        ∃ u ∈ R, K = key72 D V u := fun K hK => by
      obtain ⟨u, uR, rfl⟩ := mem_image.mp (mem_filter.mp hK).1
      exact ⟨u, uR, rfl⟩
    rcases ((R.image (key72 D V)).filter (fun K => x ∈ K.2)).eq_empty_or_nonempty with e | ne
    · rw [e, card_empty]
      exact Nat.zero_le _
    obtain ⟨K0, hK0⟩ := ne
    obtain ⟨u0, u0R, rfl⟩ := mem K0 hK0
    have xin : x ∈ layer D V (typ72 D V u0 + 1) u0 := (mem_filter.mp hK0).2
    have b38 := BankPrice.b1_bank free reg (sp u0 u0R).2.1 (sp u0 u0R).2.2.2.1 xin
    have inj : Set.InjOn Prod.fst
        (↑((R.image (key72 D V)).filter (fun K => x ∈ K.2)) : Set (ℕ × Finset ℕ)) := by
      intro K hK K' hK' e
      rw [mem_coe] at hK hK'
      obtain ⟨u, uR, rfl⟩ := mem K hK
      obtain ⟨u', uR', rfl⟩ := mem K' hK'
      have xu : x ∈ layer D V (typ72 D V u + 1) u := (mem_filter.mp hK).2
      have xu' : x ∈ layer D V (typ72 D V u' + 1) u' := (mem_filter.mp hK').2
      have et : typ72 D V u = typ72 D V u' := e
      obtain ⟨-, su⟩ := sp u uR
      obtain ⟨-, su'⟩ := sp u' uR'
      have eq := RowBanks.banks_meet (q := 8) free (by norm_num) su.1.KV su'.1.KV su.2.1 su'.2.1
        su.1.one su'.1.one su.1.keep su'.1.keep su.1.full su'.1.full xu xu'
      exact Prod.ext et eq
    have sub : ((R.image (key72 D V)).filter (fun K => x ∈ K.2)).image Prod.fst ⊆ range 3 := by
      intro i hi
      obtain ⟨K, hK, rfl⟩ := mem_image.mp hi
      obtain ⟨u, uR, rfl⟩ := mem K hK
      have := (sp u uR).1
      exact mem_range.mpr (show typ72 D V u < 3 by omega)
    have c3 := card_le_card sub
    rw [card_image_of_injOn inj, card_range] at c3
    omega

#print axioms xy_arith
#print axioms ord_arith
#print axioms bill_arith
#print axioms extra_sum
#print axioms walk_inside
#print axioms ball_back
#print axioms x_floor
#print axioms z_extra
#print axioms thin_b4
#print axioms xy_budget
#print axioms floor27
#print axioms e2
#print axioms p_close
#print axioms saver
#print axioms no72_of_profiles

end LeanCH.BR.Close72
