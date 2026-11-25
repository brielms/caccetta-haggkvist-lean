import checkpoints.shen_extension.Close63Laws

/-!
# Order 63 at degree nine, cutoff seven

No `7`-free digraph with every out-degree at least `9` has `63` labels.

Score `S(x) = |B_3(x)| + |B_4(x)|`, level `64`; units of `1/60`: capacity `60 (S - 64)⁺`,
deficit `60 (64 - S)⁺`. Savers (`R63`, `S ≤ 63`) by type (`saver_cases`, from
`Floors7Row.low_score`), classes by `key63`:

* tag `0`, T: `|B_3| = 26` (thin, `(8, 8, w)`), key the second layer, payers its eight bank rows
  (`t_bank`) at `45` if `w = 8`, else `30`; slack `1` if `w ≥ 10`.
* tag `1`, H: thin, `|B_3| = 27`, key the second layer, payers the complete heads of the
  representative (`≥ 7`) at `20`; slack `1`.
* tag `2`, L: not thin, `(9, 8, 8)`, key the third layer, payers its eight bank rows
  (`Close62.fat_bank`) at `15`.
* tag `3`, M: not thin, `(9, 8, 9)`, key the third layer, payers the good rows of `aSet` of the
  representative (`≥ 6`, `fat_good`) at `12`; slack `1`.

Row slack `1` at a row of a bank (`8` rows, exterior `8`) that is not a T-payer with `w = 8`.
`bill63`: every class is paid with its slack (class bill `d m - m (m - 1) ≤ 6, 4, 2, 1`).
`cap63`: every row is charged at most its capacity minus its row slack (H-suppliers via
`TopRowFat.supplier_score` and `h_floor`; T, L via `a2_bank` and `banks_meet`; M via `fat_score`
and `zRows_exclusive`; law G via `bank_zRows`). `payment_exact` then kills every slack: there is no
M-class, and every bank row is a T-payer with `w = 8`; by `t8_bank` the exterior of every bank is
again a bank, which `no_bank_of_succ` forbids at `63 < 64`. So no L-saver and no M-saver:
`fat63`. Then `TopRow.no63_of_fat` with `end63`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.Close63
open Finset BRq2 BRq3 FifthStripAll RigidHost LoopCollar CHRuleCatalog
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)
open ReachLedger (gap mem_gap)
open ThinSuppliers (Thin complete complete_subset)

variable {D : CH.Digraph} {V : Finset ℕ}

/-! ### Data of the count -/

/-- The savers. -/
noncomputable def R63 (D : CH.Digraph) (V : Finset ℕ) : Finset ℕ :=
  V.filter (fun v => (ball D V v 3).card + (ball D V v 4).card ≤ 63)

theorem R63_def : R63 D V = V.filter (fun v => (ball D V v 3).card + (ball D V v 4).card ≤ 63) :=
  rfl

theorem R_V {v : ℕ} (h : v ∈ R63 D V) : v ∈ V := (mem_filter.mp h).1

open Classical in
/-- The class key: tag and literal set. -/
noncomputable def key63 (D : CH.Digraph) (V : Finset ℕ) (v : ℕ) : ℕ × Finset ℕ :=
  if (ball D V v 3).card = 26 then (0, layer D V 2 v)
  else if Thin D V 9 v then (1, layer D V 2 v)
  else if (layer D V 4 v).card = 8 then (2, layer D V 3 v)
  else (3, layer D V 3 v)

/-- The representative of a class. -/
noncomputable def rep63 (D : CH.Digraph) (V : Finset ℕ) (K : ℕ × Finset ℕ) : ℕ :=
  Close54.pick (R63 D V) (key63 D V) K

/-- Rates (units of `1/60`). -/
noncomputable def rate63 (D : CH.Digraph) (V : Finset ℕ) (K : ℕ × Finset ℕ) : ℕ :=
  if K.1 = 0 then (if (layer D V 4 (rep63 D V K)).card = 8 then 45 else 30)
  else if K.1 = 1 then 20 else if K.1 = 2 then 15 else 12

/-- Payers. -/
noncomputable def pay63 (D : CH.Digraph) (V : Finset ℕ) (K : ℕ × Finset ℕ) : Finset ℕ :=
  if K.1 = 1 then complete D V (rep63 D V K)
  else if K.1 = 3 then OneHead.good D (SupplierFat54.aSet D V (rep63 D V K))
  else K.2

/-- Class slack. -/
noncomputable def slack63 (D : CH.Digraph) (V : Finset ℕ) (K : ℕ × Finset ℕ) : ℕ :=
  if K.1 = 0 then (if 10 ≤ (layer D V 4 (rep63 D V K)).card then 1 else 0)
  else if K.1 = 2 then 0 else 1

/-- A row of a bank of `8` rows with an exterior of `8` labels. -/
def InBank (D : CH.Digraph) (V : Finset ℕ) (x : ℕ) : Prop :=
  ∃ K A, BankPrice.Bank D V K A ∧ K.card = 8 ∧ A.card = 8 ∧ x ∈ K

/-- A row of the second layer of a T-saver with `|W| = 8`. -/
def T8 (D : CH.Digraph) (V : Finset ℕ) (x : ℕ) : Prop :=
  ∃ u ∈ R63 D V, (ball D V u 3).card = 26 ∧ (layer D V 4 u).card = 8 ∧ x ∈ layer D V 2 u

open Classical in
/-- Row slack. -/
noncomputable def rslack63 (D : CH.Digraph) (V : Finset ℕ) (x : ℕ) : ℕ :=
  if InBank D V x ∧ ¬ T8 D V x then 1 else 0

theorem rate_0 {K : ℕ × Finset ℕ} (h : K.1 = 0) :
    rate63 D V K = if (layer D V 4 (rep63 D V K)).card = 8 then 45 else 30 := by
  simp [rate63, h]
theorem rate_1 {K : ℕ × Finset ℕ} (h : K.1 = 1) : rate63 D V K = 20 := by simp [rate63, h]
theorem rate_2 {K : ℕ × Finset ℕ} (h : K.1 = 2) : rate63 D V K = 15 := by simp [rate63, h]
theorem rate_3 {K : ℕ × Finset ℕ} (h : K.1 = 3) : rate63 D V K = 12 := by simp [rate63, h]
theorem pay_0 {K : ℕ × Finset ℕ} (h : K.1 = 0) : pay63 D V K = K.2 := by simp [pay63, h]
theorem pay_1 {K : ℕ × Finset ℕ} (h : K.1 = 1) : pay63 D V K = complete D V (rep63 D V K) := by
  simp [pay63, h]
theorem pay_2 {K : ℕ × Finset ℕ} (h : K.1 = 2) : pay63 D V K = K.2 := by simp [pay63, h]
theorem pay_3 {K : ℕ × Finset ℕ} (h : K.1 = 3) :
    pay63 D V K = OneHead.good D (SupplierFat54.aSet D V (rep63 D V K)) := by simp [pay63, h]
theorem slack_0 {K : ℕ × Finset ℕ} (h : K.1 = 0) :
    slack63 D V K = if 10 ≤ (layer D V 4 (rep63 D V K)).card then 1 else 0 := by
  simp [slack63, h]
theorem slack_1 {K : ℕ × Finset ℕ} (h : K.1 = 1) : slack63 D V K = 1 := by simp [slack63, h]
theorem slack_2 {K : ℕ × Finset ℕ} (h : K.1 = 2) : slack63 D V K = 0 := by simp [slack63, h]
theorem slack_3 {K : ℕ × Finset ℕ} (h : K.1 = 3) : slack63 D V K = 1 := by simp [slack63, h]

theorem key_cases (u : ℕ) :
    ((ball D V u 3).card = 26 ∧ key63 D V u = (0, layer D V 2 u)) ∨
    ((ball D V u 3).card ≠ 26 ∧ Thin D V 9 u ∧ key63 D V u = (1, layer D V 2 u)) ∨
    ((ball D V u 3).card ≠ 26 ∧ ¬ Thin D V 9 u ∧ (layer D V 4 u).card = 8 ∧
      key63 D V u = (2, layer D V 3 u)) ∨
    ((ball D V u 3).card ≠ 26 ∧ ¬ Thin D V 9 u ∧ (layer D V 4 u).card ≠ 8 ∧
      key63 D V u = (3, layer D V 3 u)) := by
  unfold key63
  split_ifs with h1 h2 h3
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr (Or.inl ⟨h1, h2, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, rfl⟩))

theorem key_lt (u : ℕ) : (key63 D V u).1 < 4 := by
  rcases key_cases (D := D) (V := V) u with ⟨-, e⟩ | ⟨-, -, e⟩ | ⟨-, -, -, e⟩ | ⟨-, -, -, e⟩ <;>
    simp [e]

theorem rep_spec {K : ℕ × Finset ℕ} (hK : K ∈ (R63 D V).image (key63 D V)) :
    rep63 D V K ∈ R63 D V ∧ key63 D V (rep63 D V K) = K :=
  Close54.pick_spec hK

theorem tag_lt {K : ℕ × Finset ℕ} (hK : K ∈ (R63 D V).image (key63 D V)) : K.1 < 4 := by
  obtain ⟨-, rk⟩ := rep_spec hK
  rw [← rk]
  exact key_lt _

/-- `d m ≤ B + m (m - 1)` from the values `m ≤ d + 1`. -/
theorem tri {d B : ℕ} (h : ∀ m ≤ d + 1, d * m ≤ B + m * (m - 1)) :
    ∀ m, d * m ≤ B + m * (m - 1) := by
  intro m
  by_cases hm : m ≤ d + 1
  · exact h m hm
  · have h2 : m * (d + 1) ≤ m * (m - 1) := Nat.mul_le_mul_left m (by omega)
    have h3 : d * m ≤ m * (d + 1) := by
      rw [mul_comm d m]; exact Nat.mul_le_mul_left m (by omega)
    omega

section count
variable (free : QFree D V 7) (reg : ∀ v ∈ V, (outN D V v).card = 9)

include free reg in
/-- **A, the saver types** (from `Floors7Row.low_score`). -/
theorem saver_cases {u : ℕ} (hu : u ∈ V)
    (low : (ball D V u 3).card + (ball D V u 4).card ≤ 63) :
    ((ball D V u 3).card = 26 ∧ Thin D V 9 u ∧ (layer D V 2 u).card = 8 ∧
      (layer D V 3 u).card = 8 ∧ 8 ≤ (layer D V 4 u).card ∧
      (ball D V u 4).card = (layer D V 4 u).card + 26) ∨
    ((ball D V u 3).card = 27 ∧ Thin D V 9 u ∧ (layer D V 2 u).card = 8 ∧
      (layer D V 3 u).card = 9 ∧ 8 ≤ (layer D V 4 u).card ∧ (layer D V 4 u).card ≤ 9 ∧
      (ball D V u 4).card = (layer D V 4 u).card + 27) ∨
    ((ball D V u 3).card = 27 ∧ ¬ Thin D V 9 u ∧ (layer D V 2 u).card = 9 ∧
      (layer D V 3 u).card = 8 ∧ 8 ≤ (layer D V 4 u).card ∧ (layer D V 4 u).card ≤ 9 ∧
      (ball D V u 4).card = (layer D V 4 u).card + 27) := by
  have L := Floors7Row.balls9 free reg hu
  rcases Floors7Row.low_score free reg hu low with ⟨h26, th, z8, w8⟩ |
    ⟨h27, b35, b36, ⟨th, z9⟩ | ⟨nt, y9, z8⟩⟩
  · have y8 : (layer D V 2 u).card = 8 := by unfold Thin at th; omega
    exact Or.inl ⟨h26, th, y8, z8, w8, by omega⟩
  · have y8 : (layer D V 2 u).card = 8 := by unfold Thin at th; omega
    exact Or.inr (Or.inl ⟨h27, th, y8, z9, by omega, by omega, by omega⟩)
  · exact Or.inr (Or.inr ⟨h27, nt, y9, z8, by omega, by omega, by omega⟩)

include free reg in
theorem key_data {u : ℕ} (hu : u ∈ R63 D V) :
    (key63 D V u = (0, layer D V 2 u) ∧ (ball D V u 3).card = 26 ∧ Thin D V 9 u ∧
      (layer D V 2 u).card = 8 ∧ (layer D V 3 u).card = 8 ∧ 8 ≤ (layer D V 4 u).card ∧
      (layer D V 4 u).card ≤ 11 ∧ (ball D V u 4).card = (layer D V 4 u).card + 26) ∨
    (key63 D V u = (1, layer D V 2 u) ∧ (ball D V u 3).card = 27 ∧ Thin D V 9 u ∧
      (layer D V 2 u).card = 8 ∧ (layer D V 3 u).card = 9 ∧ 8 ≤ (layer D V 4 u).card ∧
      (layer D V 4 u).card ≤ 9 ∧ (ball D V u 4).card = (layer D V 4 u).card + 27) ∨
    (key63 D V u = (2, layer D V 3 u) ∧ (ball D V u 3).card = 27 ∧ ¬ Thin D V 9 u ∧
      (layer D V 2 u).card = 9 ∧ (layer D V 3 u).card = 8 ∧ (layer D V 4 u).card = 8 ∧
      (ball D V u 4).card = 35) ∨
    (key63 D V u = (3, layer D V 3 u) ∧ (ball D V u 3).card = 27 ∧ ¬ Thin D V 9 u ∧
      (layer D V 2 u).card = 9 ∧ (layer D V 3 u).card = 8 ∧ (layer D V 4 u).card = 9 ∧
      (ball D V u 4).card = 36) := by
  obtain ⟨uV, low⟩ := mem_filter.mp hu
  rcases key_cases (D := D) (V := V) u with ⟨h26, e⟩ | ⟨h26, th, e⟩ | ⟨h26, th, w8, e⟩ |
    ⟨h26, th, w8, e⟩ <;>
  rcases saver_cases free reg uV low with ⟨a1, a2, a3, a4, a5, a6⟩ |
    ⟨b1, b2, b3, b4, b5, b6, b7⟩ | ⟨c1, c2, c3, c4, c5, c6, c7⟩
  · exact Or.inl ⟨e, a1, a2, a3, a4, a5, by omega, a6⟩
  · omega
  · omega
  · omega
  · exact Or.inr (Or.inl ⟨e, b1, b2, b3, b4, b5, b6, b7⟩)
  · exact absurd th c2
  · omega
  · exact absurd b2 th
  · exact Or.inr (Or.inr (Or.inl ⟨e, c1, c2, c3, c4, w8, by omega⟩))
  · omega
  · exact absurd b2 th
  · exact Or.inr (Or.inr (Or.inr ⟨e, c1, c2, c3, c4, by omega, by omega⟩))

include free reg in
theorem key_T {u : ℕ} (hu : u ∈ R63 D V) (k : (key63 D V u).1 = 0) :
    key63 D V u = (0, layer D V 2 u) ∧ (ball D V u 3).card = 26 ∧ Thin D V 9 u ∧
      (layer D V 2 u).card = 8 ∧ (layer D V 3 u).card = 8 ∧ 8 ≤ (layer D V 4 u).card ∧
      (layer D V 4 u).card ≤ 11 ∧ (ball D V u 4).card = (layer D V 4 u).card + 26 := by
  rcases key_data free reg hu with h | h | h | h
  · exact h
  all_goals (rw [h.1] at k; simp at k)

include free reg in
theorem key_H {u : ℕ} (hu : u ∈ R63 D V) (k : (key63 D V u).1 = 1) :
    key63 D V u = (1, layer D V 2 u) ∧ (ball D V u 3).card = 27 ∧ Thin D V 9 u ∧
      (layer D V 2 u).card = 8 ∧ (layer D V 3 u).card = 9 ∧ 8 ≤ (layer D V 4 u).card ∧
      (layer D V 4 u).card ≤ 9 ∧ (ball D V u 4).card = (layer D V 4 u).card + 27 := by
  rcases key_data free reg hu with h | h | h | h
  · rw [h.1] at k; simp at k
  · exact h
  all_goals (rw [h.1] at k; simp at k)

include free reg in
theorem key_L {u : ℕ} (hu : u ∈ R63 D V) (k : (key63 D V u).1 = 2) :
    key63 D V u = (2, layer D V 3 u) ∧ (ball D V u 3).card = 27 ∧ ¬ Thin D V 9 u ∧
      (layer D V 2 u).card = 9 ∧ (layer D V 3 u).card = 8 ∧ (layer D V 4 u).card = 8 ∧
      (ball D V u 4).card = 35 := by
  rcases key_data free reg hu with h | h | h | h
  · rw [h.1] at k; simp at k
  · rw [h.1] at k; simp at k
  · exact h
  · rw [h.1] at k; simp at k

include free reg in
theorem key_M {u : ℕ} (hu : u ∈ R63 D V) (k : (key63 D V u).1 = 3) :
    key63 D V u = (3, layer D V 3 u) ∧ (ball D V u 3).card = 27 ∧ ¬ Thin D V 9 u ∧
      (layer D V 2 u).card = 9 ∧ (layer D V 3 u).card = 8 ∧ (layer D V 4 u).card = 9 ∧
      (ball D V u 4).card = 36 := by
  rcases key_data free reg hu with h | h | h | h
  · rw [h.1] at k; simp at k
  · rw [h.1] at k; simp at k
  · rw [h.1] at k; simp at k
  · exact h

/-! ### The classes through their representatives -/

include free reg in
theorem class0 {K : ℕ × Finset ℕ} (hK : K ∈ (R63 D V).image (key63 D V)) (h : K.1 = 0) :
    K = (0, layer D V 2 (rep63 D V K)) ∧ K.2 = layer D V 2 (rep63 D V K) ∧
      rep63 D V K ∈ R63 D V ∧ (ball D V (rep63 D V K) 3).card = 26 ∧
      (layer D V 2 (rep63 D V K)).card = 8 ∧ (layer D V 3 (rep63 D V K)).card = 8 ∧
      8 ≤ (layer D V 4 (rep63 D V K)).card ∧ (layer D V 4 (rep63 D V K)).card ≤ 11 ∧
      BankPrice.Bank D V (layer D V 2 (rep63 D V K)) (layer D V 3 (rep63 D V K)) := by
  obtain ⟨rR, rk⟩ := rep_spec hK
  obtain ⟨e, r26, -, ry, rz, r8, r11, -⟩ := key_T free reg rR (by rw [rk]; exact h)
  have eK : K = (0, layer D V 2 (rep63 D V K)) := rk.symm.trans e
  exact ⟨eK, congrArg Prod.snd eK, rR, r26, ry, rz, r8, r11, t_bank free reg (R_V rR) r26⟩

include free reg in
theorem class1 {K : ℕ × Finset ℕ} (hK : K ∈ (R63 D V).image (key63 D V)) (h : K.1 = 1) :
    K = (1, layer D V 2 (rep63 D V K)) ∧ rep63 D V K ∈ R63 D V ∧ Thin D V 9 (rep63 D V K) ∧
      (ball D V (rep63 D V K) 3).card = 27 ∧ (layer D V 4 (rep63 D V K)).card ≤ 9 ∧
      7 ≤ (complete D V (rep63 D V K)).card := by
  obtain ⟨rR, rk⟩ := rep_spec hK
  obtain ⟨e, r27, rth, -, -, -, r9, -⟩ := key_H free reg rR (by rw [rk]; exact h)
  have cc := ThinSuppliers.complete_count free (by norm_num) reg (R_V rR) rth (by norm_num)
  exact ⟨rk.symm.trans e, rR, rth, r27, r9, by omega⟩

include free reg in
theorem class2 {K : ℕ × Finset ℕ} (hK : K ∈ (R63 D V).image (key63 D V)) (h : K.1 = 2) :
    K = (2, layer D V 3 (rep63 D V K)) ∧ K.2 = layer D V 3 (rep63 D V K) ∧
      rep63 D V K ∈ R63 D V ∧ (layer D V 3 (rep63 D V K)).card = 8 ∧
      (layer D V 4 (rep63 D V K)).card = 8 ∧
      BankPrice.Bank D V (layer D V 3 (rep63 D V K)) (layer D V 4 (rep63 D V K)) := by
  obtain ⟨rR, rk⟩ := rep_spec hK
  obtain ⟨e, -, -, ry, rz, rw, -⟩ := key_L free reg rR (by rw [rk]; exact h)
  have eK : K = (2, layer D V 3 (rep63 D V K)) := rk.symm.trans e
  exact ⟨eK, congrArg Prod.snd eK, rR, rz, rw, Close62.fat_bank free reg (R_V rR) ry rz rw⟩

include free reg in
theorem class3 {K : ℕ × Finset ℕ} (hK : K ∈ (R63 D V).image (key63 D V)) (h : K.1 = 3) :
    K = (3, layer D V 3 (rep63 D V K)) ∧ K.2 = layer D V 3 (rep63 D V K) ∧
      rep63 D V K ∈ R63 D V ∧ (layer D V 2 (rep63 D V K)).card = 9 ∧
      (layer D V 3 (rep63 D V K)).card = 8 ∧ (layer D V 4 (rep63 D V K)).card = 9 := by
  obtain ⟨rR, rk⟩ := rep_spec hK
  obtain ⟨e, -, -, ry, rz, rw, -⟩ := key_M free reg rR (by rw [rk]; exact h)
  have eK : K = (3, layer D V 3 (rep63 D V K)) := rk.symm.trans e
  exact ⟨eK, congrArg Prod.snd eK, rR, ry, rz, rw⟩

/-! ### Part 2: the class bills -/

include free in
/-- **F, the class bill.** Roots of `C` share layer `j` and `|B_{j-1}|`, deficit at most `d`: the
total deficit is at most `60 B` plus the pair credit, when `d m ≤ B + m (m - 1)` for all `m`. -/
theorem class_bill63 {C Λ : Finset ℕ} {j s : ℕ} (d B : ℕ) (hj : 1 ≤ j) (hjq : 2 * j ≤ 9)
    (CV : C ⊆ V) (lay : ∀ u ∈ C, layer D V j u = Λ)
    (cb : ∀ u ∈ C, (ball D V u (j - 1)).card = s)
    (hd : ∀ u ∈ C, 64 - ((ball D V u 3).card + (ball D V u 4).card) ≤ d)
    (hB : ∀ m, d * m ≤ B + m * (m - 1)) :
    ∑ v ∈ C, 60 * (64 - ((ball D V v 3).card + (ball D V v 4).card)) ≤
      60 * ∑ w ∈ C, (C.filter (fun x => x ∈ gap D V 3 4 w)).card + 60 * B := by
  have cg := Close54.class_gap (j := j) (i := 3) (i' := 4) (s := s) (Λ := Λ) (K₂ := ∅) free hj
    hjq (by norm_num) (by norm_num) CV (empty_subset _) (disjoint_empty_right _) lay
    (fun v hv => absurd hv (notMem_empty v)) cb (fun v hv => absurd hv (notMem_empty v))
  rw [union_empty, card_empty] at cg
  have s1 : ∑ v ∈ C, 60 * (64 - ((ball D V v 3).card + (ball D V v 4).card)) ≤
      ∑ _v ∈ C, 60 * d := sum_le_sum (fun v hv => by have := hd v hv; omega)
  rw [sum_const, smul_eq_mul] at s1
  have e : C.card * (60 * d) = 60 * (d * C.card) := by ring
  have := hB C.card
  omega

include free reg in
/-- **Every class is paid, with its slack.** -/
theorem bill63 {K : ℕ × Finset ℕ} (hK : K ∈ (R63 D V).image (key63 D V)) :
    ∑ v ∈ (R63 D V).filter (fun v => key63 D V v = K),
        60 * (64 - ((ball D V v 3).card + (ball D V v 4).card)) + slack63 D V K ≤
      60 * ∑ w ∈ (R63 D V).filter (fun v => key63 D V v = K),
          (((R63 D V).filter (fun v => key63 D V v = K)).filter
            (fun x => x ∈ gap D V 3 4 w)).card +
        rate63 D V K * (pay63 D V K).card := by
  have CV : (R63 D V).filter (fun v => key63 D V v = K) ⊆ V :=
    fun v hv => R_V (mem_filter.mp hv).1
  have tl := tag_lt hK
  rcases (show K.1 = 0 ∨ K.1 = 1 ∨ K.1 = 2 ∨ K.1 = 3 by omega) with h | h | h | h
  · -- T
    obtain ⟨-, K2, rR, r26, ry, -, r8, r11, -⟩ := class0 free reg hK h
    have rV := R_V rR
    have mem : ∀ v ∈ (R63 D V).filter (fun v => key63 D V v = K), layer D V 2 v = K.2 ∧
        (layer D V 4 v).card = (layer D V 4 (rep63 D V K)).card ∧
        (ball D V v 3).card = 26 ∧ (ball D V v 4).card = (layer D V 4 v).card + 26 := by
      intro v hv
      obtain ⟨vR, kv⟩ := mem_filter.mp hv
      obtain ⟨ev, v26, -, -, -, -, -, v4⟩ := key_T free reg vR (by rw [kv]; exact h)
      have l2 : layer D V 2 v = K.2 := (congrArg Prod.snd (kv.symm.trans ev)).symm
      have e4 := (t_layers free reg (R_V vR) rV v26 r26 (l2.trans K2)).2
      exact ⟨l2, by rw [e4], v26, v4⟩
    have lay : ∀ v ∈ (R63 D V).filter (fun v => key63 D V v = K), layer D V 2 v = K.2 :=
      fun v hv => (mem v hv).1
    have cb : ∀ v ∈ (R63 D V).filter (fun v => key63 D V v = K), (ball D V v (2 - 1)).card = 10 :=
      fun v hv => (Floors7Row.balls9 free reg (CV hv)).1
    have pc : (pay63 D V K).card = 8 := by rw [pay_0 h, K2]; exact ry
    rw [slack_0 h, rate_0 h, pc]
    rcases (show (layer D V 4 (rep63 D V K)).card = 8 ∨ (layer D V 4 (rep63 D V K)).card = 9 ∨
        10 ≤ (layer D V 4 (rep63 D V K)).card by omega) with w | w | w
    · have hb := class_bill63 free 4 6 (by norm_num) (by norm_num) CV lay cb
        (fun v hv => by obtain ⟨-, e4, e3, e5⟩ := mem v hv; omega)
        (tri (fun m hm => by interval_cases m <;> omega))
      rw [if_neg (by omega), if_pos w]
      omega
    · have hb := class_bill63 free 3 4 (by norm_num) (by norm_num) CV lay cb
        (fun v hv => by obtain ⟨-, e4, e3, e5⟩ := mem v hv; omega)
        (tri (fun m hm => by interval_cases m <;> omega))
      rw [if_neg (by omega), if_neg (by omega)]
      omega
    · have hb := class_bill63 free 2 2 (by norm_num) (by norm_num) CV lay cb
        (fun v hv => by obtain ⟨-, e4, e3, e5⟩ := mem v hv; omega)
        (tri (fun m hm => by interval_cases m <;> omega))
      rw [if_pos w, if_neg (by omega)]
      omega
  · -- H
    obtain ⟨-, -, -, -, -, cc⟩ := class1 free reg hK h
    have mem : ∀ v ∈ (R63 D V).filter (fun v => key63 D V v = K), layer D V 2 v = K.2 ∧
        64 - ((ball D V v 3).card + (ball D V v 4).card) ≤ 2 := by
      intro v hv
      obtain ⟨vR, kv⟩ := mem_filter.mp hv
      obtain ⟨ev, v27, -, -, -, v8, -, v4⟩ := key_H free reg vR (by rw [kv]; exact h)
      exact ⟨(congrArg Prod.snd (kv.symm.trans ev)).symm, by omega⟩
    have hb := class_bill63 free (j := 2) (s := 10) 2 2 (by norm_num) (by norm_num) CV
      (fun v hv => (mem v hv).1) (fun v hv => (Floors7Row.balls9 free reg (CV hv)).1)
      (fun v hv => (mem v hv).2) (tri (fun m hm => by interval_cases m <;> omega))
    have pc : 7 ≤ (pay63 D V K).card := by rw [pay_1 h]; exact cc
    rw [slack_1 h, rate_1 h]
    omega
  · -- L
    obtain ⟨-, K2, -, rz, -, -⟩ := class2 free reg hK h
    have mem : ∀ v ∈ (R63 D V).filter (fun v => key63 D V v = K), layer D V 3 v = K.2 ∧
        (ball D V v (3 - 1)).card = 19 ∧ 64 - ((ball D V v 3).card + (ball D V v 4).card) ≤ 2 := by
      intro v hv
      obtain ⟨vR, kv⟩ := mem_filter.mp hv
      obtain ⟨ev, v27, -, vy, -, -, v4⟩ := key_L free reg vR (by rw [kv]; exact h)
      have b2 := (Floors7Row.balls9 free reg (R_V vR)).2.1
      exact ⟨(congrArg Prod.snd (kv.symm.trans ev)).symm, by show (ball D V v 2).card = 19; omega,
        by omega⟩
    have hb := class_bill63 free (j := 3) (s := 19) 2 2 (by norm_num) (by norm_num) CV
      (fun v hv => (mem v hv).1) (fun v hv => (mem v hv).2.1) (fun v hv => (mem v hv).2.2)
      (tri (fun m hm => by interval_cases m <;> omega))
    have pc : (pay63 D V K).card = 8 := by rw [pay_2 h, K2]; exact rz
    rw [slack_2 h, rate_2 h, pc]
    omega
  · -- M
    obtain ⟨-, -, rR, ry, rz, -⟩ := class3 free reg hK h
    have g6 := (fat_good free reg (R_V rR) ry rz).1
    have mem : ∀ v ∈ (R63 D V).filter (fun v => key63 D V v = K), layer D V 3 v = K.2 ∧
        (ball D V v (3 - 1)).card = 19 ∧ 64 - ((ball D V v 3).card + (ball D V v 4).card) ≤ 1 := by
      intro v hv
      obtain ⟨vR, kv⟩ := mem_filter.mp hv
      obtain ⟨ev, v27, -, vy, -, -, v4⟩ := key_M free reg vR (by rw [kv]; exact h)
      have b2 := (Floors7Row.balls9 free reg (R_V vR)).2.1
      exact ⟨(congrArg Prod.snd (kv.symm.trans ev)).symm, by show (ball D V v 2).card = 19; omega,
        by omega⟩
    have hb := class_bill63 free (j := 3) (s := 19) 1 1 (by norm_num) (by norm_num) CV
      (fun v hv => (mem v hv).1) (fun v hv => (mem v hv).2.1) (fun v hv => (mem v hv).2.2)
      (tri (fun m hm => by interval_cases m <;> omega))
    have pc : 6 ≤ (pay63 D V K).card := by rw [pay_3 h]; exact g6
    rw [slack_3 h, rate_3 h]
    omega

/-! ### Part 2: the row capacities -/

include free reg in
/-- A bank row scores at least `65` (`BankPrice.a2_bank`). -/
theorem bank_row {x : ℕ} (h : InBank D V x) :
    65 ≤ (ball D V x 3).card + (ball D V x 4).card := by
  obtain ⟨K, A, b, -, hA, hx⟩ := h
  exact BankPrice.a2_bank free reg b hA hx

include free reg in
/-- **Every row is charged at most its capacity, minus its row slack.** -/
theorem cap63 {x : ℕ} (hx : x ∈ V) :
    ∑ K ∈ ((R63 D V).image (key63 D V)).filter (fun K => x ∈ pay63 D V K), rate63 D V K +
        rslack63 D V x ≤ 60 * ((ball D V x 3).card + (ball D V x 4).card - 64) := by
  set C := (R63 D V).image (key63 D V) with hC
  set F := C.filter (fun K => x ∈ pay63 D V K) with hF
  have h1 := sum_filter_add_sum_filter_not F (fun K => K.1 = 1) (rate63 D V)
  set F1 := F.filter (fun K => K.1 = 1) with hF1
  set G := F.filter (fun K => ¬ K.1 = 1) with hG
  have h2 := sum_filter_add_sum_filter_not G (fun K => K.1 = 3) (rate63 D V)
  set F3 := G.filter (fun K => K.1 = 3) with hF3
  set G' := G.filter (fun K => ¬ K.1 = 3) with hG'
  have h3 := sum_filter_add_sum_filter_not G' (fun K => K.1 = 0) (rate63 D V)
  set F0 := G'.filter (fun K => K.1 = 0) with hF0
  set F2 := G'.filter (fun K => ¬ K.1 = 0) with hF2
  -- membership
  have e1 : ∀ K ∈ F1, K ∈ C ∧ x ∈ pay63 D V K ∧ K.1 = 1 := by
    intro K hK
    obtain ⟨a, a1⟩ := mem_filter.mp hK
    obtain ⟨b, b1⟩ := mem_filter.mp a
    exact ⟨b, b1, a1⟩
  have e3 : ∀ K ∈ F3, K ∈ C ∧ x ∈ pay63 D V K ∧ K.1 = 3 := by
    intro K hK
    obtain ⟨a, a1⟩ := mem_filter.mp hK
    obtain ⟨b, -⟩ := mem_filter.mp a
    obtain ⟨c, c1⟩ := mem_filter.mp b
    exact ⟨c, c1, a1⟩
  have e0 : ∀ K ∈ F0, K ∈ C ∧ x ∈ pay63 D V K ∧ K.1 = 0 := by
    intro K hK
    obtain ⟨a, a1⟩ := mem_filter.mp hK
    obtain ⟨b, -⟩ := mem_filter.mp a
    obtain ⟨c, -⟩ := mem_filter.mp b
    obtain ⟨d, d1⟩ := mem_filter.mp c
    exact ⟨d, d1, a1⟩
  have e2 : ∀ K ∈ F2, K ∈ C ∧ x ∈ pay63 D V K ∧ K.1 = 2 := by
    intro K hK
    obtain ⟨a, a1⟩ := mem_filter.mp hK
    obtain ⟨b, b1⟩ := mem_filter.mp a
    obtain ⟨c, c1⟩ := mem_filter.mp b
    obtain ⟨d, d1⟩ := mem_filter.mp c
    have := tag_lt d
    exact ⟨d, d1, by omega⟩
  -- T-classes: bank rows of the second layer
  have t0 : ∀ K ∈ F0, x ∈ layer D V 2 (rep63 D V K) ∧ InBank D V x := by
    intro K hK
    obtain ⟨KC, xK, h0⟩ := e0 K hK
    obtain ⟨-, K2, -, -, ry, rz, -, -, B⟩ := class0 free reg KC h0
    have xr : x ∈ layer D V 2 (rep63 D V K) := by rw [pay_0 h0, K2] at xK; exact xK
    exact ⟨xr, _, _, B, ry, rz, xr⟩
  have c0 : F0.card ≤ 1 := by
    refine card_le_one.mpr (fun K hK K' hK' => ?_)
    obtain ⟨KC, -, h0⟩ := e0 K hK
    obtain ⟨KC', -, h0'⟩ := e0 K' hK'
    obtain ⟨eK, -, -, -, ry, -, -, -, B⟩ := class0 free reg KC h0
    obtain ⟨eK', -, -, -, ry', -, -, -, B'⟩ := class0 free reg KC' h0'
    have m := RowBanks.banks_meet free (by norm_num) B.KV B'.KV (by rw [ry]) (by rw [ry'])
      B.one B'.one B.keep B'.keep B.full B'.full (t0 K hK).1 (t0 K' hK').1
    rw [eK, eK', m]
  -- L-classes: bank rows of the third layer
  have t2 : ∀ K ∈ F2, x ∈ layer D V 3 (rep63 D V K) ∧ InBank D V x := by
    intro K hK
    obtain ⟨KC, xK, h2'⟩ := e2 K hK
    obtain ⟨-, K2, -, rz, rw, B⟩ := class2 free reg KC h2'
    have xr : x ∈ layer D V 3 (rep63 D V K) := by rw [pay_2 h2', K2] at xK; exact xK
    exact ⟨xr, _, _, B, rz, rw, xr⟩
  have c2 : F2.card ≤ 1 := by
    refine card_le_one.mpr (fun K hK K' hK' => ?_)
    obtain ⟨KC, -, h2'⟩ := e2 K hK
    obtain ⟨KC', -, h2''⟩ := e2 K' hK'
    obtain ⟨eK, -, -, rz, -, B⟩ := class2 free reg KC h2'
    obtain ⟨eK', -, -, rz', -, B'⟩ := class2 free reg KC' h2''
    have m := RowBanks.banks_meet free (by norm_num) B.KV B'.KV (by rw [rz]) (by rw [rz'])
      B.one B'.one B.keep B'.keep B.full B'.full (t2 K hK).1 (t2 K' hK').1
    rw [eK, eK', m]
  -- M-classes: good rows, in `zRows` of the third layer
  have t3 : ∀ K ∈ F3, x ∈ Supplier54.zRows D V (layer D V 3 (rep63 D V K)) ∧
      65 ≤ (ball D V x 3).card + (ball D V x 4).card := by
    intro K hK
    obtain ⟨KC, xK, h3'⟩ := e3 K hK
    obtain ⟨-, -, rR, ry, rz, rw⟩ := class3 free reg KC h3'
    rw [pay_3 h3'] at xK
    have sc := fat_score free reg (R_V rR) ry rz (by omega) (by omega) xK
    exact ⟨(fat_good free reg (R_V rR) ry rz).2.1 xK, by omega⟩
  have c3 : F3.card ≤ 1 := by
    refine card_le_one.mpr (fun K hK K' hK' => ?_)
    obtain ⟨KC, -, h3'⟩ := e3 K hK
    obtain ⟨KC', -, h3''⟩ := e3 K' hK'
    obtain ⟨eK, -, -, -, rz, -⟩ := class3 free reg KC h3'
    obtain ⟨eK', -, -, -, rz', -⟩ := class3 free reg KC' h3''
    have m : layer D V 3 (rep63 D V K) = layer D V 3 (rep63 D V K') := by
      by_contra ne
      exact Supplier54.zRows_exclusive free (by norm_num) ne (by rw [rz, rz']) (t3 K hK).1
        (t3 K' hK').1
    rw [eK, eK', m]
  -- sums
  have s1 : ∑ K ∈ F1, rate63 D V K = 20 * F1.card := by
    rw [sum_congr rfl (fun K hK => rate_1 (e1 K hK).2.2), sum_const, smul_eq_mul, mul_comm]
  have s0 : ∑ K ∈ F0, rate63 D V K ≤ 45 * F0.card := by
    have := sum_le_card_nsmul F0 (rate63 D V) 45 (fun K hK => by
      rw [rate_0 (e0 K hK).2.2]; split_ifs <;> norm_num)
    rw [smul_eq_mul, mul_comm] at this
    exact this
  have s2 : ∑ K ∈ F2, rate63 D V K ≤ 15 * F2.card := by
    have := sum_le_card_nsmul F2 (rate63 D V) 15 (fun K hK => by
      rw [rate_2 (e2 K hK).2.2])
    rw [smul_eq_mul, mul_comm] at this
    exact this
  have s3 : ∑ K ∈ F3, rate63 D V K ≤ 12 * F3.card := by
    have := sum_le_card_nsmul F3 (rate63 D V) 12 (fun K hK => by
      rw [rate_3 (e3 K hK).2.2])
    rw [smul_eq_mul, mul_comm] at this
    exact this
  -- positivity forces a high score
  have p0 : 0 < F0.card → 65 ≤ (ball D V x 3).card + (ball D V x 4).card := by
    intro hp
    obtain ⟨K, hK⟩ := card_pos.mp hp
    exact bank_row free reg (t0 K hK).2
  have p2 : 0 < F2.card → 65 ≤ (ball D V x 3).card + (ball D V x 4).card := by
    intro hp
    obtain ⟨K, hK⟩ := card_pos.mp hp
    exact bank_row free reg (t2 K hK).2
  have p3 : 0 < F3.card → 65 ≤ (ball D V x 3).card + (ball D V x 4).card := by
    intro hp
    obtain ⟨K, hK⟩ := card_pos.mp hp
    exact (t3 K hK).2
  have pr : rslack63 D V x ≤ 1 ∧
      (0 < rslack63 D V x → 65 ≤ (ball D V x 3).card + (ball D V x 4).card) := by
    unfold rslack63
    split_ifs with hc
    · exact ⟨le_rfl, fun _ => bank_row free reg hc.1⟩
    · exact ⟨by norm_num, fun h => by omega⟩
  -- law G: a T-class at rate 45 excludes the row slack and every M-class
  have pT : ∑ K ∈ F0, rate63 D V K ≤ 30 * F0.card ∨ (rslack63 D V x = 0 ∧ F3.card = 0) := by
    by_cases hT : ∃ K ∈ F0, (layer D V 4 (rep63 D V K)).card = 8
    · obtain ⟨K, hK, w8⟩ := hT
      obtain ⟨KC, -, h0⟩ := e0 K hK
      obtain ⟨-, -, rR, r26, -, rz, -, -, B⟩ := class0 free reg KC h0
      have xr := (t0 K hK).1
      refine Or.inr ⟨?_, ?_⟩
      · unfold rslack63
        rw [if_neg (fun h => h.2 ⟨rep63 D V K, rR, r26, w8, xr⟩)]
      · by_contra hne
        obtain ⟨K', hK'⟩ := card_pos.mp (by omega : 0 < F3.card)
        obtain ⟨KC', -, h3'⟩ := e3 K' hK'
        obtain ⟨-, -, rR', ry', rz', rw'⟩ := class3 free reg KC' h3'
        have zx := bank_zRows B xr
        have m : layer D V 3 (rep63 D V K) = layer D V 3 (rep63 D V K') := by
          by_contra ne
          exact Supplier54.zRows_exclusive free (by norm_num) ne (by rw [rz, rz']) zx
            (t3 K' hK').1
        have tn : layer D V 4 (rep63 D V K) =
            (layer D V 3 (rep63 D V K)).biUnion (outN D V) \ layer D V 3 (rep63 D V K) :=
          next_layer (R_V rR) (j := 3) (by norm_num) (t_zkeep free reg (R_V rR) r26)
        have fn := fat_next free reg (R_V rR') ry' rz'
        rw [tn, m, ← fn] at w8
        omega
    · push Not at hT
      refine Or.inl ?_
      have := sum_le_card_nsmul F0 (rate63 D V) 30 (fun K hK => by
        rw [rate_0 (e0 K hK).2.2, if_neg (hT K hK)])
      rw [smul_eq_mul, mul_comm] at this
      exact this
  -- H-classes: the supplier score
  have pH : 0 < F1.card → 60 + min (F1.card + 2) 8 + min (F1.card + 3) 8 ≤
      (ball D V x 3).card + (ball D V x 4).card ∧ F1.card ≤ 9 := by
    intro hp
    obtain ⟨K0, hK0⟩ := card_pos.mp hp
    have inj : Set.InjOn (rep63 D V) F1 := by
      intro K hK K' hK' e
      obtain ⟨-, rk⟩ := rep_spec (e1 K hK).1
      obtain ⟨-, rk'⟩ := rep_spec (e1 K' hK').1
      rw [← rk, ← rk']
      exact congrArg (key63 D V) e
    have cR : (F1.image (rep63 D V)).card = F1.card := card_image_of_injOn inj
    have sc := TopRowFat.supplier_score (q := 7) (r := 9) (i := 3) (j := 4) free (by norm_num)
      (by norm_num) reg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (R := F1.image (rep63 D V))
      (fun w hw => by
        obtain ⟨K, hK, rfl⟩ := mem_image.mp hw
        exact R_V (class1 free reg (e1 K hK).1 (e1 K hK).2.2).2.1)
      (fun w hw => by
        obtain ⟨K, hK, rfl⟩ := mem_image.mp hw
        exact (class1 free reg (e1 K hK).1 (e1 K hK).2.2).2.2.1)
      (fun w hw => by
        obtain ⟨K, hK, rfl⟩ := mem_image.mp hw
        have := (e1 K hK).2.1
        rwa [pay_1 (e1 K hK).2.2] at this)
      (fun w hw w' hw' e => by
        obtain ⟨K, hK, rfl⟩ := mem_image.mp hw
        obtain ⟨K', hK', rfl⟩ := mem_image.mp hw'
        have eK := (class1 free reg (e1 K hK).1 (e1 K hK).2.2).1
        have eK' := (class1 free reg (e1 K' hK').1 (e1 K' hK').2.2).1
        have : K = K' := eK.trans ((congrArg (fun Y => ((1 : ℕ), Y)) e).trans eK'.symm)
        rw [this])
      (mem_image_of_mem (rep63 D V) hK0)
    obtain ⟨-, cR', cth, c27, c9, -⟩ := class1 free reg (e1 K0 hK0).1 (e1 K0 hK0).2.2
    have hf := h_floor free reg (R_V cR') cth c27 c9
    have e4 : ball D V (rep63 D V K0) (3 + 1) = ball D V (rep63 D V K0) 4 := rfl
    have e5 : ball D V (rep63 D V K0) (4 + 1) = ball D V (rep63 D V K0) 5 := rfl
    rw [e4, e5, cR] at sc
    obtain ⟨sc1, sc2⟩ := sc
    constructor <;> omega
  omega

/-! ### Part 2: the tie, and no bank -/

include free reg in
/-- **No saver that is not thin** at order `63`. -/
theorem fat63 (n : V.card = 63) :
    ∀ v ∈ V, ¬ Thin D V 9 v → 64 ≤ (ball D V v 3).card + (ball D V v 4).card := by
  -- the ledger, in units of `1/60`
  have tot : ∑ x ∈ V, 60 * ((ball D V x 3).card + (ball D V x 4).card - 64) +
      60 * ∑ v ∈ V, (gap D V 3 4 v).card ≤
      ∑ v ∈ R63 D V, 60 * (64 - ((ball D V v 3).card + (ball D V v 4).card)) := by
    have led := Close54.ledger_split (D := D) (V := V) (i := 3) (i' := 4) free (by norm_num)
    have e1 : ∑ x ∈ V, 60 * ((ball D V x 3).card + (ball D V x 4).card - 64) =
        60 * ∑ v ∈ V, ((ball D V v 3).card + (ball D V v 4).card - (V.card + 1)) := by
      rw [mul_sum]; exact sum_congr rfl (fun v _ => by omega)
    have e2 : ∑ v ∈ V, 60 * (64 - ((ball D V v 3).card + (ball D V v 4).card)) =
        60 * ∑ v ∈ V, ((V.card + 1) - ((ball D V v 3).card + (ball D V v 4).card)) := by
      rw [mul_sum]; exact sum_congr rfl (fun v _ => by omega)
    have spl := sum_filter_add_sum_filter_not V
      (fun v => (ball D V v 3).card + (ball D V v 4).card ≤ 63)
      (fun v => 60 * (64 - ((ball D V v 3).card + (ball D V v 4).card)))
    rw [← R63_def] at spl
    have z : ∑ v ∈ V.filter (fun v => ¬ (ball D V v 3).card + (ball D V v 4).card ≤ 63),
        60 * (64 - ((ball D V v 3).card + (ball D V v 4).card)) = 0 :=
      sum_eq_zero (fun v hv => by have := (mem_filter.mp hv).2; omega)
    omega
  have hG : ∑ K ∈ (R63 D V).image (key63 D V),
      60 * ∑ w ∈ (R63 D V).filter (fun v => key63 D V v = K),
        (((R63 D V).filter (fun v => key63 D V v = K)).filter
          (fun x => x ∈ gap D V 3 4 w)).card ≤ 60 * ∑ v ∈ V, (gap D V 3 4 v).card := by
    rw [← mul_sum]
    refine Nat.mul_le_mul_left 60 ?_
    calc ∑ K ∈ (R63 D V).image (key63 D V), ∑ w ∈ (R63 D V).filter (fun v => key63 D V v = K),
          (((R63 D V).filter (fun v => key63 D V v = K)).filter
            (fun x => x ∈ gap D V 3 4 w)).card
        ≤ ∑ K ∈ (R63 D V).image (key63 D V),
            ∑ w ∈ (R63 D V).filter (fun v => key63 D V v = K), (gap D V 3 4 w).card :=
          sum_le_sum (fun K _ => sum_le_sum (fun w _ => card_le_card
            (fun x hx => (mem_filter.mp hx).2)))
      _ = ∑ w ∈ R63 D V, (gap D V 3 4 w).card :=
          sum_fiberwise_of_maps_to (fun v hv => mem_image_of_mem (key63 D V) hv) _
      _ ≤ ∑ v ∈ V, (gap D V 3 4 v).card := sum_le_sum_of_subset (fun v hv => R_V hv)
  have hP : ∀ K ∈ (R63 D V).image (key63 D V), pay63 D V K ⊆ V := by
    intro K hK
    have tl := tag_lt hK
    rcases (show K.1 = 0 ∨ K.1 = 1 ∨ K.1 = 2 ∨ K.1 = 3 by omega) with h | h | h | h
    · rw [pay_0 h, (class0 free reg hK h).2.1]; exact layer_subset
    · rw [pay_1 h]; exact complete_subset.trans outN_subset
    · rw [pay_2 h, (class2 free reg hK h).2.1]; exact layer_subset
    · rw [pay_3 h]; exact fun s hs => good_V hs
  obtain ⟨ex1, ex2⟩ := payment_exact (R := R63 D V) (P := V) (key63 D V)
    (fun v => 60 * (64 - ((ball D V v 3).card + (ball D V v 4).card)))
    (fun x => 60 * ((ball D V x 3).card + (ball D V x 4).card - 64))
    (fun K => 60 * ∑ w ∈ (R63 D V).filter (fun v => key63 D V v = K),
        (((R63 D V).filter (fun v => key63 D V v = K)).filter
          (fun x => x ∈ gap D V 3 4 w)).card)
    (rate63 D V) (slack63 D V) (rslack63 D V) (pay63 D V)
    (60 * ∑ v ∈ V, (gap D V 3 4 v).card) hG (fun K hK => bill63 free reg hK) hP
    (fun x hx => cap63 free reg hx) tot
  -- every bank row is a T-payer with `|W| = 8`; so the exterior of a bank is a bank
  have succ : ∀ K A, BankPrice.Bank D V K A → K.card = 7 + 1 → A.card = 7 + 1 →
      ∃ A', BankPrice.Bank D V A A' ∧ A'.card = 7 + 1 := by
    intro K A b hK hA
    obtain ⟨x, hx⟩ := card_pos.mp (by rw [hK]; norm_num : 0 < K.card)
    have r0 := ex2 x (b.KV hx)
    have t8 : T8 D V x := by
      by_contra nt
      unfold rslack63 at r0
      rw [if_pos ⟨⟨K, A, b, hK, hA, hx⟩, nt⟩] at r0
      exact absurd r0 one_ne_zero
    obtain ⟨u, uR, u26, w8, xu⟩ := t8
    have uV := R_V uR
    obtain ⟨th, z8⟩ := Floors7Row.b3_26 free reg uV u26
    have y8 : (layer D V 2 u).card = 8 := by unfold Thin at th; omega
    have Bu := t_bank free reg uV u26
    have eK : K = layer D V 2 u := RowBanks.banks_meet free (by norm_num) b.KV Bu.KV hK
      (by rw [y8]) b.one Bu.one b.keep Bu.keep b.full Bu.full hx xu
    rw [eK] at b
    have eA : A = layer D V 3 u := bank_ext_unique b Bu (card_pos.mp (by rw [y8]; norm_num))
    rw [eA]
    exact ⟨layer D V 4 u, t8_bank free reg uV u26 w8, w8⟩
  have noBank : ∀ K A, BankPrice.Bank D V K A → K.card = 7 + 1 → A.card = 7 + 1 → False :=
    fun K A b hK hA => no_bank_of_succ free (by norm_num) (by rw [n]; norm_num) succ b hK hA
  intro v hv nt
  by_contra low
  have vR : v ∈ R63 D V := mem_filter.mpr ⟨hv, by omega⟩
  rcases key_data free reg vR with h | h | h | h
  · exact nt h.2.2.1
  · exact nt h.2.2.1
  · obtain ⟨-, -, -, hY, hZ, hW, -⟩ := h
    exact noBank _ _ (Close62.fat_bank free reg hv hY hZ hW) (by rw [hZ]) (by rw [hW])
  · have kC : key63 D V v ∈ (R63 D V).image (key63 D V) := mem_image_of_mem _ vR
    have s := ex1 _ kC
    rw [slack_3 (by rw [h.1])] at s
    exact absurd s one_ne_zero

/-! ### Part 3: the theorems -/

include free reg in
/-- **Order 63, out-regular.** -/
theorem no63_regular (n : V.card = 63) : False :=
  TopRow.no63_of_fat free reg n (Floors7Row.floors7 free reg) (end63 free reg) (fat63 free reg n)

end count

/-- **Order 63.** No `7`-free digraph of minimum out-degree `9` has `63` labels. -/
theorem no_63 (free : QFree D V 7) (deg : ∀ v ∈ V, 9 ≤ (outN D V v).card) (n : V.card = 63) :
    False := by
  obtain ⟨E, freeE, regE⟩ := CollarBound.exists_regular free deg
  exact no63_regular freeE regE n

/-- No counterexample at degree `9`, cutoff `7` has `63` labels. -/
theorem excluded_63 {p : Input} (bad : Bad p) (hs : p.s = 9) (hc : cutoff p = 7) :
    p.n ≠ 63 := by
  intro hn
  have free : QFree p.D (range p.n) (cutoff p) := qfree_of_noShort bad.loopless bad.missing
  rw [hc] at free
  have deg : ∀ v ∈ range p.n, 9 ≤ (outN p.D (range p.n) v).card := fun v hv => by
    rw [← hs]
    exact Compose.FloorSix.out_card bad.degree (mem_range.mp hv)
  exact no_63 free deg (by rw [card_range, hn])

#print axioms tri
#print axioms saver_cases
#print axioms key_data
#print axioms class_bill63
#print axioms bill63
#print axioms cap63
#print axioms fat63
#print axioms no63_regular
#print axioms no_63
#print axioms excluded_63

end LeanCH.BR.Close63
