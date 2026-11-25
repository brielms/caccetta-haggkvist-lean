import checkpoints.shen_extension.BankPrice

/-!
# The bank price as a function of `(q, r, a)`

`BankPrice.a1` and `BankPrice.b1` bound the exterior of a `Chain D V r A B C E` by hand-written
case analysis at `(q, r) = (7, 9)` and `(8, 9)`. Here the same steps are stated once, generic in
`q`, `r` and the four sizes, as a decidable predicate `admissible q r a b c e`, and the price is
the least weighted exterior over the admissible sizes, `extFloor q r a α β γ`.

## Part 1: necessary conditions (`chain_admissible`)
`fragOK q r N nf m` is what a `q`-free fragment of `N` labels, `nf` of them full rows (exactly `r`
heads inside), all rows keeping `≥ m` heads inside, must satisfy:
* hosts: `m ≥ 1` gives `N ≥ q · min m 8 + 1` (`ShapeClimbMono.lower_hosts_every`, the closed lower
  degrees `≤ 8`) and `N ≥ m + 1` (loopless);
* budgets: for all radii `1 ≤ i ≤ j`, `i + j ≤ q`,
  `nf (fullFl i + fullFl j) + (N - nf)(ordFl i + ordFl j) ≤ N (N - 1)` (`mixed_budget`), with the
  ordinary floor `ordFl` (`ball_grow` at `m = 1`, `ordinary_floor` at `m ≥ 2`, `ordinary_rows` at
  `m ≥ 3`, `q ≥ 6`) and the full floor `fullFl` (`r` heads, `full_floor`, `full_row`).
The chain gives three fragments, N1–N3: `A` (`m = r - b`), `A ∪ B` (`nf = a`, `m = r - c`),
`A ∪ B ∪ C` (`nf = a + b`, `m = r - e`); and N4 (`TopRowFat.loop_complete`): `a = q + 1`,
`b + 1 ≤ r` forces `b + 1 = r` and `B` keeps its heads in `B ∪ C` (fragment `B`, `m = r - c`);
then `b = q + 1`, `c + 1 ≤ r` forces `c + 1 = r` and `C` keeps its heads in `C ∪ E`
(fragment `C`, `m = r - e`).

## Part 2: the price (`ext_floor_chain`, `bank_price*`, `bank_score`)
`extFloor` scans `b, c` over the box `α b ≤ M`, `β c ≤ M`, `M = (α + β + γ) r`, and takes the
first admissible `e`; outside the box `α b + β c > M ≥ extFloor`. Regressions by kernel
evaluation: `extFloor 7 9 8 2 2 1 = 40` (`a1`), `bFloor 8 9 8 = 9`, `extFloor 8 9 8 1 1 0 = 17`,
`extFloor 8 9 8 1 1 1 = 25` (`b1`), hence `a2_bank'` (`65`) and `b1_bank'` (`38`).
-/

set_option linter.style.longLine false
namespace LeanCH.BR.BankPriceRow
open Finset BRq2 BRq3
open DotTwoPassShellTransport (layer layer_subset)
open Profile54 (reach)
open BankPrice (Chain Bank)

variable {D : CH.Digraph} {q : ℕ} {V : Finset ℕ}

/-! ### Search combinators -/

/-- `f k` for every `k < n`. -/
def allBelow : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, f => allBelow n f && f n

theorem allBelow_of {f : ℕ → Bool} : ∀ {n : ℕ}, (∀ k < n, f k = true) → allBelow n f = true
  | 0, _ => rfl
  | n + 1, h => by
    simp only [allBelow, Bool.and_eq_true]
    exact ⟨allBelow_of (fun k hk => h k (by omega)), h n (by omega)⟩

/-- The least `k ∈ [lo, lo + n)` with `p k`, else `lo + n`. -/
def firstFrom (p : ℕ → Bool) : ℕ → ℕ → ℕ
  | lo, 0 => lo
  | lo, n + 1 => if p lo then lo else firstFrom p (lo + 1) n

theorem firstFrom_le {p : ℕ → Bool} : ∀ {n lo k : ℕ}, lo ≤ k → p k = true → firstFrom p lo n ≤ k
  | 0, _, _, h, _ => h
  | n + 1, lo, k, h, hp => by
    simp only [firstFrom]
    split
    · exact h
    · rename_i hlo
      have : lo ≠ k := fun e => hlo (by rw [e]; exact hp)
      exact firstFrom_le (by omega) hp

/-- `min acc (min_{lo ≤ k < lo + n} g k)`. -/
def minFrom (g : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, 0, acc => acc
  | lo, n + 1, acc => minFrom g (lo + 1) n (min acc (g lo))

theorem minFrom_le_acc {g : ℕ → ℕ} : ∀ {n lo acc : ℕ}, minFrom g lo n acc ≤ acc
  | 0, _, _ => le_rfl
  | n + 1, lo, acc => by
    simp only [minFrom]
    exact (minFrom_le_acc (n := n)).trans (min_le_left _ _)

theorem minFrom_le {g : ℕ → ℕ} : ∀ {n lo acc k : ℕ}, lo ≤ k → k < lo + n → minFrom g lo n acc ≤ g k
  | 0, _, _, _, h1, h2 => by omega
  | n + 1, lo, acc, k, h1, h2 => by
    simp only [minFrom]
    rcases Nat.eq_or_lt_of_le h1 with e | lt
    · subst e
      exact minFrom_le_acc.trans (min_le_right _ _)
    · exact minFrom_le (by omega) (by omega)

/-! ### Row floors as functions -/

/-- Ordinary floor at radius `i` when every row keeps `m` heads. -/
def ordFl (q m i : ℕ) : ℕ :=
  if m = 0 then 0 else if m = 1 then i else
    max (2 * i + (m - 2))
      (if 6 ≤ q ∧ 3 ≤ m then (if i = 3 then m + 6 else if 4 ≤ i then m + 8 else 0) else 0)

/-- Floor of a full row (exactly `r` heads inside) at radius `i`, fragment of `N` labels. -/
def fullFl (q r N m i : ℕ) : ℕ :=
  max (max (ordFl q m i) r)
    (if 2 ≤ m ∧ r + 1 ≤ N then
      max (if 3 ≤ i ∧ r + 2 ≤ 2 * q then r + 3 + min (m - 2) (N - (r + 1)) else 0)
        (if 4 ≤ i ∧ r + 5 ≤ 2 * q then r + 5 + min (m - 2) (N - (r + 1)) else 0)
    else 0)

/-- **Ordinary floor** (generic). -/
theorem ord_floor {F : Finset ℕ} {m i : ℕ} (free : QFree D F q) (hi1 : 1 ≤ i) (hi : i ≤ q)
    (deg : ∀ v ∈ F, m ≤ (outN D F v).card) {x : ℕ} (hx : x ∈ F) :
    ordFl q m i ≤ reach D F i x := by
  unfold ordFl
  by_cases h0 : m = 0
  · rw [if_pos h0]; exact Nat.zero_le _
  rw [if_neg h0]
  by_cases h1 : m = 1
  · rw [if_pos h1]
    have g := LoopCollar.ball_grow free (fun v hv => by have := deg v hv; omega) hx i hi
    have := Profile54.card_ball_erase (D := D) (W := F) (k := i) hx
    unfold reach
    omega
  rw [if_neg h1]
  have o := FragmentBudget.ordinary_floor (t := m - 2) free hi1 hi
    (fun v hv => by have := deg v hv; omega) hx
  refine max_le o ?_
  split_ifs with h6 h3 h4
  · subst h3
    have := (FullRow.ordinary_rows (t := m - 3) free h6.1
      (fun v hv => by have := deg v hv; omega) hx).1
    omega
  · have := (FullRow.ordinary_rows (t := m - 3) free h6.1
      (fun v hv => by have := deg v hv; omega) hx).2
    have := FragmentBudget.reach_mono (D := D) (F := F) (x := x) h4
    omega
  · exact Nat.zero_le _
  · exact Nat.zero_le _

/-- **Full floor** (generic). -/
theorem full_fl {F : Finset ℕ} {r m i : ℕ} (free : QFree D F q) (hi1 : 1 ≤ i) (hi : i ≤ q)
    (deg : ∀ v ∈ F, m ≤ (outN D F v).card) {x : ℕ} (hx : x ∈ F)
    (full : (outN D F x).card = r) : fullFl q r F.card m i ≤ reach D F i x := by
  have hq : 1 ≤ q := by omega
  have o := ord_floor free hi1 hi deg hx
  have rr : r ≤ reach D F i x := by
    have h1 : outN D F x ⊆ (ball D F x i).erase x := by
      intro v hv
      refine mem_erase.mpr ⟨?_, ball_mono_radius hi1 ((mem_ball_one hx).mpr (Or.inr hv))⟩
      intro e
      have h2 := (mem_outN.mp hv).2
      rw [e] at h2
      exact loopfree free hq hx h2
    rw [← full]
    exact card_le_card h1
  unfold fullFl
  refine max_le (max_le o rr) ?_
  by_cases hm : 2 ≤ m ∧ r + 1 ≤ F.card
  · rw [if_pos hm]
    have l1 := min_le_left (m - 2) (F.card - (r + 1))
    have l2 := min_le_right (m - 2) (F.card - (r + 1))
    have deg' : ∀ v ∈ F, 2 + min (m - 2) (F.card - (r + 1)) ≤ (outN D F v).card :=
      fun v hv => by have := deg v hv; omega
    have hN : r + 1 + min (m - 2) (F.card - (r + 1)) ≤ F.card := by omega
    refine max_le ?_ ?_
    · split_ifs with h3
      · exact FragmentBudget.full_floor free h3.1 hi h3.2 hN deg' hx full
      · exact Nat.zero_le _
    · split_ifs with h4
      · exact FullRow.full_row free h4.1 h4.2 hN deg' hx full
      · exact Nat.zero_le _
  · rw [if_neg hm]; exact Nat.zero_le _

/-- **The budget at radii `(i, j)`** (generic): full rows `Fs`, every row keeping `m` heads. -/
theorem budget_ineq {F Fs : Finset ℕ} {r m i j : ℕ} (free : QFree D F q) (FsF : Fs ⊆ F)
    (full : ∀ x ∈ Fs, (outN D F x).card = r) (deg : ∀ v ∈ F, m ≤ (outN D F v).card)
    (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i + j ≤ q) :
    Fs.card * (fullFl q r F.card m i + fullFl q r F.card m j) +
      (F.card - Fs.card) * (ordFl q m i + ordFl q m j) ≤ F.card * (F.card - 1) := by
  classical
  have mb := FragmentBudget.mixed_budget free hij (D := D) (F := F) (i := i) (j := j)
  have sp := sum_sdiff FsF (f := fun x => reach D F i x + reach D F j x)
  have s1 : Fs.card • (fullFl q r F.card m i + fullFl q r F.card m j) ≤
      ∑ x ∈ Fs, (reach D F i x + reach D F j x) :=
    card_nsmul_le_sum _ _ _ (fun x hx => add_le_add
      (full_fl free hi (by omega) deg (FsF hx) (full x hx))
      (full_fl free hj (by omega) deg (FsF hx) (full x hx)))
  have s2 : (F \ Fs).card • (ordFl q m i + ordFl q m j) ≤
      ∑ x ∈ F \ Fs, (reach D F i x + reach D F j x) :=
    card_nsmul_le_sum _ _ _ (fun x hx => add_le_add
      (ord_floor free hi (by omega) deg (mem_sdiff.mp hx).1)
      (ord_floor free hj (by omega) deg (mem_sdiff.mp hx).1))
  rw [smul_eq_mul] at s1 s2
  rw [card_sdiff_of_subset FsF] at s2
  omega

/-! ### The fragment test -/

/-- Budgets over all radii `1 ≤ i ≤ j`, `i + j ≤ q` (`i = k + 1`, `j = i + l`). -/
def budgetOK (q r N nf m : ℕ) : Bool :=
  allBelow (q / 2) fun k => allBelow (q + 1 - 2 * (k + 1)) fun l =>
    decide (nf * (fullFl q r N m (k + 1) + fullFl q r N m (k + 1 + l)) +
      (N - nf) * (ordFl q m (k + 1) + ordFl q m (k + 1 + l)) ≤ N * (N - 1))

/-- What a `q`-free fragment of `N` labels, `nf` full rows, minimum kept degree `m` satisfies. -/
def fragOK (q r N nf m : ℕ) : Bool :=
  decide (N = 0) || (decide (m = 0 ∨ (q * min m 8 + 1 ≤ N ∧ m + 1 ≤ N)) && budgetOK q r N nf m)

/-- **Fragment law** (generic in `q`, `r`, `m`). -/
theorem frag_ok {F Fs : Finset ℕ} {r m : ℕ} (free : QFree D F q) (hq : 1 ≤ q) (FsF : Fs ⊆ F)
    (full : ∀ x ∈ Fs, (outN D F x).card = r) (deg : ∀ v ∈ F, m ≤ (outN D F v).card) :
    fragOK q r F.card Fs.card m = true := by
  unfold fragOK
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rcases F.eq_empty_or_nonempty with h | ne
  · left; simp [h]
  right
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos m with h0 | hm
    · exact Or.inl h0
    right
    obtain ⟨x, hx⟩ := ne
    constructor
    · by_contra hlt
      have host := ShapeClimbMono.lower_hosts_every q (min m 8) (by rw [Profile54.floor_nine]; omega)
      exact host D F ⟨x, hx⟩ (by omega) free (fun v hv => (min_le_left _ _).trans (deg v hv))
    · have sub : outN D F x ⊆ F.erase x := fun v hv => mem_erase.mpr
        ⟨fun e => loopfree free hq hx (by have h2 := (mem_outN.mp hv).2; rw [e] at h2; exact h2),
          outN_subset hv⟩
      have := card_le_card sub
      rw [card_erase_of_mem hx] at this
      have := deg x hx
      omega
  · unfold budgetOK
    apply allBelow_of
    intro k hk
    apply allBelow_of
    intro l hl
    exact decide_eq_true (budget_ineq free FsF full deg (by omega) (by omega) (by omega))

/-! ### Part 1: the admissible sizes of a chain -/

/-- N1 on `A`. -/
def adm1 (q r a b : ℕ) : Bool := fragOK q r a 0 (r - b)

/-- N4, first step: `a = q + 1`, `b + 1 ≤ r`. -/
def n4a (q r a b c : ℕ) : Bool :=
  !decide (a = q + 1 ∧ b + 1 ≤ r ∧ 2 ≤ q) || (decide (b + 1 = r) && fragOK q r b 0 (r - c))

/-- Conditions free of `e`: N1 on `A`, N2 on `A ∪ B`, N4 first step. -/
def adm2 (q r a b c : ℕ) : Bool := adm1 q r a b && fragOK q r (a + b) a (r - c) && n4a q r a b c

/-- N4, second step: `a = b = q + 1`, `c + 1 ≤ r`. -/
def n4b (q r a b c e : ℕ) : Bool :=
  !decide (a = q + 1 ∧ b + 1 ≤ r ∧ b = q + 1 ∧ c + 1 ≤ r ∧ 3 ≤ q) ||
    (decide (c + 1 = r) && fragOK q r c 0 (r - e))

/-- Conditions with `e`: N3 on `A ∪ B ∪ C`, N4 second step. -/
def adm3 (q r a b c e : ℕ) : Bool := fragOK q r (a + b + c) (a + b) (r - e) && n4b q r a b c e

def admissible (q r a b c e : ℕ) : Bool := adm2 q r a b c && adm3 q r a b c e

section chain
variable {r : ℕ} {A B C E : Finset ℕ}

theorem kept_deg {S T : Finset ℕ} {v : ℕ} (deg : (outN D V v).card = r) (keep : outN D V v ⊆ S ∪ T) :
    r - T.card ≤ (outN D S v).card := by
  have := FragmentBudget.keep_le keep
  omega

theorem chain_adm1 (free : QFree D V q) (hq : 1 ≤ q) (ch : Chain D V r A B C E) :
    adm1 q r A.card B.card = true := by
  have := frag_ok (r := r) (Fs := ∅) (free.mono_set ch.AV) hq (empty_subset _) (by simp)
    (fun v hv => kept_deg (ch.degA v hv) (ch.kA v hv))
  rwa [card_empty] at this

/-- `B` keeps its heads in `B ∪ C` when `A` is a loop of `q + 1` complete to `B`. -/
theorem step_one (free : QFree D V q) (hq : 2 ≤ q) (ch : Chain D V r A B C E)
    (hA : A.card = q + 1) (hB : B.card + 1 ≤ r) :
    B.card + 1 = r ∧ (∀ b ∈ B, outN D V b ⊆ B ∪ C) ∧
      ∀ z ∈ A, B ⊆ outN D V z := by
  have LA := TopRowFat.loop_complete free (by omega) ch.AV hA ch.dAB hB ch.degA ch.kA
  obtain ⟨a0, ha0⟩ : A.Nonempty := card_pos.mp (by omega)
  refine ⟨(LA a0 ha0).2.2, ?_, fun z hz => (LA z hz).2.1⟩
  intro b hb w hw
  rcases mem_union.mp (ch.kB b hb hw) with h | h
  · rcases mem_union.mp h with h | h
    · exact absurd (mem_outN.mp hw).2 (fun ba => digonfree free hq (ch.AV h) (ch.BV hb)
        (mem_outN.mp ((LA w h).2.1 hb)).2 ba)
    · exact mem_union_left _ h
  · exact mem_union_right _ h

theorem chain_n4a (free : QFree D V q) (hq : 1 ≤ q) (ch : Chain D V r A B C E) :
    n4a q r A.card B.card C.card = true := by
  unfold n4a
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.and_eq_true,
    decide_eq_true_eq]
  by_cases h : A.card = q + 1 ∧ B.card + 1 ≤ r ∧ 2 ≤ q
  · right
    obtain ⟨e1, kB', -⟩ := step_one free h.2.2 ch h.1 h.2.1
    refine ⟨e1, ?_⟩
    have := frag_ok (r := r) (Fs := ∅) (free.mono_set ch.BV) hq (empty_subset _) (by simp)
      (fun v hv => kept_deg (ch.degB v hv) (kB' v hv))
    rwa [card_empty] at this
  · exact Or.inl h

theorem chain_ab (free : QFree D V q) (hq : 1 ≤ q) (ch : Chain D V r A B C E) :
    fragOK q r (A.card + B.card) A.card (r - C.card) = true := by
  have FV : A ∪ B ⊆ V := union_subset ch.AV ch.BV
  have := frag_ok (r := r) (m := r - C.card) (Fs := A) (free.mono_set FV) hq subset_union_left
    (fun v hv => by rw [BankPrice.keep_out FV (ch.kA v hv), ch.degA v hv])
    (fun v hv => by
      rcases mem_union.mp hv with h | h
      · rw [BankPrice.keep_out FV (ch.kA v h), ch.degA v h]; omega
      · exact kept_deg (ch.degB v h) (ch.kB v h))
  rwa [card_union_of_disjoint ch.dAB] at this

theorem chain_adm2 (free : QFree D V q) (hq : 1 ≤ q) (ch : Chain D V r A B C E) :
    adm2 q r A.card B.card C.card = true := by
  unfold adm2
  simp only [Bool.and_eq_true]
  exact ⟨⟨chain_adm1 free hq ch, chain_ab free hq ch⟩, chain_n4a free hq ch⟩

theorem chain_abc (free : QFree D V q) (hq : 1 ≤ q) (ch : Chain D V r A B C E) :
    fragOK q r (A.card + B.card + C.card) (A.card + B.card) (r - E.card) = true := by
  have FV : A ∪ B ∪ C ⊆ V := union_subset (union_subset ch.AV ch.BV) ch.CV
  have dABC : Disjoint (A ∪ B) C := disjoint_union_left.mpr ⟨ch.dAC, ch.dBC⟩
  have full : ∀ v ∈ A ∪ B, (outN D (A ∪ B ∪ C) v).card = r := by
    intro v hv
    rcases mem_union.mp hv with h | h
    · rw [BankPrice.keep_out FV (fun w hw => mem_union_left _ (ch.kA v h hw)), ch.degA v h]
    · rw [BankPrice.keep_out FV (ch.kB v h), ch.degB v h]
  have := frag_ok (r := r) (m := r - E.card) (Fs := A ∪ B) (free.mono_set FV) hq subset_union_left full
    (fun v hv => by
      rcases mem_union.mp hv with h | h
      · rw [full v h]; omega
      · exact kept_deg (ch.degC v h) (ch.kC v h))
  rwa [card_union_of_disjoint dABC, card_union_of_disjoint ch.dAB] at this

theorem chain_n4b (free : QFree D V q) (hq : 1 ≤ q) (ch : Chain D V r A B C E) :
    n4b q r A.card B.card C.card E.card = true := by
  unfold n4b
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Bool.and_eq_true,
    decide_eq_true_eq]
  by_cases h : A.card = q + 1 ∧ B.card + 1 ≤ r ∧ B.card = q + 1 ∧ C.card + 1 ≤ r ∧ 3 ≤ q
  · right
    obtain ⟨hA, hB, hB', hC, hq3⟩ := h
    obtain ⟨-, kB', LA⟩ := step_one free (by omega) ch hA hB
    have LB := TopRowFat.loop_complete free (by omega) ch.BV hB' ch.dBC hC ch.degB kB'
    obtain ⟨b0, hb0⟩ : B.Nonempty := card_pos.mp (by omega)
    refine ⟨(LB b0 hb0).2.2, ?_⟩
    have noC : ∀ c ∈ C, ∀ w ∈ A ∪ B, ¬ D c w = true := by
      intro c hc w hw cw
      rcases mem_union.mp hw with wa | wb
      · have wb0 := (mem_outN.mp (LA w wa hb0)).2
        have b0c := (mem_outN.mp ((LB b0 hb0).2.1 hc)).2
        exact free w 3 (by norm_num) hq3
          (.step (ch.BV hb0) wb0 (.step (ch.CV hc) b0c (.step (ch.AV wa) cw (.refl w))))
      · exact digonfree free (by omega) (ch.BV wb) (ch.CV hc)
          (mem_outN.mp ((LB w wb).2.1 hc)).2 cw
    have kC' : ∀ c ∈ C, outN D V c ⊆ C ∪ E := fun c hc w hw => by
      rcases mem_union.mp (ch.kC c hc hw) with h | h
      · rcases mem_union.mp h with h | h
        · exact absurd (mem_outN.mp hw).2 (noC c hc w h)
        · exact mem_union_left _ h
      · exact mem_union_right _ h
    have := frag_ok (r := r) (Fs := ∅) (free.mono_set ch.CV) hq (empty_subset _) (by simp)
      (fun v hv => kept_deg (ch.degC v hv) (kC' v hv))
    rwa [card_empty] at this
  · exact Or.inl h

theorem chain_adm3 (free : QFree D V q) (hq : 1 ≤ q) (ch : Chain D V r A B C E) :
    adm3 q r A.card B.card C.card E.card = true := by
  unfold adm3
  simp only [Bool.and_eq_true]
  exact ⟨chain_abc free hq ch, chain_n4b free hq ch⟩

/-- **Part 1.** Every chain in a `q`-free digraph has admissible sizes. -/
theorem chain_admissible (free : QFree D V q) (hq : 1 ≤ q) (ch : Chain D V r A B C E) :
    admissible q r A.card B.card C.card E.card = true := by
  unfold admissible
  simp only [Bool.and_eq_true]
  exact ⟨chain_adm2 free hq ch, chain_adm3 free hq ch⟩

end chain

/-! ### Part 2: the price -/

/-- The cap `M = (α + β + γ) r`. -/
def cap (r α β γ : ℕ) : ℕ := (α + β + γ) * r

/-- Least `b` passing N1 on `A`. -/
def bFloor (q r a : ℕ) : ℕ := firstFrom (adm1 q r a) 0 (r + 1)

/-- The exterior floor: least `α b + β c + γ e` over admissible sizes (capped at `M`). -/
def extFloor (q r a α β γ : ℕ) : ℕ :=
  minFrom (fun b => minFrom (fun c =>
      if adm2 q r a b c then
        α * b + β * c + γ * firstFrom (adm3 q r a b c) 0 (cap r α β γ / γ + 1)
      else cap r α β γ) 0 (cap r α β γ / β + 1) (cap r α β γ))
    0 (cap r α β γ / α + 1) (cap r α β γ)

theorem b_floor_sound {q r a b : ℕ} (h : adm1 q r a b = true) : bFloor q r a ≤ b :=
  firstFrom_le (Nat.zero_le b) h

/-- **Soundness of the price** (`α, β ≥ 1`; out of the box `α b + β c > M`). -/
theorem ext_floor_sound {q r a b c e α β γ : ℕ} (hα : 1 ≤ α) (hβ : 1 ≤ β)
    (h2 : adm2 q r a b c = true) (h3 : adm3 q r a b c e = true) :
    extFloor q r a α β γ ≤ α * b + β * c + γ * e := by
  unfold extFloor
  by_cases hb : b < cap r α β γ / α + 1
  · by_cases hc : c < cap r α β γ / β + 1
    · refine (minFrom_le (k := b) (Nat.zero_le _) (by omega)).trans ?_
      refine (minFrom_le (k := c) (Nat.zero_le _) (by omega)).trans ?_
      simp only [h2, if_true]
      have f := firstFrom_le (n := cap r α β γ / γ + 1) (Nat.zero_le e) h3
      have := Nat.mul_le_mul_left γ f
      omega
    · refine minFrom_le_acc.trans ?_
      have l := Nat.lt_mul_div_succ (cap r α β γ) (show 0 < β by omega)
      have := Nat.mul_le_mul_left β (show cap r α β γ / β + 1 ≤ c by omega)
      omega
  · refine minFrom_le_acc.trans ?_
    have l := Nat.lt_mul_div_succ (cap r α β γ) (show 0 < α by omega)
    have := Nat.mul_le_mul_left α (show cap r α β γ / α + 1 ≤ b by omega)
    omega

theorem ext_floor_chain {r : ℕ} {A B C E : Finset ℕ} (free : QFree D V q) (hq : 1 ≤ q)
    (ch : Chain D V r A B C E) {α β γ : ℕ} (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    extFloor q r A.card α β γ ≤ α * B.card + β * C.card + γ * E.card :=
  ext_floor_sound hα hβ (chain_adm2 free hq ch) (chain_adm3 free hq ch)

theorem b_floor_chain {r : ℕ} {A B C E : Finset ℕ} (free : QFree D V q) (hq : 1 ≤ q)
    (ch : Chain D V r A B C E) : bFloor q r A.card ≤ B.card :=
  b_floor_sound (chain_adm1 free hq ch)

/-! ### Bank corollaries (generic in `q ≥ 4`, `r`, `|A|`) -/

section bank
variable {r : ℕ} {K A : Finset ℕ}

theorem bank_layers (free : QFree D V q) (hq : 4 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (bank : Bank D V K A) {x : ℕ} (hx : x ∈ K) :
    Chain D V r A (layer D V 2 x \ K) (layer D V 3 x \ K) (layer D V 4 x \ K) := by
  have ch := BankPrice.bank_chain free hq reg bank hx
  rwa [BankPrice.ext_one free (by omega) bank hx] at ch

theorem bank_price2 (free : QFree D V q) (hq : 4 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (bank : Bank D V K A) {x : ℕ} (hx : x ∈ K) :
    3 + A.card + bFloor q r A.card ≤ (ball D V x 2).card := by
  have f := b_floor_chain free (by omega) (bank_layers free hq reg bank hx)
  have b := BankPrice.bank_ball free bank hx (k := 2) (by omega)
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.reduceAdd] at b
  rw [BankPrice.ext_one free (by omega) bank hx] at b
  omega

theorem bank_price3 (free : QFree D V q) (hq : 4 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (bank : Bank D V K A) {x : ℕ} (hx : x ∈ K) :
    4 + A.card + extFloor q r A.card 1 1 0 ≤ (ball D V x 3).card := by
  have f := ext_floor_chain free (by omega) (bank_layers free hq reg bank hx) (α := 1) (β := 1)
    (γ := 0) le_rfl le_rfl
  have b := BankPrice.bank_ball free bank hx (k := 3) (by omega)
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.reduceAdd] at b
  rw [BankPrice.ext_one free (by omega) bank hx] at b
  omega

theorem bank_price4 (free : QFree D V q) (hq : 4 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (bank : Bank D V K A) {x : ℕ} (hx : x ∈ K) :
    5 + A.card + extFloor q r A.card 1 1 1 ≤ (ball D V x 4).card := by
  have f := ext_floor_chain free (by omega) (bank_layers free hq reg bank hx) (α := 1) (β := 1)
    (γ := 1) le_rfl le_rfl
  have b := BankPrice.bank_ball free bank hx (k := 4) (by omega)
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.reduceAdd] at b
  rw [BankPrice.ext_one free (by omega) bank hx] at b
  omega

/-- Mixed `(2, 3)`. -/
theorem bank_mixed23 (free : QFree D V q) (hq : 4 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (bank : Bank D V K A) {x : ℕ} (hx : x ∈ K) :
    7 + 2 * A.card + extFloor q r A.card 2 1 0 ≤ (ball D V x 2).card + (ball D V x 3).card := by
  have f := ext_floor_chain free (by omega) (bank_layers free hq reg bank hx) (α := 2) (β := 1)
    (γ := 0) (by norm_num) le_rfl
  have b2 := BankPrice.bank_ball free bank hx (k := 2) (by omega)
  have b3 := BankPrice.bank_ball free bank hx (k := 3) (by omega)
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.reduceAdd] at b2 b3
  rw [BankPrice.ext_one free (by omega) bank hx] at b2 b3
  omega

/-- Mixed `(3, 4)`. -/
theorem bank_mixed34 (free : QFree D V q) (hq : 4 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (bank : Bank D V K A) {x : ℕ} (hx : x ∈ K) :
    9 + 2 * A.card + extFloor q r A.card 2 2 1 ≤ (ball D V x 3).card + (ball D V x 4).card := by
  have f := ext_floor_chain free (by omega) (bank_layers free hq reg bank hx) (α := 2) (β := 2)
    (γ := 1) (by norm_num) (by norm_num)
  have b3 := BankPrice.bank_ball free bank hx (k := 3) (by omega)
  have b4 := BankPrice.bank_ball free bank hx (k := 4) (by omega)
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.reduceAdd] at b3 b4
  rw [BankPrice.ext_one free (by omega) bank hx] at b3 b4
  omega

/-- The middle radii used by the score: `(2,2)`, `(2,3)`, `(3,3)`, `(3,4)`, `(4,4)` for
`q = 4, 5, 6, 7, ≥ 8`. -/
def midI (q : ℕ) : ℕ := min 4 (q / 2)
def midJ (q : ℕ) : ℕ := min 4 (q - q / 2)

/-- The bank score: a lower bound on `|B_i(x)| + |B_j(x)|` at the middle radii. -/
def bankScore (q r a : ℕ) : ℕ :=
  if 8 ≤ q then 2 * (5 + a + extFloor q r a 1 1 1)
  else if q = 7 then 9 + 2 * a + extFloor q r a 2 2 1
  else if q = 6 then 2 * (4 + a + extFloor q r a 1 1 0)
  else if q = 5 then 7 + 2 * a + extFloor q r a 2 1 0
  else 2 * (3 + a + bFloor q r a)

theorem mid_le (q : ℕ) : midI q + midJ q ≤ q := by unfold midI midJ; omega

/-- **The bank score** (generic, `q ≥ 4`): every bank row `x` has
`bankScore q r |A| ≤ |B_{midI q}(x)| + |B_{midJ q}(x)|`, `midI q + midJ q ≤ q`; the
level of that score is `n + 1` (`ReachLedger`). -/
theorem bank_score (free : QFree D V q) (hq : 4 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (bank : Bank D V K A) {x : ℕ} (hx : x ∈ K) :
    bankScore q r A.card ≤ (ball D V x (midI q)).card + (ball D V x (midJ q)).card := by
  unfold bankScore midI midJ
  by_cases h8 : 8 ≤ q
  · rw [if_pos h8, show min 4 (q / 2) = 4 by omega, show min 4 (q - q / 2) = 4 by omega]
    have := bank_price4 free hq reg bank hx
    omega
  rw [if_neg h8]
  by_cases h7 : q = 7
  · subst h7
    rw [if_pos rfl]
    exact bank_mixed34 free hq reg bank hx
  rw [if_neg h7]
  by_cases h6 : q = 6
  · subst h6
    rw [if_pos rfl]
    have := bank_price3 free hq reg bank hx
    show _ ≤ (ball D V x 3).card + (ball D V x 3).card
    omega
  rw [if_neg h6]
  by_cases h5 : q = 5
  · subst h5
    rw [if_pos rfl]
    exact bank_mixed23 free hq reg bank hx
  rw [if_neg h5]
  have h4 : q = 4 := by omega
  subst h4
  have := bank_price2 free hq reg bank hx
  show _ ≤ (ball D V x 2).card + (ball D V x 2).card
  omega

end bank

/-! ### Regressions by kernel evaluation -/

set_option maxRecDepth 100000 in
set_option profiler true in
/-- `a1`. -/
theorem ext_a1 : extFloor 7 9 8 2 2 1 = 40 := by decide +kernel

set_option profiler true in
theorem b_b1 : bFloor 8 9 8 = 9 := by decide +kernel

set_option profiler true in
theorem ext_b1_bc : extFloor 8 9 8 1 1 0 = 17 := by decide +kernel

set_option profiler true in
/-- `b1`. -/
theorem ext_b1 : extFloor 8 9 8 1 1 1 = 25 := by decide +kernel

/-- `a2_bank` as an instance. -/
theorem a2_bank' {K A : Finset ℕ} (free : QFree D V 7) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (bank : Bank D V K A) (hA : A.card = 8) {x : ℕ} (hx : x ∈ K) :
    65 ≤ (ball D V x 3).card + (ball D V x 4).card := by
  have := bank_mixed34 free (by norm_num) reg bank hx
  rw [hA, ext_a1] at this
  omega

/-- `b1` as an instance. -/
theorem b1' {A B C E : Finset ℕ} (free : QFree D V 8) (ch : Chain D V 9 A B C E)
    (hA : A.card = 8) :
    9 ≤ B.card ∧ 17 ≤ B.card + C.card ∧ 25 ≤ B.card + C.card + E.card := by
  have h1 := b_floor_chain free (by norm_num) ch
  have h2 := ext_floor_chain free (by norm_num) ch (α := 1) (β := 1) (γ := 0) le_rfl le_rfl
  have h3 := ext_floor_chain free (by norm_num) ch (α := 1) (β := 1) (γ := 1) le_rfl le_rfl
  rw [hA, b_b1] at h1
  rw [hA, ext_b1_bc] at h2
  rw [hA, ext_b1] at h3
  omega

/-- `a1` as an instance. -/
theorem a1' {A B C E : Finset ℕ} (free : QFree D V 7) (ch : Chain D V 9 A B C E)
    (hA : A.card = 8) : 40 ≤ 2 * (B.card + C.card) + E.card := by
  have h := ext_floor_chain free (by norm_num) ch (α := 2) (β := 2) (γ := 1) (by norm_num)
    (by norm_num)
  rw [hA, ext_a1] at h
  omega

/-- `b1_bank` as an instance. -/
theorem b1_bank' {K A : Finset ℕ} (free : QFree D V 8) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (bank : Bank D V K A) (hA : A.card = 8) {x : ℕ} (hx : x ∈ K) :
    38 ≤ (ball D V x 4).card := by
  have := bank_price4 free (by norm_num) reg bank hx
  rw [hA, ext_b1] at this
  omega

/-! ### Part 3: the table (`a = r - 1`, `4 ≤ q ≤ 12`, `4 ≤ r ≤ min 12 (2q)`)
Rows `(q, r, exterior floor at the middle radii, bankScore, largest n with score > n + 1,
score - (q r + 1))`. -/

/-- The exterior term entering `bankScore`. -/
def bankExt (q r a : ℕ) : ℕ :=
  if 8 ≤ q then extFloor q r a 1 1 1
  else if q = 7 then extFloor q r a 2 2 1
  else if q = 6 then extFloor q r a 1 1 0
  else if q = 5 then extFloor q r a 2 1 0
  else bFloor q r a

set_option profiler true in
#eval (List.range 9).flatMap fun i => let q := i + 4
  (List.range (min 12 (2 * q) - 3)).map fun j => let r := j + 4
    let s := bankScore q r (r - 1)
    (q, r, bankExt q r (r - 1), s, s - 2, (s : ℤ) - (q * r + 1))

#print axioms frag_ok
#print axioms chain_admissible
#print axioms ext_floor_sound
#print axioms ext_floor_chain
#print axioms b_floor_chain
#print axioms bank_price2
#print axioms bank_price3
#print axioms bank_price4
#print axioms bank_mixed23
#print axioms bank_mixed34
#print axioms bank_score
#print axioms ext_a1
#print axioms ext_b1
#print axioms a1'
#print axioms b1'
#print axioms a2_bank'
#print axioms b1_bank'

end LeanCH.BR.BankPriceRow
