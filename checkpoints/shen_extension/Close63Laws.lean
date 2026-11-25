import checkpoints.shen_extension.Close62
import checkpoints.shen_extension.Close54

/-!
# Order 63 at degree nine, cutoff seven: the payment with slack and the local laws

## Part 0 (generic, no digraph)

* `payment_exact`: debtors `R` with deficits, classes by a key, each class paid by its pair
  credit and its payers at a rate, with a class slack: `bill + slack ≤ pairs + rate · |pay|`;
  every payer row charged at most its capacity minus a row slack; the pair credits are at most
  `G`; and the ledger `∑ cap + G ≤ ∑ deficit`. Then every class slack and every row slack is
  zero (the count is tight everywhere).

## Generic bank lemmas (`BankPrice.Bank`)

* `bank_ext`, `bank_ext_unique`: the exterior of a bank is `N⁺(k) \ K` for any bank row `k`, so it
  is determined by the bank.
* `bank_zRows`: a bank row lies in `Supplier54.zRows` of the exterior.
* `next_layer`: if the rows of layer `j` keep their heads in layers `j, j + 1`, then layer
  `j + 1` is `N⁺(L_j) \ L_j`.
* `no_bank_of_succ` (`|V| < (q + 1)²`): if the exterior of every bank of `q + 1` rows with an
  exterior of `q + 1` labels is again such a bank, there is no such bank (eight pairwise
  disjoint banks do not fit; two equal ones close a cyclic chain, `RowBanks.no_cyclic_chain`).
* `pair_next` (`q = 7`, `r = 9`, `Floors7Row.chain_next` without the third keep):
  `|A| = 8`, `9 ≤ |B| ≤ 10`, `A` keeps in `A ∪ B`, `B` in `A ∪ B ∪ C`: `8 ≤ |C|`.

## Root laws at `q = 7`, `r = 9`

* T-roots (`|B_3| = 26`): `t_bank` (the second layer is a bank with exterior the third),
  `t_zkeep` (the third layer keeps its heads in layers `3, 4`), `t8_bank` (with `|W| = 8` the
  third layer is a bank with exterior the fourth), `t_layers` (roots with the same second layer
  have the same third and fourth layers).
* Fat roots (not thin, `(|Y|, |Z|) = (9, 8)`): `fat_keep` (lower cutoff `6`), `fat_next`,
  `fat_l5` (`9 ≤ |W| ≤ 10 ⇒ 8 ≤ |L5|`), `fat_good` (at least six good rows of `aSet`, all in
  `zRows Z`, each with `|B_3| ≥ 12 + |W| + |L5|`), `fat_score` (`|W| ≥ 9`: good rows score
  `≥ 65`).
* H-roots (thin, `|B_3| = 27`, `|W| ≤ 9`): `h_frag` (budget on `Y ∪ Z ∪ W`), `h_floor`
  (`78 ≤ |B_4| + |B_5|`).
* `end63 : TopRow.End63 D V`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.Close63
open Finset BRq2 BRq3
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)
open Profile54 (reach)
open ThinSuppliers (Thin complete complete_subset)

/-! ### Part 0: payment with slack -/

/-- **Payment with slack** (no digraph). If every class is paid with its slack, every payer is
charged at most its capacity minus its row slack, and the capacities plus the pair credit do not
exceed the total deficit, then all slacks vanish. -/
theorem payment_exact {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {R P : Finset ι}
    (key : ι → κ) (dfc cap : ι → ℕ) (pairs rate slack : κ → ℕ) (rslack : ι → ℕ)
    (pay : κ → Finset ι) (G : ℕ)
    (hG : ∑ K ∈ R.image key, pairs K ≤ G)
    (hK : ∀ K ∈ R.image key,
      ∑ v ∈ R.filter (fun v => key v = K), dfc v + slack K ≤ pairs K + rate K * (pay K).card)
    (hP : ∀ K ∈ R.image key, pay K ⊆ P)
    (hcap : ∀ x ∈ P,
      ∑ K ∈ (R.image key).filter (fun K => x ∈ pay K), rate K + rslack x ≤ cap x)
    (tot : ∑ x ∈ P, cap x + G ≤ ∑ v ∈ R, dfc v) :
    (∀ K ∈ R.image key, slack K = 0) ∧ ∀ x ∈ P, rslack x = 0 := by
  classical
  set C := R.image key with hC
  have fib : ∑ K ∈ C, ∑ v ∈ R.filter (fun v => key v = K), dfc v = ∑ v ∈ R, dfc v :=
    sum_fiberwise_of_maps_to (fun v hv => mem_image_of_mem key hv) dfc
  have le1 : ∑ K ∈ C, (∑ v ∈ R.filter (fun v => key v = K), dfc v + slack K) ≤
      ∑ K ∈ C, (pairs K + rate K * (pay K).card) := sum_le_sum hK
  have swap : ∑ K ∈ C, rate K * (pay K).card =
      ∑ x ∈ P, ∑ K ∈ C.filter (fun K => x ∈ pay K), rate K := by
    have e1 : ∀ K ∈ C, rate K * (pay K).card = ∑ x ∈ P, if x ∈ pay K then rate K else 0 := by
      intro K hK'
      rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr (hP K hK'), sum_const,
        smul_eq_mul, mul_comm]
    rw [sum_congr rfl e1, sum_comm]
    refine sum_congr rfl (fun x _ => ?_)
    rw [sum_filter]
  have le2 : ∑ x ∈ P, (∑ K ∈ C.filter (fun K => x ∈ pay K), rate K + rslack x) ≤
      ∑ x ∈ P, cap x := sum_le_sum hcap
  rw [sum_add_distrib, sum_add_distrib] at le1
  rw [sum_add_distrib] at le2
  have s0 : ∑ K ∈ C, slack K = 0 := by omega
  have r0 : ∑ x ∈ P, rslack x = 0 := by omega
  rw [sum_eq_zero_iff] at s0 r0
  exact ⟨s0, r0⟩

/-! ### Generic bank lemmas -/

variable {D : CH.Digraph} {V : Finset ℕ} {q : ℕ}

/-- The exterior of a bank seen from one bank row: `A = N⁺(k) \ K`. -/
theorem bank_ext {K A : Finset ℕ} (bank : BankPrice.Bank D V K A) {k : ℕ} (hk : k ∈ K) :
    A = outN D V k \ K := by
  ext w
  constructor
  · intro hw
    exact mem_sdiff.mpr ⟨bank.full k hk hw, disjoint_right.mp bank.dis hw⟩
  · intro hw
    obtain ⟨h1, h2⟩ := mem_sdiff.mp hw
    exact (mem_union.mp (bank.keep k hk h1)).resolve_left h2

/-- A nonempty bank has one exterior. -/
theorem bank_ext_unique {K A A' : Finset ℕ} (b : BankPrice.Bank D V K A)
    (b' : BankPrice.Bank D V K A') (ne : K.Nonempty) : A = A' := by
  obtain ⟨k, hk⟩ := ne
  rw [bank_ext b hk, bank_ext b' hk]

/-- A bank row lies in `zRows` of the exterior. -/
theorem bank_zRows {K A : Finset ℕ} (bank : BankPrice.Bank D V K A) {x : ℕ} (hx : x ∈ K) :
    x ∈ Supplier54.zRows D V A := by
  have e : outN D V x \ A = outN D K x := by
    ext w
    simp only [mem_sdiff, mem_outN]
    constructor
    · rintro ⟨⟨wV, a⟩, wA⟩
      exact ⟨(mem_union.mp (bank.keep x hx (mem_outN.mpr ⟨wV, a⟩))).resolve_right wA, a⟩
    · rintro ⟨wK, a⟩
      exact ⟨⟨bank.KV wK, a⟩, disjoint_left.mp bank.dis wK⟩
  refine mem_filter.mpr ⟨bank.KV hx, bank.full x hx, ?_, ?_⟩
  · rw [e, bank.one x hx]
  · intro e' he'
    rw [e] at he'
    exact bank.full e' (mem_outN.mp he').1

/-- **Next layer.** If the rows of layer `j ≥ 1` keep their heads in layers `j` and `j + 1`, then
layer `j + 1` is the set of heads of layer `j` outside it. -/
theorem next_layer {u j : ℕ} (hu : u ∈ V) (hj : 1 ≤ j)
    (keep : ∀ z ∈ layer D V j u, outN D V z ⊆ layer D V j u ∪ layer D V (j + 1) u) :
    layer D V (j + 1) u = (layer D V j u).biUnion (outN D V) \ layer D V j u := by
  ext w
  constructor
  · intro hw
    obtain ⟨p, hp, pw⟩ := ShapeClimbRoot.parent_mem hu hj hw
    refine mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨p, hp, mem_outN.mpr ⟨layer_subset hw, pw⟩⟩, ?_⟩
    exact disjoint_right.mp (FragmentBudget.layer_disj (by omega)) hw
  · intro hw
    obtain ⟨h1, h2⟩ := mem_sdiff.mp hw
    obtain ⟨z, hz, zw⟩ := mem_biUnion.mp h1
    exact (mem_union.mp (keep z hz zw)).resolve_left h2

/-- **No bank chain** (generic, `2 ≤ q`, `|V| < (q + 1)²`). If the exterior of every bank of
`q + 1` rows with an exterior of `q + 1` labels is again such a bank, there is no such bank. -/
theorem no_bank_of_succ (free : QFree D V q) (hq : 2 ≤ q) (small : V.card < (q + 1) * (q + 1))
    (succ : ∀ K A, BankPrice.Bank D V K A → K.card = q + 1 → A.card = q + 1 →
      ∃ A', BankPrice.Bank D V A A' ∧ A'.card = q + 1)
    {K A : Finset ℕ} (b : BankPrice.Bank D V K A) (hK : K.card = q + 1) (hA : A.card = q + 1) :
    False := by
  classical
  have step : ∀ p : Finset ℕ × Finset ℕ,
      (BankPrice.Bank D V p.1 p.2 ∧ p.1.card = q + 1 ∧ p.2.card = q + 1) →
      ∃ A', BankPrice.Bank D V p.2 A' ∧ p.2.card = q + 1 ∧ A'.card = q + 1 := by
    rintro ⟨K0, A0⟩ ⟨b0, hK0, hA0⟩
    obtain ⟨A', b', hA'⟩ := succ K0 A0 b0 hK0 hA0
    exact ⟨A', b', hA0, hA'⟩
  choose! g hg using step
  obtain ⟨s, s0, sS⟩ : ∃ s : ℕ → Finset ℕ × Finset ℕ,
      s 0 = (K, A) ∧ ∀ n, s (n + 1) = ((s n).2, g (s n)) :=
    ⟨fun n => Nat.rec (motive := fun _ => Finset ℕ × Finset ℕ) (K, A)
      (fun _ p => (p.2, g p)) n, rfl, fun _ => rfl⟩
  have sP : ∀ n, BankPrice.Bank D V (s n).1 (s n).2 ∧ (s n).1.card = q + 1 ∧
      (s n).2.card = q + 1 := by
    intro n
    induction n with
    | zero => rw [s0]; exact ⟨b, hK, hA⟩
    | succ n ih => rw [sS n]; exact hg _ ih
  have link : ∀ t, BankPrice.Bank D V (s t).1 (s (t + 1)).1 := fun t => by
    rw [sS t]; exact (sP t).1
  have cK : ∀ t, (s t).1.card = q + 1 := fun t => (sP t).2.1
  have meet : ∀ t t', ¬ Disjoint (s t).1 (s t').1 → (s t).1 = (s t').1 := by
    intro t t' nd
    obtain ⟨x, hx, hx'⟩ := not_disjoint_iff.mp nd
    have B := link t
    have B' := link t'
    exact RowBanks.banks_meet free hq B.KV B'.KV (cK t) (cK t') B.one B'.one B.keep B'.keep
      B.full B'.full hx hx'
  have cyc : ∀ a c, a < c → c ≤ q → (s a).1 = (s c).1 → False := by
    intro a c hac hc e
    refine RowBanks.no_cyclic_chain (A := fun i => (s (a + i)).1) (m := c - a - 1) free
      (fun t _ => (link (a + t)).KV)
      (fun t _ => card_pos.mp (by show 0 < (s (a + t)).1.card; rw [cK]; omega))
      (fun t _ x hx y hy => (mem_outN.mp ((link (a + t)).full x hx hy)).2) ?_ (by omega)
    intro x hx y hy
    have hc' : a + (c - a - 1) + 1 = c := by omega
    have B := link (a + (c - a - 1))
    rw [hc', ← e] at B
    exact (mem_outN.mp (B.full x hx hy)).2
  have notall : ¬ (∀ t ≤ q, ∀ t' ≤ q, t ≠ t' → Disjoint (s t).1 (s t').1) := by
    intro h
    have := RowBanks.chain_card (V := V) (A := fun t => (s t).1) (m := q)
      (fun t _ => (link t).KV) (fun t _ => cK t) h
    omega
  push Not at notall
  obtain ⟨t, ht, t', ht', ne, nd⟩ := notall
  rcases lt_or_gt_of_ne ne with h | h
  · exact cyc t t' h ht' (meet t t' nd)
  · exact cyc t' t h ht (meet t' t (fun d => nd d.symm))

/-- **Pair step** (`q = 7`, `r = 9`). `|A| = 8`, `9 ≤ |B| ≤ 10`, rows of `A` keep their heads
in `A ∪ B`, rows of `B` in `A ∪ B ∪ C`: `8 ≤ |C|` (the budget on `A ∪ B`, `Floors7Row.ar_chain`). -/
theorem pair_next {A B C : Finset ℕ} (free : QFree D V 7) (AV : A ⊆ V) (BV : B ⊆ V)
    (dAB : Disjoint A B) (degA : ∀ v ∈ A, (outN D V v).card = 9)
    (degB : ∀ v ∈ B, (outN D V v).card = 9) (kA : ∀ v ∈ A, outN D V v ⊆ A ∪ B)
    (kB : ∀ v ∈ B, outN D V v ⊆ A ∪ B ∪ C) (hA : A.card = 8) (hB9 : 9 ≤ B.card)
    (hB10 : B.card ≤ 10) : 8 ≤ C.card := by
  by_contra hC
  have FV : A ∪ B ⊆ V := union_subset AV BV
  have Fc : (A ∪ B).card = 8 + B.card := by rw [card_union_of_disjoint dAB, hA]
  have fullA : ∀ v ∈ A, (outN D (A ∪ B) v).card = 9 := fun v hv => by
    rw [BankPrice.keep_out FV (kA v hv), degA v hv]
  have deg : ∀ v ∈ A ∪ B, 2 + (7 - C.card) ≤ (outN D (A ∪ B) v).card := by
    intro v hv
    rcases mem_union.mp hv with h | h
    · rw [fullA v h]; omega
    · have := FragmentBudget.keep_le (kB v h)
      rw [degB v h] at this
      omega
  have fb := FragmentBudget.fragment_budget (i := 3) (j := 4) (r := 9) (t := 7 - C.card)
    (Fs := A) (free.mono_set FV) deg subset_union_left fullA (by norm_num) (by rw [Fc]; omega)
    le_rfl (by norm_num) (by norm_num)
  rw [Fc, hA] at fb
  exact Floors7Row.ar_chain B.card C.card hB9 hB10 (by omega) fb

/-! ### Root laws at `q = 7`, `r = 9` -/

section laws
variable (free : QFree D V 7) (reg : ∀ v ∈ V, (outN D V v).card = 9)

include free reg in
/-- **B, T-root.** At a root with `|B_3| = 26` the second layer is a bank with exterior the
third layer. -/
theorem t_bank {u : ℕ} (hu : u ∈ V) (h26 : (ball D V u 3).card = 26) :
    BankPrice.Bank D V (layer D V 2 u) (layer D V 3 u) := by
  obtain ⟨th, z8⟩ := Floors7Row.b3_26 free reg hu h26
  have y8 : (layer D V 2 u).card = 8 := by unfold Thin at th; omega
  have ch := BankPrice.thin_chain free reg hu y8
  have dj : Disjoint (layer D V 2 u) (layer D V 3 u) := FragmentBudget.layer_disj (by norm_num)
  have L := TopRowFat.loop_complete (r := 9) free (by norm_num) layer_subset (by rw [y8]) dj
    (by rw [z8]) (fun z hz => reg z (layer_subset hz)) ch.kA
  exact { KV := layer_subset, dis := dj, one := fun k hk => (L k hk).1, keep := ch.kA,
          full := fun k hk => (L k hk).2.1 }

include free reg in
/-- **B, T-root.** The third layer keeps its heads in layers `3, 4` (no return into `{u} ∪ X`
by `thin_return`; none into `Y`, which is complete to `Z`). -/
theorem t_zkeep {u : ℕ} (hu : u ∈ V) (h26 : (ball D V u 3).card = 26) :
    ∀ z ∈ layer D V 3 u, outN D V z ⊆ layer D V 3 u ∪ layer D V 4 u := by
  obtain ⟨th, -⟩ := Floors7Row.b3_26 free reg hu h26
  have y8 : (layer D V 2 u).card = 8 := by unfold Thin at th; omega
  have B := t_bank free reg hu h26
  intro z hz w hw
  obtain ⟨i, h1, h2, h3⟩ := BankPrice.thin_heads free reg hu y8 (j := 3) (by norm_num)
    (by norm_num) hz hw
  interval_cases i
  · exfalso
    exact digonfree free (by norm_num) (layer_subset h3) (layer_subset hz)
      (mem_outN.mp (B.full w h3 hz)).2 (mem_outN.mp hw).2
  · exact mem_union_left _ h3
  · exact mem_union_right _ h3

include free reg in
/-- **C, the successor law.** A root with `|B_3| = 26` and `|W| = 8`: the third layer is a bank
with exterior the fourth layer. -/
theorem t8_bank {u : ℕ} (hu : u ∈ V) (h26 : (ball D V u 3).card = 26)
    (w8 : (layer D V 4 u).card = 8) : BankPrice.Bank D V (layer D V 3 u) (layer D V 4 u) := by
  obtain ⟨-, z8⟩ := Floors7Row.b3_26 free reg hu h26
  have keep := t_zkeep free reg hu h26
  have dj : Disjoint (layer D V 3 u) (layer D V 4 u) := FragmentBudget.layer_disj (by norm_num)
  have L := TopRowFat.loop_complete (r := 9) free (by norm_num) layer_subset (by rw [z8]) dj
    (by rw [w8]) (fun z hz => reg z (layer_subset hz)) keep
  exact { KV := layer_subset, dis := dj, one := fun k hk => (L k hk).1, keep := keep,
          full := fun k hk => (L k hk).2.1 }

include free reg in
/-- **F, T-classes.** Two roots with `|B_3| = 26` and the same second layer have the same third
and fourth layers. -/
theorem t_layers {u u' : ℕ} (hu : u ∈ V) (hu' : u' ∈ V) (h26 : (ball D V u 3).card = 26)
    (h26' : (ball D V u' 3).card = 26) (same : layer D V 2 u = layer D V 2 u') :
    layer D V 3 u = layer D V 3 u' ∧ layer D V 4 u = layer D V 4 u' := by
  obtain ⟨th, -⟩ := Floors7Row.b3_26 free reg hu h26
  have y8 : (layer D V 2 u).card = 8 := by unfold Thin at th; omega
  have B := t_bank free reg hu h26
  have B' := t_bank free reg hu' h26'
  rw [same] at B
  have e3 := bank_ext_unique B B' (card_pos.mp (by rw [← same, y8]; norm_num))
  have n := next_layer (D := D) hu (j := 3) (by norm_num) (t_zkeep free reg hu h26)
  have n' := next_layer (D := D) hu' (j := 3) (by norm_num) (t_zkeep free reg hu' h26')
  refine ⟨e3, ?_⟩
  change layer D V (3 + 1) u = layer D V (3 + 1) u'
  rw [n, n', e3]

include free reg in
/-- **Fat roots** (not thin, `(|Y|, |Z|) = (9, 8)`), by the lower cutoff `6`: rows of `Z` keep
their heads in `Z ∪ W`, rows of `W` in `Z ∪ W ∪ L5`, and `aSet` is nonempty. -/
theorem fat_keep {u : ℕ} (hu : u ∈ V) (hY : (layer D V 2 u).card = 9)
    (hZ : (layer D V 3 u).card = 8) :
    (∀ z ∈ layer D V 3 u, outN D V z ⊆ layer D V 3 u ∪ layer D V 4 u) ∧
    (∀ w ∈ layer D V 4 u, outN D V w ⊆ layer D V 3 u ∪ layer D V 4 u ∪ layer D V 5 u) ∧
    (SupplierFat54.aSet D V u).Nonempty := by
  have free6 : QFree D V 6 := free.mono_bound (by norm_num)
  have ne := SupplierFat54.a_nonempty (AncestorRow.lemma5_six free6 reg hu hY)
  exact ⟨fun z hz => SupplierFat54.z_cover free6 hu le_rfl reg hY hZ ne hz,
    fun w hw => SupplierFat54.w_cover free6 hu le_rfl reg hY hZ ne hw, ne⟩

include free reg in
/-- At a fat root the fourth layer is the set of heads of the third layer outside it. -/
theorem fat_next {u : ℕ} (hu : u ∈ V) (hY : (layer D V 2 u).card = 9)
    (hZ : (layer D V 3 u).card = 8) :
    layer D V 4 u = (layer D V 3 u).biUnion (outN D V) \ layer D V 3 u :=
  next_layer (D := D) hu (j := 3) (by norm_num) (fat_keep free reg hu hY hZ).1

include free reg in
/-- **D.** A fat root with `9 ≤ |W| ≤ 10` has `|L5| ≥ 8` (budget on `Z ∪ W`, `pair_next`). -/
theorem fat_l5 {u : ℕ} (hu : u ∈ V) (hY : (layer D V 2 u).card = 9)
    (hZ : (layer D V 3 u).card = 8) (hW9 : 9 ≤ (layer D V 4 u).card)
    (hW10 : (layer D V 4 u).card ≤ 10) : 8 ≤ (layer D V 5 u).card := by
  obtain ⟨kz, kw, -⟩ := fat_keep free reg hu hY hZ
  exact pair_next free layer_subset layer_subset (FragmentBudget.layer_disj (by norm_num))
    (fun v hv => reg v (layer_subset hv)) (fun v hv => reg v (layer_subset hv)) kz kw hZ hW9 hW10

/-- Good rows of `aSet` are labels of `V`. -/
theorem good_V {u s : ℕ} (hs : s ∈ OneHead.good D (SupplierFat54.aSet D V u)) : s ∈ V :=
  SupplierFat54.aSet_V (ThinSuppliers.lone_subset (OneHead.good_subset hs))

include free reg in
/-- **D.** A fat root has at least six good rows of `aSet` (`OneHead.good_count` at `q = 7`,
`|aSet| ≤ 9`); they lie in `zRows Z`, and each has `|B_3| ≥ 4 + 8 + |W| + |L5|`
(`SupplierFat54.complete_ball_A`). -/
theorem fat_good {u : ℕ} (hu : u ∈ V) (hY : (layer D V 2 u).card = 9)
    (hZ : (layer D V 3 u).card = 8) :
    6 ≤ (OneHead.good D (SupplierFat54.aSet D V u)).card ∧
    OneHead.good D (SupplierFat54.aSet D V u) ⊆ Supplier54.zRows D V (layer D V 3 u) ∧
    ∀ s ∈ OneHead.good D (SupplierFat54.aSet D V u),
      4 + 8 + (layer D V 4 u).card + (layer D V 5 u).card ≤ (ball D V s 3).card := by
  have free6 : QFree D V 6 := free.mono_bound (by norm_num)
  obtain ⟨-, -, ne⟩ := fat_keep free reg hu hY hZ
  have deg := SupplierFat54.a_deg free6 hu (by norm_num) reg hZ
  have le : (SupplierFat54.aSet D V u).card ≤ 9 := by
    have := SupplierFat54.oa_card (D := D) (V := V) (u := u)
    omega
  have gc := OneHead.good_count (free.mono_set SupplierFat54.aSet_V) (by norm_num) deg ne
    (by omega)
  refine ⟨by omega, fun s hs => ?_, fun s hs => ?_⟩
  · obtain ⟨full, rest, full'⟩ := SupplierFat54.good_supplier free6 hu (by norm_num) reg hZ hs
    refine mem_filter.mpr ⟨good_V hs, full, ?_, ?_⟩
    · rw [rest, card_singleton]
    · intro e he
      rw [rest, mem_singleton] at he
      rw [he]
      exact full'
  · obtain ⟨full, -, -⟩ := SupplierFat54.good_supplier free6 hu (by norm_num) reg hZ hs
    have sA := ThinSuppliers.lone_subset (OneHead.good_subset hs)
    have := SupplierFat54.complete_ball_A free6 hu (by norm_num) reg hZ sA full
    omega

include free reg in
/-- **D.** At a fat root with `9 ≤ |W| ≤ 10` every good row of `aSet` scores at least
`65 + (|W| - 9)`. -/
theorem fat_score {u : ℕ} (hu : u ∈ V) (hY : (layer D V 2 u).card = 9)
    (hZ : (layer D V 3 u).card = 8) (hW9 : 9 ≤ (layer D V 4 u).card)
    (hW10 : (layer D V 4 u).card ≤ 10) {s : ℕ}
    (hs : s ∈ OneHead.good D (SupplierFat54.aSet D V u)) :
    56 + (layer D V 4 u).card ≤ (ball D V s 3).card + (ball D V s 4).card := by
  have l5 := fat_l5 free reg hu hY hZ hW9 hW10
  have b3 := (fat_good free reg hu hY hZ).2.2 s hs
  have b4 := Floors7Row.four_of_29 free reg (good_V hs) (by omega)
  omega

include free reg in
/-- **E, the budget.** A thin root with `|B_3| = 27` and `|W| = 8 + t`, `t ≤ 1`, has
`|L5| + t ≥ 8`. Fragment `Y ∪ Z ∪ W` (`25 + t` labels, every row keeps `2 + t`); floors on
`reach 3 + reach 4`: `34` on `Y` (the global `2`-ball, `≥ 18`, lies in the fragment), `26 + 2t`
on the full rows of `Z`, `14 + 2t` on `W`: `272 + 9 (26 + 2t) + (8 + t)(14 + 2t)` exceeds
`(25 + t)(24 + t)` (`618 > 600`, `668 > 650`). -/
theorem h_frag {u t : ℕ} (hu : u ∈ V) (th : Thin D V 9 u) (h27 : (ball D V u 3).card = 27)
    (ht : t ≤ 1) (hw : (layer D V 4 u).card = 8 + t) (hl : (layer D V 5 u).card + t ≤ 7) :
    False := by
  classical
  have L := Floors7Row.balls9 free reg hu
  have y8 : (layer D V 2 u).card = 8 := by unfold Thin at th; omega
  have z9 : (layer D V 3 u).card = 9 := by omega
  have ch := BankPrice.thin_chain free reg hu y8
  have d23 : Disjoint (layer D V 2 u) (layer D V 3 u) := FragmentBudget.layer_disj (by norm_num)
  have d24 : Disjoint (layer D V 2 u) (layer D V 4 u) := FragmentBudget.layer_disj (by norm_num)
  have d34 : Disjoint (layer D V 3 u) (layer D V 4 u) := FragmentBudget.layer_disj (by norm_num)
  have d234 : Disjoint (layer D V 2 u ∪ layer D V 3 u) (layer D V 4 u) :=
    disjoint_union_left.mpr ⟨d24, d34⟩
  have FV : layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u ⊆ V :=
    union_subset (union_subset layer_subset layer_subset) layer_subset
  have Fc : (layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u).card = 25 + t := by
    rw [card_union_of_disjoint d234, card_union_of_disjoint d23]
    omega
  have fr : QFree D (layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u) 7 := free.mono_set FV
  have fullY : ∀ v ∈ layer D V 2 u,
      (outN D (layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u) v).card = 9 := fun v hv => by
    rw [BankPrice.keep_out FV (fun w hw => mem_union_left _ (ch.kA v hv hw)),
      reg v (layer_subset hv)]
  have fullZ : ∀ v ∈ layer D V 3 u,
      (outN D (layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u) v).card = 9 := fun v hv => by
    rw [BankPrice.keep_out FV (ch.kB v hv), reg v (layer_subset hv)]
  have deg : ∀ v ∈ layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u,
      2 + t ≤ (outN D (layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u) v).card := by
    intro v hv
    rcases mem_union.mp hv with h | h
    · rcases mem_union.mp h with h | h
      · rw [fullY v h]; omega
      · rw [fullZ v h]; omega
    · have := FragmentBudget.keep_le (ch.kC v h)
      rw [reg v (layer_subset h)] at this
      omega
  -- floors
  have fY : ∀ y ∈ layer D V 2 u,
      34 ≤ reach D (layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u) 3 y +
        reach D (layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u) 4 y := by
    intro y hy
    have yV : y ∈ V := layer_subset hy
    have yF : y ∈ layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u :=
      mem_union_left _ (mem_union_left _ hy)
    have b2 : ball D V y 2 ⊆ layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u := by
      intro w hw
      have wV : w ∈ V := ball_subset hw
      by_cases w1 : w ∈ ball D V y 1
      · rcases (mem_ball_one yV).mp w1 with rfl | ho
        · exact yF
        · exact mem_union_left _ (ch.kA _ hy ho)
      · obtain ⟨p, hp, pw⟩ := ball_succ_pred (k := 1) yV hw w1
        rcases (mem_ball_one yV).mp hp with rfl | ho
        · exact mem_union_left _ (ch.kA _ hy (mem_outN.mpr ⟨wV, pw⟩))
        · rcases mem_union.mp (ch.kA y hy ho) with p2 | p3
          · exact mem_union_left _ (ch.kA p p2 (mem_outN.mpr ⟨wV, pw⟩))
          · exact ch.kB p p3 (mem_outN.mpr ⟨wV, pw⟩)
    have lf := card_le_card (Floors7Row.lift (A := layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u)
      yV 2 b2)
    have f2 := (Floors7Row.f2_floor free reg yV).1
    have e2 := Profile54.card_ball_erase (D := D)
      (W := layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u) (k := 2) yF
    have m3 := FragmentBudget.reach_mono (D := D)
      (F := layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u) (x := y) (show 2 ≤ 3 by norm_num)
    have m4 := FragmentBudget.reach_mono (D := D)
      (F := layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u) (x := y) (show 2 ≤ 4 by norm_num)
    unfold reach at m3 m4 ⊢
    omega
  have fZ : ∀ z ∈ layer D V 3 u,
      26 + 2 * t ≤ reach D (layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u) 3 z +
        reach D (layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u) 4 z := by
    intro z hz
    have zF : z ∈ layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u :=
      mem_union_left _ (mem_union_right _ hz)
    have a := FragmentBudget.full_floor fr (i := 3) (t := t) (r := 9) le_rfl (by norm_num)
      (by norm_num) (by rw [Fc]; omega) deg zF (fullZ z hz)
    have b := FullRow.full_row fr (i := 4) (t := t) (r := 9) le_rfl (by norm_num)
      (by rw [Fc]; omega) deg zF (fullZ z hz)
    omega
  have fW : ∀ w ∈ layer D V 4 u,
      14 + 2 * t ≤ reach D (layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u) 3 w +
        reach D (layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u) 4 w := by
    intro w hw
    have wF : w ∈ layer D V 2 u ∪ layer D V 3 u ∪ layer D V 4 u := mem_union_right _ hw
    have a := FragmentBudget.ordinary_floor fr (i := 3) (t := t) (by norm_num) (by norm_num)
      deg wF
    have b := FragmentBudget.ordinary_floor fr (i := 4) (t := t) (by norm_num) (by norm_num)
      deg wF
    omega
  -- the budget
  have mb := FragmentBudget.mixed_budget fr (i := 3) (j := 4) (by norm_num)
  rw [sum_union d234, sum_union d23, Fc] at mb
  have lY := Floors7Row.low3 fY
  have lZ := Floors7Row.low3 fZ
  have lW := Floors7Row.low3 fW
  rw [y8] at lY
  rw [z9] at lZ
  rw [hw] at lW
  interval_cases t <;> omega

include free reg in
/-- **E.** A thin root with `|B_3| = 27` and `|W| ≤ 9` has `78 ≤ |B_4| + |B_5|`. -/
theorem h_floor {u : ℕ} (hu : u ∈ V) (th : Thin D V 9 u) (h27 : (ball D V u 3).card = 27)
    (hw : (layer D V 4 u).card ≤ 9) : 78 ≤ (ball D V u 4).card + (ball D V u 5).card := by
  have L := Floors7Row.balls9 free reg hu
  have w8 := (Floors7Row.four_of_27 free reg hu h27).1
  by_contra hlt
  rcases (show (layer D V 4 u).card = 8 ∨ (layer D V 4 u).card = 9 by omega) with e | e
  · exact h_frag free reg hu th h27 (t := 0) (by norm_num) (by omega) (by omega)
  · exact h_frag free reg hu th h27 (t := 1) (by norm_num) (by omega) (by omega)

include free reg in
/-- **Part 3: the endgame law.** A row that is not thin, scores `64` and has `|B_4| ≥ 37` forces
a row scoring at least `65`: `|B_3| = 27`, layers `(9, 8, 10)`, and a good row of `aSet` has
`|B_3| ≥ 4 + 8 + 10 + 8 = 30`, so `|B_4| ≥ 36` (`four_of_29`). -/
theorem end63 : TopRow.End63 D V := by
  intro v hv nt S64 b37
  have L := Floors7Row.balls9 free reg hv
  have f3 := (Floors7Row.fat3_floor free reg hv nt).1
  have h27 : (ball D V v 3).card = 27 := by omega
  obtain ⟨hY, hZ⟩ := (Floors7Row.fat3_floor free reg hv nt).2 h27
  have w10 : (layer D V 4 v).card = 10 := by omega
  obtain ⟨g6, -, -⟩ := fat_good free reg hv hY hZ
  obtain ⟨s, hs⟩ : (OneHead.good D (SupplierFat54.aSet D V v)).Nonempty := card_pos.mp (by omega)
  have sc := fat_score free reg hv hY hZ (by omega) (by omega) hs
  exact ⟨s, good_V hs, by omega⟩

end laws

#print axioms payment_exact
#print axioms bank_ext
#print axioms bank_ext_unique
#print axioms bank_zRows
#print axioms next_layer
#print axioms no_bank_of_succ
#print axioms pair_next
#print axioms t_bank
#print axioms t_zkeep
#print axioms t8_bank
#print axioms t_layers
#print axioms fat_keep
#print axioms fat_next
#print axioms fat_l5
#print axioms fat_good
#print axioms fat_score
#print axioms h_frag
#print axioms h_floor
#print axioms end63

end LeanCH.BR.Close63
