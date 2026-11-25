import checkpoints.shen_extension.EqualLayers
import checkpoints.shen_extension.Supplier54
import checkpoints.shen_extension.Profile54
import checkpoints.shen_extension.TopRowFat
import checkpoints.shen_extension.TopRowFloors6

/-!
# Order 54 at degree nine, cutoff six: the closing count

Generic part (no fixed numbers):

* `payment` (no digraph): debtors with deficits, split into classes by a key; each class is
  paid by its pair credit and by a set of payers at a rate, strictly more than its deficit; the
  payers' capacities cover their rates. Then the capacities plus the pair credit exceed the
  total deficit.
* `ledger_split` (`QFree D V q`, `i + i' ≤ q`, level `L = |V| + 1`, score
  `s v = |B_i v| + |B_{i'} v|`): `∑ (s - L)⁺ + ∑ |gap| = ∑ (L - s)⁺`.
* `class_gap` (`QFree D V q`, `2j ≤ q + 2`, radii `i, i' ≤ q`): a set `K = K₁ ∪ K₂` of roots
  sharing `layer j`, with `|B_{j-1}| = s` on `K₁` and `s + 1` on `K₂`, has at least
  `|K| (|K| - 1) - 2 |K₂|` ordered gap incidences inside `K`.
* `class_bill`: with deficits `δ₁` on `K₁`, `δ₂` on `K₂`, gap worth `g`, and
  `δ₁ a + (δ₂ + 2g) c ≤ d (a + c)`, `d m ≤ B + g m (m - 1)` for all `m`: the class deficit is
  at most `B + g · (incidences)`. Instances `bill_mixed` (`(6, 2, 2)`, `d = 6`, `B = 8`) and
  `bill_pure` (`δ = 2`, `g = 2`, `B = 2`).

Instance `(n, q, r) = (54, 6, 9)`, radii `(3, 3)`, quarter units (deficit `110 - 4 b`,
capacity `4 b - 110`, `b = |B_3|`):

* `Laws54`: S5 (`(8, 8)` roots have five `zSet` rows), S2 (`(9, 8)` roots that are not thin
  have two), L9 (complete heads of thin `b = 27` roots have `b ≥ 29`).
* `no54_of_laws`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.Close54
open Finset BRq2 BRq3
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)
open ReachLedger (gap mem_gap)
open ThinSuppliers (Thin TightR complete complete_subset)
open Supplier54 (zSet)

/-! ### Part 1: the payment lemma -/

/-- **Payment lemma.** No digraph. -/
theorem payment {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {R P : Finset ι} (key : ι → κ)
    (dfc cap : ι → ℕ) (pairs rate : κ → ℕ) (pay : κ → Finset ι) (G : ℕ)
    (hG : ∑ K ∈ R.image key, pairs K ≤ G)
    (hK : ∀ K ∈ R.image key,
      ∑ v ∈ R.filter (fun v => key v = K), dfc v < pairs K + rate K * (pay K).card)
    (hP : ∀ K ∈ R.image key, pay K ⊆ P)
    (hcap : ∀ x ∈ P, ∑ K ∈ (R.image key).filter (fun K => x ∈ pay K), rate K ≤ cap x)
    (hR : R.Nonempty)
    (tot : ∑ x ∈ P, cap x + G ≤ ∑ v ∈ R, dfc v) : False := by
  classical
  set C := R.image key with hC
  have fib : ∑ K ∈ C, ∑ v ∈ R.filter (fun v => key v = K), dfc v = ∑ v ∈ R, dfc v :=
    sum_fiberwise_of_maps_to (fun v hv => mem_image_of_mem key hv) dfc
  have Cne : C.Nonempty := hR.image key
  have lt : ∑ K ∈ C, ∑ v ∈ R.filter (fun v => key v = K), dfc v <
      ∑ K ∈ C, (pairs K + rate K * (pay K).card) := sum_lt_sum_of_nonempty Cne hK
  have swap : ∑ K ∈ C, rate K * (pay K).card =
      ∑ x ∈ P, ∑ K ∈ C.filter (fun K => x ∈ pay K), rate K := by
    have e1 : ∀ K ∈ C, rate K * (pay K).card = ∑ x ∈ P, if x ∈ pay K then rate K else 0 := by
      intro K hK'
      rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr (hP K hK'), sum_const,
        smul_eq_mul, mul_comm]
    rw [sum_congr rfl e1, sum_comm]
    refine sum_congr rfl (fun x _ => ?_)
    rw [sum_filter]
  have capS : ∑ x ∈ P, ∑ K ∈ C.filter (fun K => x ∈ pay K), rate K ≤ ∑ x ∈ P, cap x :=
    sum_le_sum hcap
  rw [sum_add_distrib] at lt
  omega

/-! ### Generic: the ledger in surplus/deficit form -/

variable {D : CH.Digraph} {V : Finset ℕ} {q : ℕ}

/-- **Ledger, split.** `∑ (s - L)⁺ + ∑ |gap| = ∑ (L - s)⁺`, `s v = |B_i v| + |B_{i'} v|`,
`L = |V| + 1`. -/
theorem ledger_split {i i' : ℕ} (free : QFree D V q) (hii : i + i' ≤ q) :
    ∑ v ∈ V, ((ball D V v i).card + (ball D V v i').card - (V.card + 1)) +
        ∑ v ∈ V, (gap D V i i' v).card =
      ∑ v ∈ V, ((V.card + 1) - ((ball D V v i).card + (ball D V v i').card)) := by
  have L := ReachLedger.ledger (D := D) (V := V) free hii
  have per := sum_congr rfl (fun v (_ : v ∈ V) =>
    (show ((ball D V v i).card + (ball D V v i').card - (V.card + 1)) + (V.card + 1) =
      ((ball D V v i).card + (ball D V v i').card) +
        ((V.card + 1) - ((ball D V v i).card + (ball D V v i').card)) by omega))
  simp only [sum_add_distrib, sum_const, smul_eq_mul] at per
  have e : V.card * (V.card + 1) = V.card * V.card + V.card := by ring
  omega

/-! ### Generic: gap incidences inside a class of equal layers -/

/-- **Class gap count.** -/
theorem class_gap (free : QFree D V q) {j i i' s : ℕ} (hj : 1 ≤ j) (hjq : 2 * j ≤ q + 2)
    (hi : i ≤ q) (hi' : i' ≤ q) {Λ K₁ K₂ : Finset ℕ} (K1V : K₁ ⊆ V) (K2V : K₂ ⊆ V)
    (dis : Disjoint K₁ K₂)
    (lay1 : ∀ u ∈ K₁, layer D V j u = Λ) (lay2 : ∀ u ∈ K₂, layer D V j u = Λ)
    (c1 : ∀ u ∈ K₁, (ball D V u (j - 1)).card = s)
    (c2 : ∀ u ∈ K₂, (ball D V u (j - 1)).card = s + 1) :
    (K₁ ∪ K₂).card * ((K₁ ∪ K₂).card - 1) ≤
      ∑ w ∈ K₁ ∪ K₂, ((K₁ ∪ K₂).filter (fun x => x ∈ gap D V i i' w)).card + 2 * K₂.card := by
  classical
  set K := K₁ ∪ K₂ with hK
  -- same size: a gap
  have same : ∀ w x, (w ∈ K₁ ∧ x ∈ K₁ ∨ w ∈ K₂ ∧ x ∈ K₂) → w ≠ x → x ∈ gap D V i i' w := by
    intro w x h ne
    rcases h with ⟨hw, hx⟩ | ⟨hw, hx⟩
    · exact EqualLayers.equal_layer_gap free (K1V hw) (K1V hx) ne hj hjq
        ((lay1 w hw).trans (lay1 x hx).symm) ((c1 w hw).trans (c1 x hx).symm) hi hi'
    · exact EqualLayers.equal_layer_gap free (K2V hw) (K2V hx) ne hj hjq
        ((lay2 w hw).trans (lay2 x hx).symm) ((c2 w hw).trans (c2 x hx).symm) hi hi'
  -- small does not reach big
  have noUp : ∀ x ∈ K₁, ∀ u ∈ K₂, u ∉ ball D V x q := by
    intro x hx u hu reach
    have ne : x ≠ u := fun e => disjoint_left.mp dis hx (e ▸ hu)
    have sub := card_le_card (EqualLayers.equal_layer_ball free (K1V hx) (K2V hu) ne hj hjq
      ((lay1 x hx).trans (lay2 u hu).symm) reach)
    rw [card_erase_of_mem (self_mem_ball (K1V hx)), c1 x hx, c2 u hu] at sub
    omega
  -- big reaches at most one small
  have oneDown : ∀ u ∈ K₂, ∀ {k : ℕ}, k ≤ q → (K₁.filter (fun x => x ∈ ball D V u k)).card ≤ 1 := by
    intro u hu k hk
    refine card_le_one.mpr (fun x hx x' hx' => ?_)
    by_contra ne
    obtain ⟨xK, xb⟩ := mem_filter.mp hx
    obtain ⟨xK', xb'⟩ := mem_filter.mp hx'
    have nu : u ≠ x := fun e => disjoint_left.mp dis xK (e ▸ hu)
    have nu' : u ≠ x' := fun e => disjoint_left.mp dis xK' (e ▸ hu)
    exact EqualLayers.equal_layer_pair free (K2V hu) (K1V xK) (K1V xK') nu nu' ne hj hjq
      ((lay2 u hu).trans (lay1 x xK).symm) ((lay2 u hu).trans (lay1 x' xK').symm)
      (ball_mono_radius hk xb) (ball_mono_radius hk xb')
      (by rw [c1 x xK, c2 u hu]) (by rw [c1 x' xK', c2 u hu])
  -- the misses of a row
  set bad := fun w => (K.erase w).filter (fun x => x ∉ gap D V i i' w) with hbad
  have per : ∀ w ∈ K, K.card - 1 ≤ (K.filter (fun x => x ∈ gap D V i i' w)).card + (bad w).card := by
    intro w hw
    have split := card_filter_add_card_filter_not (s := K.erase w) (fun x => x ∈ gap D V i i' w)
    have sub := card_le_card (filter_subset_filter (fun x => x ∈ gap D V i i' w)
      (erase_subset w K))
    rw [card_erase_of_mem hw] at split
    simp only [hbad]
    omega
  have bad1 : ∀ w ∈ K₁, bad w ⊆ K₂.filter (fun u => w ∈ ball D V u i') := by
    intro w hw x hx
    obtain ⟨hx1, hng⟩ := mem_filter.mp hx
    obtain ⟨ne, xK⟩ := mem_erase.mp hx1
    rcases mem_union.mp xK with x1 | x2
    · exact absurd (same w x (Or.inl ⟨hw, x1⟩) (Ne.symm ne)) hng
    · refine mem_filter.mpr ⟨x2, ?_⟩
      by_contra nb
      refine hng (mem_gap.mpr ⟨K2V x2, fun h => noUp w hw x x2 (ball_mono_radius hi h), nb⟩)
  have bad2 : ∀ w ∈ K₂, bad w ⊆ K₁.filter (fun x => x ∈ ball D V w i) := by
    intro w hw x hx
    obtain ⟨hx1, hng⟩ := mem_filter.mp hx
    obtain ⟨ne, xK⟩ := mem_erase.mp hx1
    rcases mem_union.mp xK with x1 | x2
    · refine mem_filter.mpr ⟨x1, ?_⟩
      by_contra nb
      exact hng (mem_gap.mpr ⟨K1V x1, nb, fun h => noUp x x1 w hw (ball_mono_radius hi' h)⟩)
    · exact absurd (same w x (Or.inr ⟨hw, x2⟩) (Ne.symm ne)) hng
  have dc : ∑ w ∈ K₁, (K₂.filter (fun u => w ∈ ball D V u i')).card =
      ∑ u ∈ K₂, (K₁.filter (fun w => w ∈ ball D V u i')).card := by
    simp only [card_filter]
    rw [sum_comm]
  have s1 : ∑ w ∈ K₁, (bad w).card ≤ K₂.card := by
    calc ∑ w ∈ K₁, (bad w).card ≤ ∑ w ∈ K₁, (K₂.filter (fun u => w ∈ ball D V u i')).card :=
          sum_le_sum (fun w hw => card_le_card (bad1 w hw))
      _ = ∑ u ∈ K₂, (K₁.filter (fun w => w ∈ ball D V u i')).card := dc
      _ ≤ ∑ _u ∈ K₂, 1 := sum_le_sum (fun u hu => oneDown u hu hi')
      _ = K₂.card := by simp
  have s2 : ∑ w ∈ K₂, (bad w).card ≤ K₂.card := by
    calc ∑ w ∈ K₂, (bad w).card ≤ ∑ w ∈ K₂, (K₁.filter (fun x => x ∈ ball D V w i)).card :=
          sum_le_sum (fun w hw => card_le_card (bad2 w hw))
      _ ≤ ∑ _u ∈ K₂, 1 := sum_le_sum (fun u hu => oneDown u hu hi)
      _ = K₂.card := by simp
  have tot := sum_le_sum per
  rw [sum_add_distrib, sum_const, smul_eq_mul] at tot
  have bs : ∑ w ∈ K, (bad w).card = ∑ w ∈ K₁, (bad w).card + ∑ w ∈ K₂, (bad w).card :=
    sum_union dis
  omega

/-! ### Generic: the class bill -/

/-- **Class bill.** -/
theorem class_bill {a c inc δ₁ δ₂ g d B : ℕ} (hinc : (a + c) * (a + c - 1) ≤ inc + 2 * c)
    (hd : δ₁ * a + (δ₂ + 2 * g) * c ≤ d * (a + c))
    (hB : ∀ m, d * m ≤ B + g * (m * (m - 1))) :
    δ₁ * a + δ₂ * c ≤ B + g * inc := by
  have h1 := hB (a + c)
  have h2 := Nat.mul_le_mul_left g hinc
  have e1 : (δ₂ + 2 * g) * c = δ₂ * c + 2 * (g * c) := by ring
  have e2 : g * (inc + 2 * c) = g * inc + 2 * (g * c) := by ring
  rw [e1] at hd
  rw [e2] at h2
  omega

/-- `6 m ≤ 8 + 2 m (m - 1)`. -/
theorem six_le (m : ℕ) : 6 * m ≤ 8 + 2 * (m * (m - 1)) := by
  rcases Nat.lt_or_ge m 4 with h | h
  · interval_cases m <;> simp
  · have : 3 * m ≤ m * (m - 1) := by
      calc 3 * m = m * 3 := by ring
        _ ≤ m * (m - 1) := Nat.mul_le_mul_left m (by omega)
    omega

/-- **Bill, mixed class** (`δ₁ = 6`, `δ₂ = 2`, `g = 2`): at most `8`. -/
theorem bill_mixed {a c inc : ℕ} (hinc : (a + c) * (a + c - 1) ≤ inc + 2 * c) :
    6 * a + 2 * c ≤ 8 + 2 * inc :=
  class_bill (d := 6) hinc (by ring_nf; omega) six_le

/-- **Bill, pure class** (`δ = 2`, `g = 2`): at most `2`. -/
theorem bill_pure {m inc : ℕ} (hinc : m * (m - 1) ≤ inc) : 2 * m ≤ 2 + 2 * inc := by
  have := class_bill (a := m) (c := 0) (δ₂ := 0) (d := 2) (B := 2) (g := 2) (δ₁ := 2) (inc := inc)
    (by simpa using hinc) (by simp) (fun m => by have := EqualLayers.two_le m; omega)
  simpa using this

/-! ### Instance `(54, 6, 9)` -/

/-- The local supplier laws at `q = 6`, `r = 9`. -/
structure Laws54 (D : CH.Digraph) (V : Finset ℕ) : Prop where
  /-- S5: a root with layers `(8, 8)` has at least five `zSet` rows for its third layer. -/
  s5 : ∀ u ∈ V, TightR D V 9 u → 5 ≤ (zSet D V (layer D V 3 u)).card
  /-- S2: a root that is not thin, with layers `(9, 8)`, has at least two. -/
  s2 : ∀ u ∈ V, ¬ Thin D V 9 u → (layer D V 2 u).card = 9 → (layer D V 3 u).card = 8 →
    2 ≤ (zSet D V (layer D V 3 u)).card
  /-- L9: complete heads of a thin root with `|B_3| = 27` have `|B_3| ≥ 29`. -/
  l9 : ∀ u ∈ V, Thin D V 9 u → (ball D V u 3).card = 27 → ∀ x ∈ complete D V u,
    29 ≤ (ball D V x 3).card

/-- Roots below the level: three types. -/
theorem root_type (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9) {v : ℕ}
    (hv : v ∈ V) (low : (ball D V v 3).card ≤ 27) :
    ((ball D V v 3).card = 26 ∧ (layer D V 2 v).card = 8 ∧ (layer D V 3 v).card = 8) ∨
    ((ball D V v 3).card = 27 ∧ (layer D V 2 v).card = 8 ∧ (layer D V 3 v).card = 9) ∨
    ((ball D V v 3).card = 27 ∧ (layer D V 2 v).card = 9 ∧ (layer D V 3 v).card = 8) := by
  have f := (TopRowFloors6.floors6 free reg).1 v hv
  have L := (ThinSuppliers.balls_by_layers free (by norm_num) reg hv).2.2
  have w2 := ThinSuppliers.second_wide free (by norm_num) reg hv (by norm_num)
  rcases (show (ball D V v 3).card = 26 ∨ (ball D V v 3).card = 27 by omega) with e | e
  · exact Or.inl ⟨e, Profile54.thin_26 free reg hv e⟩
  · by_cases h8 : (layer D V 2 v).card = 8
    · exact Or.inr (Or.inl ⟨e, h8, by omega⟩)
    · exact Or.inr (Or.inr ⟨e, Profile54.profile_cases free reg hv (by omega) e⟩)

/-- The class key: the third layer for roots with `|layer 3| = 8`, else the second layer. -/
noncomputable def key54 (D : CH.Digraph) (V : Finset ℕ) (v : ℕ) : Bool × Finset ℕ :=
  if (layer D V 3 v).card = 8 then (true, layer D V 3 v) else (false, layer D V 2 v)

theorem key_true {v : ℕ} {Z : Finset ℕ} (h : key54 D V v = (true, Z)) :
    (layer D V 3 v).card = 8 ∧ layer D V 3 v = Z := by
  unfold key54 at h
  split_ifs at h with c
  · exact ⟨c, (Prod.mk.inj h).2⟩
  · exact absurd (Prod.mk.inj h).1 (by decide)

theorem key_false {v : ℕ} {Y : Finset ℕ} (h : key54 D V v = (false, Y)) :
    (layer D V 3 v).card ≠ 8 ∧ layer D V 2 v = Y := by
  unfold key54 at h
  split_ifs at h with c
  · exact absurd (Prod.mk.inj h).1 (by decide)
  · exact ⟨c, (Prod.mk.inj h).2⟩

open Classical in
/-- A representative of a class. -/
noncomputable def pick {κ : Type*} (R : Finset ℕ) (key : ℕ → κ) (K : κ) : ℕ :=
  if h : ∃ v ∈ R, key v = K then h.choose else 0

theorem pick_spec {κ : Type*} [DecidableEq κ] {R : Finset ℕ} {key : ℕ → κ} {K : κ} (hK : K ∈ R.image key) :
    pick R key K ∈ R ∧ key (pick R key K) = K := by
  classical
  have h : ∃ v ∈ R, key v = K := by simpa using hK
  unfold pick
  rw [dif_pos h]
  exact h.choose_spec

/-- **Order 54 from the supplier laws.** -/
theorem no54_of_laws (free : QFree D V 6) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 54) (laws : Laws54 D V) : False := by
  classical
  set R := V.filter (fun v => ¬ 28 ≤ (ball D V v 3).card) with hR
  set P := V.filter (fun v => 28 ≤ (ball D V v 3).card) with hP
  set key := key54 D V with hkey
  set cls := fun K => R.filter (fun v => key v = K) with hcls
  set rep := pick R key with hrep
  have RV : R ⊆ V := filter_subset _ _
  have PV : P ⊆ V := filter_subset _ _
  -- data of the roots below the level
  have typ : ∀ v ∈ R, _ := fun v hv =>
    root_type free reg (RV hv) (by have := (mem_filter.mp hv).2; omega)
  have b2 : ∀ v ∈ V, (ball D V v 2).card = (layer D V 2 v).card + 10 := fun v hv => by
    have := (ThinSuppliers.balls_by_layers free (by norm_num) reg hv).2.1; omega
  have b1 : ∀ v ∈ V, (ball D V v 1).card = 10 := fun v hv =>
    (ThinSuppliers.balls_by_layers free (by norm_num) reg hv).1
  -- the ledger in quarter units
  have led := ledger_split (D := D) (V := V) (i := 3) (i' := 3) free (by norm_num)
  rw [n] at led
  have splitS := sum_filter_add_sum_filter_not V (fun v => 28 ≤ (ball D V v 3).card)
    (fun v => (ball D V v 3).card + (ball D V v 3).card - (54 + 1))
  have splitD := sum_filter_add_sum_filter_not V (fun v => 28 ≤ (ball D V v 3).card)
    (fun v => (54 + 1) - ((ball D V v 3).card + (ball D V v 3).card))
  rw [← hP, ← hR] at splitS splitD
  have zS : ∑ v ∈ R, ((ball D V v 3).card + (ball D V v 3).card - (54 + 1)) = 0 :=
    sum_eq_zero (fun v hv => by have := (mem_filter.mp hv).2; omega)
  have zD : ∑ v ∈ P, ((54 + 1) - ((ball D V v 3).card + (ball D V v 3).card)) = 0 :=
    sum_eq_zero (fun v hv => by have := (mem_filter.mp hv).2; omega)
  have capE : ∑ x ∈ P, (4 * (ball D V x 3).card - 110) =
      2 * ∑ v ∈ P, ((ball D V v 3).card + (ball D V v 3).card - (54 + 1)) := by
    rw [mul_sum]; exact sum_congr rfl (fun v _ => by omega)
  have dfcE : ∑ v ∈ R, (110 - 4 * (ball D V v 3).card) =
      2 * ∑ v ∈ R, ((54 + 1) - ((ball D V v 3).card + (ball D V v 3).card)) := by
    rw [mul_sum]; exact sum_congr rfl (fun v _ => by omega)
  have tot : ∑ x ∈ P, (4 * (ball D V x 3).card - 110) + 2 * ∑ v ∈ V, (gap D V 3 3 v).card =
      ∑ v ∈ R, (110 - 4 * (ball D V v 3).card) := by omega
  -- a debtor exists
  have Rne : R.Nonempty := by
    by_contra e
    rw [not_nonempty_iff_eq_empty] at e
    obtain ⟨v, hv⟩ : V.Nonempty := card_pos.mp (by omega)
    have vP : v ∈ P := by
      by_contra nP
      have : v ∈ R := mem_filter.mpr ⟨hv, fun h => nP (mem_filter.mpr ⟨hv, h⟩)⟩
      rw [e] at this; simp at this
    have one := single_le_sum (f := fun x => 4 * (ball D V x 3).card - 110)
      (fun _ _ => Nat.zero_le _) vP
    have := (mem_filter.mp vP).2
    rw [e, sum_empty] at tot
    omega
  -- class membership
  have memZ : ∀ {Z v}, v ∈ cls (true, Z) → v ∈ R ∧ (layer D V 3 v).card = 8 ∧
      layer D V 3 v = Z := fun {Z v} hv => by
    obtain ⟨vR, kv⟩ := mem_filter.mp hv
    exact ⟨vR, key_true kv⟩
  have memY : ∀ {Y v}, v ∈ cls (false, Y) → v ∈ R ∧ (layer D V 3 v).card ≠ 8 ∧
      layer D V 2 v = Y := fun {Y v} hv => by
    obtain ⟨vR, kv⟩ := mem_filter.mp hv
    exact ⟨vR, key_false kv⟩
  have keyY : ∀ v ∈ R, (layer D V 3 v).card ≠ 8 → key v = (false, layer D V 2 v) :=
    fun v _ h => by simp only [hkey, key54, if_neg h]
  have keyZ : ∀ v ∈ R, (layer D V 3 v).card = 8 → key v = (true, layer D V 3 v) :=
    fun v _ h => by simp only [hkey, key54, if_pos h]
  -- the payment data
  refine payment (R := R) (P := P) key (fun v => 110 - 4 * (ball D V v 3).card)
    (fun x => 4 * (ball D V x 3).card - 110)
    (fun K => 2 * ∑ w ∈ cls K, ((cls K).filter (fun x => x ∈ gap D V 3 3 w)).card)
    (fun K => if K.1 then 2 else 1)
    (fun K => if K.1 then zSet D V K.2 else complete D V (rep K))
    (2 * ∑ v ∈ V, (gap D V 3 3 v).card) ?_ ?_ ?_ ?_ Rne tot.le
  · -- pair credit
    rw [← mul_sum]
    refine Nat.mul_le_mul_left 2 ?_
    calc ∑ K ∈ R.image key, ∑ w ∈ cls K, ((cls K).filter (fun x => x ∈ gap D V 3 3 w)).card
        ≤ ∑ K ∈ R.image key, ∑ w ∈ R.filter (fun v => key v = K), (gap D V 3 3 w).card :=
          sum_le_sum (fun K _ => sum_le_sum (fun w _ => card_le_card
            (fun x hx => (mem_filter.mp hx).2)))
      _ = ∑ w ∈ R, (gap D V 3 3 w).card :=
          sum_fiberwise_of_maps_to (fun v hv => mem_image_of_mem key hv) _
      _ ≤ ∑ v ∈ V, (gap D V 3 3 v).card := sum_le_sum_of_subset RV
  · -- each class
    intro K hK
    obtain ⟨t, Z⟩ := K
    cases t with
    | true =>
      simp only [if_true]
      set C0 := cls (true, Z) with hC0
      change ∑ v ∈ C0, _ < 2 * ∑ w ∈ C0, (C0.filter (fun x => x ∈ gap D V 3 3 w)).card + _
      obtain ⟨u, uR, ku⟩ := mem_image.mp hK
      have uC : u ∈ C0 := mem_filter.mpr ⟨uR, ku⟩
      set A := C0.filter (fun v => (ball D V v 3).card = 26) with hA
      set Cc := C0.filter (fun v => ¬ (ball D V v 3).card = 26) with hCc
      have AC : A ∪ Cc = C0 := filter_union_filter_not_eq _ _
      have disAC : Disjoint A Cc := disjoint_filter_filter_not _ _ _
      have Afacts : ∀ v ∈ A, v ∈ V ∧ (ball D V v 3).card = 26 ∧ (layer D V 2 v).card = 8 ∧
          (layer D V 3 v).card = 8 ∧ layer D V 3 v = Z := by
        intro v hv
        obtain ⟨vC, e⟩ := mem_filter.mp hv
        obtain ⟨vR, c8, lz⟩ := memZ vC
        rcases typ v vR with h | h | h
        · exact ⟨RV vR, e, h.2.1, c8, lz⟩
        · omega
        · omega
      have Cfacts : ∀ v ∈ Cc, v ∈ V ∧ (ball D V v 3).card = 27 ∧ (layer D V 2 v).card = 9 ∧
          (layer D V 3 v).card = 8 ∧ layer D V 3 v = Z := by
        intro v hv
        obtain ⟨vC, e⟩ := mem_filter.mp hv
        obtain ⟨vR, c8, lz⟩ := memZ vC
        rcases typ v vR with h | h | h
        · omega
        · omega
        · exact ⟨RV vR, h.1, h.2.1, c8, lz⟩
      have dfcS : ∑ v ∈ C0, (110 - 4 * (ball D V v 3).card) = 6 * A.card + 2 * Cc.card := by
        rw [← sum_filter_add_sum_filter_not C0 (fun v => (ball D V v 3).card = 26), ← hA, ← hCc,
          sum_congr rfl (fun v hv => by rw [(Afacts v hv).2.1] : ∀ v ∈ A,
            110 - 4 * (ball D V v 3).card = 6),
          sum_congr rfl (fun v hv => by rw [(Cfacts v hv).2.1] : ∀ v ∈ Cc,
            110 - 4 * (ball D V v 3).card = 2)]
        simp [mul_comm]
      rw [dfcS]
      by_cases hAe : A.Nonempty
      · obtain ⟨u0, hu0⟩ := hAe
        obtain ⟨u0V, -, l2, l3, lz⟩ := Afacts u0 hu0
        have five := laws.s5 u0 u0V ⟨by omega, by omega⟩
        rw [lz] at five
        have cg := class_gap (j := 3) (i := 3) (i' := 3) (s := 18) (Λ := Z) free (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (fun v hv => (Afacts v hv).1)
          (fun v hv => (Cfacts v hv).1) disAC (fun v hv => (Afacts v hv).2.2.2.2)
          (fun v hv => (Cfacts v hv).2.2.2.2)
          (fun v hv => by rw [show 3 - 1 = 2 from rfl, b2 v (Afacts v hv).1, (Afacts v hv).2.2.1])
          (fun v hv => by rw [show 3 - 1 = 2 from rfl, b2 v (Cfacts v hv).1, (Cfacts v hv).2.2.1])
        have hm : C0.card = A.card + Cc.card := by rw [← AC, card_union_of_disjoint disAC]
        rw [AC, hm] at cg
        have bill := bill_mixed (a := A.card) (c := Cc.card)
          (inc := ∑ w ∈ C0, (C0.filter (fun x => x ∈ gap D V 3 3 w)).card)
          cg
        omega
      · rw [not_nonempty_iff_eq_empty] at hAe
        have CcC : Cc = C0 := by rw [← AC, hAe, empty_union]
        obtain ⟨uV, -, l2, l3, lz⟩ := Cfacts u (by rw [CcC]; exact uC)
        have two := laws.s2 u uV (by unfold Thin; omega) l2 l3
        rw [lz] at two
        have cg := class_gap (j := 3) (i := 3) (i' := 3) (s := 19) (Λ := Z) (K₂ := ∅) free
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun v hv => (Cfacts v hv).1)
          (empty_subset _) (disjoint_empty_right _) (fun v hv => (Cfacts v hv).2.2.2.2)
          (fun v hv => absurd hv (notMem_empty v))
          (fun v hv => by rw [show 3 - 1 = 2 from rfl, b2 v (Cfacts v hv).1, (Cfacts v hv).2.2.1])
          (fun v hv => absurd hv (notMem_empty v))
        rw [union_empty, card_empty, CcC] at cg
        have bill := bill_pure (m := C0.card) (by simpa using cg)
        rw [hAe, CcC, card_empty]
        omega
    | false =>
      simp only [Bool.false_eq_true, if_false]
      set C0 := cls (false, Z) with hC0
      change ∑ v ∈ C0, _ < 2 * ∑ w ∈ C0, (C0.filter (fun x => x ∈ gap D V 3 3 w)).card + _
      have Yfacts : ∀ v ∈ C0, v ∈ V ∧ (ball D V v 3).card = 27 ∧ (layer D V 2 v).card = 8 ∧
          layer D V 2 v = Z := by
        intro v hv
        obtain ⟨vR, c8, lz⟩ := memY hv
        rcases typ v vR with h | h | h
        · exact absurd h.2.2 c8
        · exact ⟨RV vR, h.1, h.2.1, lz⟩
        · exact absurd h.2.2 c8
      have dfcS : ∑ v ∈ C0, (110 - 4 * (ball D V v 3).card) = 2 * C0.card := by
        rw [sum_congr rfl (fun v hv => by rw [(Yfacts v hv).2.1] : ∀ v ∈ C0,
          110 - 4 * (ball D V v 3).card = 2)]
        simp [mul_comm]
      rw [dfcS]
      obtain ⟨rR, rk⟩ := pick_spec hK
      have rC : rep (false, Z) ∈ C0 := mem_filter.mpr ⟨rR, rk⟩
      obtain ⟨rV, -, r8, -⟩ := Yfacts _ rC
      have cc := ThinSuppliers.complete_count (q := 6) free (by norm_num) reg rV
        (show Thin D V 9 (rep (false, Z)) by unfold Thin; omega) (by norm_num)
      have cg := class_gap (j := 2) (i := 3) (i' := 3) (s := 10) (Λ := Z) (K₂ := ∅) free
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun v hv => (Yfacts v hv).1)
        (empty_subset _) (disjoint_empty_right _) (fun v hv => (Yfacts v hv).2.2.2)
        (fun v hv => absurd hv (notMem_empty v))
        (fun v hv => by rw [show 2 - 1 = 1 from rfl, b1 v (Yfacts v hv).1])
        (fun v hv => absurd hv (notMem_empty v))
      rw [union_empty, card_empty] at cg
      have bill := bill_pure (m := C0.card) (by simpa using cg)
      omega
  · -- payers are above the level
    intro K hK
    obtain ⟨t, Z⟩ := K
    cases t with
    | true =>
      simp only [if_true]
      intro x hx
      obtain ⟨xV, b28, -⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨xV, b28⟩
    | false =>
      simp only [Bool.false_eq_true, if_false]
      intro x hx
      obtain ⟨rR, rk⟩ := pick_spec hK
      obtain ⟨-, c8, lz⟩ := memY (mem_filter.mpr ⟨rR, rk⟩ : rep (false, Z) ∈ cls (false, Z))
      have rV := RV rR
      rcases typ _ rR with h | h | h
      · exact absurd h.2.2 c8
      · have x29 := laws.l9 _ rV (by unfold Thin; omega) h.1 x hx
        exact mem_filter.mpr ⟨(mem_outN.mp (complete_subset hx)).1, by omega⟩
      · exact absurd h.2.2 c8
  · -- capacities
    intro x hx
    obtain ⟨xV, b28⟩ := mem_filter.mp hx
    set F := (R.image key).filter (fun K => x ∈ if K.1 then zSet D V K.2 else complete D V (rep K))
      with hF
    have spl := sum_filter_add_sum_filter_not F (fun K => K.1 = true)
      (fun K => if K.1 then 2 else 1)
    set FZ := F.filter (fun K => K.1 = true) with hFZ
    set FY := F.filter (fun K => ¬ K.1 = true) with hFY
    have eZ : ∑ K ∈ FZ, (if K.1 then 2 else 1) = 2 * FZ.card := by
      rw [sum_congr rfl (fun K hK => by rw [if_pos (mem_filter.mp hK).2]), sum_const,
        smul_eq_mul, mul_comm]
    have eY : ∑ K ∈ FY, (if K.1 then 2 else 1) = FY.card := by
      rw [sum_congr rfl (fun K hK => by rw [if_neg (mem_filter.mp hK).2]), sum_const,
        smul_eq_mul, mul_one]
    -- at most one third-layer class
    have zc : FZ.card ≤ 1 := by
      refine card_le_one.mpr (fun K hK K' hK' => ?_)
      obtain ⟨hKF, t1⟩ := mem_filter.mp hK
      obtain ⟨hK'F, t1'⟩ := mem_filter.mp hK'
      obtain ⟨hKi, xK⟩ := mem_filter.mp hKF
      obtain ⟨hK'i, xK'⟩ := mem_filter.mp hK'F
      rw [if_pos t1] at xK
      rw [if_pos t1'] at xK'
      obtain ⟨u, uR, rfl⟩ := mem_image.mp hKi
      obtain ⟨u', uR', rfl⟩ := mem_image.mp hK'i
      have hu : (layer D V 3 u).card = 8 := by
        by_contra c; rw [keyY u uR c] at t1; simp at t1
      have hu' : (layer D V 3 u').card = 8 := by
        by_contra c; rw [keyY u' uR' c] at t1'; simp at t1'
      rw [keyZ u uR hu] at xK ⊢
      rw [keyZ u' uR' hu'] at xK' ⊢
      by_contra ne
      exact Supplier54.zSet_exclusive free (by norm_num) (fun e => ne (Prod.ext rfl e))
        (by rw [hu, hu']) xK xK'
    -- the second-layer classes
    have sY : 2 * FZ.card + FY.card ≤ 4 * (ball D V x 3).card - 110 := by
      rcases FY.eq_empty_or_nonempty with e | ne
      · rw [e, card_empty]; omega
      have repF : ∀ K ∈ FY, rep K ∈ R ∧ key (rep K) = K ∧ x ∈ complete D V (rep K) ∧
          K = (false, layer D V 2 (rep K)) ∧ (ball D V (rep K) 3).card = 27 ∧
          Thin D V 9 (rep K) := by
        intro K hK
        obtain ⟨hKF, t0⟩ := mem_filter.mp hK
        obtain ⟨hKi, xK⟩ := mem_filter.mp hKF
        rw [if_neg t0] at xK
        obtain ⟨rR, rk⟩ := pick_spec hKi
        have c8 : (layer D V 3 (rep K)).card ≠ 8 := by
          intro c; rw [keyZ _ rR c] at rk; rw [← rk] at t0; exact t0 rfl
        rcases typ _ rR with h | h | h
        · exact absurd h.2.2 c8
        · refine ⟨rR, rk, xK, rk.symm.trans (keyY _ rR c8), h.1, ?_⟩
          show (layer D V 2 (pick R key K)).card + 1 = 9
          omega
        · exact absurd h.2.2 c8
      obtain ⟨K0, hK0⟩ := ne
      obtain ⟨r0R, -, x0, -, r27, r0t⟩ := repF K0 hK0
      have x29 := laws.l9 _ (RV r0R) r0t r27 x x0
      by_cases small : FY.card ≤ 4
      · omega
      -- five or more: the supplier score
      set Rr := FY.image rep with hRr
      have injR : Set.InjOn rep FY := fun K hK K' hK' e => by
        rw [← (repF K hK).2.1, ← (repF K' hK').2.1, e]
      have cR : Rr.card = FY.card := card_image_of_injOn injR
      have c0 : rep K0 ∈ Rr := mem_image_of_mem rep hK0
      have sc := TopRowFat.supplier_score (q := 6) (r := 9) (i := 3) (j := 3) free (by norm_num)
        (by norm_num) reg (by norm_num) (by norm_num) (by norm_num) (by norm_num) (R := Rr)
        (fun w hw => by
          obtain ⟨K, hK, rfl⟩ := mem_image.mp hw
          exact RV (repF K hK).1)
        (fun w hw => by
          obtain ⟨K, hK, rfl⟩ := mem_image.mp hw
          exact (repF K hK).2.2.2.2.2)
        (fun w hw => by
          obtain ⟨K, hK, rfl⟩ := mem_image.mp hw
          exact (repF K hK).2.2.1)
        (fun w hw w' hw' e => by
          obtain ⟨K, hK, rfl⟩ := mem_image.mp hw
          obtain ⟨K', hK', rfl⟩ := mem_image.mp hw'
          rw [show K = K' by rw [(repF K hK).2.2.2.1, (repF K' hK').2.2.2.1, e]])
        c0
      have f4 := (TopRowFloors6.floors6 free reg).2 _ (RV r0R) r0t (by omega)
      rw [cR] at sc
      have e4 : ball D V (rep K0) (3 + 1) = ball D V (rep K0) 4 := rfl
      rw [e4] at sc
      omega
    show ∑ K ∈ F, _ ≤ _
    rw [← spl, eZ, eY]
    exact sY

#print axioms payment
#print axioms ledger_split
#print axioms class_gap
#print axioms class_bill
#print axioms bill_mixed
#print axioms bill_pure
#print axioms root_type
#print axioms no54_of_laws

end LeanCH.BR.Close54
