import checkpoints.shen_extension.AncestorRow
import checkpoints.shen_extension.TopRowFat
import checkpoints.shen_extension.SinkDepthReturn

/-!
# Three layer profiles on the row `r = q + 1` (every `q ≥ 8`; at `q = 8`, `r = 9`: order 72)

`free : QFree D V q`, `8 ≤ q`, every out-degree `q + 1`, a root `u ∈ V`,
`X = outN D V u` (`|X| = q + 1`), `Y = layer D V 2 u`, `Z = layer D V 3 u`, `W = layer D V 4 u`.

Common lemmas (generic, no degree hypothesis unless stated):
* `cyc_omit` (L1 on a cycle): `v` on a closed walk inside `P`, `v ⇝ x` of length `b`: `x` omits at
  least `q - b` labels of `P`.
* `split_bank`: a set of `q + 1` labels is a bank cycle (one inner head each) or acyclic with a sink.
* `deep_bound` (L2 counting): `t`-deep rows and sinks of an acyclic set; `near_exists`.
* L3 is `SupplierFat54.fact_C` (used with `j = 0` and with a sink at distance `j`).
* `x_acct`: a head of `u` omits `|Y| + h - (q + 1)` labels of `Y`, `h` its heads in `X`.

Profile 0 (`|Y| = q + 1`, `|Z| = q`): `profile0`, through the row-`(q' + 3)` theorems at `q' = q - 2`.
Profile I (`|Y| = |Z| = q + 1`, `|W| = q`): `profileI`. The split is: `Y` a bank (`ycyc_noRet`), or
`Y` acyclic with `X` acyclic (`xacyc_part`) or `X` a bank (`xcyc_part`), both finished by
`acycA_finish` (paper I.5) with `A = aSet`, the rows of `Y` reaching no tail.
Profile II is in `Profiles72II.lean`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.Profiles72
open Finset BRq2 BRq3 ThinSuppliers OneHead
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)
open SupplierFat54 (IsTail oSet aSet mem_oSet oSet_subset aSet_subset aSet_V tail_o a_cover om mem_om
  om_card fact_C in_ball_two two_layers layer_disj keep_count oa_card)
open SinkReturnAncestors (Sink)
open SinkDepthReturn (Deep return_deep deep_heads)

variable {D : CH.Digraph} {V : Finset ℕ} {u q : ℕ}

/-! ### Generic lemmas -/

/-- `v` lies on a closed walk inside `P`. -/
def OnCyc (D : CH.Digraph) (P : Finset ℕ) (v : ℕ) : Prop :=
  ∃ w ∈ P, D v w = true ∧ ∃ L, Walk D P w v L

/-- Rows of `P` that omit `y`. -/
def omx (D : CH.Digraph) (P : Finset ℕ) (y : ℕ) : Finset ℕ := P.filter (fun x => ¬ D x y = true)

theorem mem_omx {P : Finset ℕ} {y x : ℕ} : x ∈ omx D P y ↔ x ∈ P ∧ ¬ D x y = true := mem_filter

/-- Double counting of omissions. -/
theorem om_swap (X Y : Finset ℕ) :
    ∑ x ∈ X, (om D Y x).card = ∑ y ∈ Y, (omx D X y).card := by
  unfold om omx
  simp only [card_filter]
  exact sum_comm

theorem ball_trans {a b c i j : ℕ} (h1 : b ∈ ball D V a i) (h2 : c ∈ ball D V b j) :
    c ∈ ball D V a (i + j) := by
  obtain ⟨-, k1, hk1, w1⟩ := mem_ball.mp h1
  obtain ⟨cV, k2, hk2, w2⟩ := mem_ball.mp h2
  exact mem_ball.mpr ⟨cV, k1 + k2, by omega, w1.append w2⟩

theorem ball_arc {a b : ℕ} (bV : b ∈ V) (ab : D a b = true) : b ∈ ball D V a 1 :=
  mem_ball.mpr ⟨bV, 1, le_rfl, .step bV ab (.refl b)⟩

/-- Heads split between two sets. -/
theorem split_count {F E : Finset ℕ} {v : ℕ} (cover : outN D V v ⊆ F ∪ E) :
    (outN D V v).card ≤ (outN D F v).card + (outN D E v).card := by
  have : outN D V v ⊆ outN D F v ∪ outN D E v := by
    intro t ht
    obtain ⟨-, a⟩ := mem_outN.mp ht
    rcases mem_union.mp (cover ht) with h | h
    · exact mem_union_left _ (mem_outN.mpr ⟨h, a⟩)
    · exact mem_union_right _ (mem_outN.mpr ⟨h, a⟩)
  exact (card_le_card this).trans (card_union_le _ _)

theorem sink_empty {P : Finset ℕ} {s : ℕ} (h : Sink D P s) : outN D P s = ∅ := by
  ext a
  simp only [mem_outN, Finset.notMem_empty, iff_false, not_and]
  exact fun aP arc => h a aP arc

theorem sink_of_empty {P : Finset ℕ} {s : ℕ} (h : outN D P s = ∅) : Sink D P s := by
  intro a aP arc
  have : a ∈ outN D P s := mem_outN.mpr ⟨aP, arc⟩
  rw [h] at this
  exact Finset.notMem_empty a this

/-- **L1 on a cycle (generic).** If `v` lies on a closed walk inside `P ⊆ V` and `v ⇝ x` by a
walk of length `b` with `b + 1 ≤ q`, then `x` omits at least `q - b` labels of `P`: the last
`q - b` rows of the closed walk before `v`. -/
theorem cyc_omit (free : QFree D V q) {P : Finset ℕ} (PV : P ⊆ V) {v x b : ℕ}
    (hv : OnCyc D P v) (path : Walk D V v x b) (hb : b + 1 ≤ q) :
    q - b ≤ (om D P x).card := by
  obtain ⟨w, wP, vw, L, back⟩ := hv
  have hL : q ≤ L := by
    by_contra h
    exact free w (L + 1) (by omega) (by omega) ((back.snoc wP vw).mono PV)
  obtain ⟨f, -, fL, hf⟩ := back.toFun
  have fP : ∀ i, 1 ≤ i → i ≤ L → f i ∈ P := fun i h1 h2 => by
    have := (hf (i - 1) (by omega)).1
    rwa [show i - 1 + 1 = i by omega] at this
  have seg : ∀ i, i ≤ L → Walk D P (f (L - i)) v i := by
    intro i hi
    have := walk_between (D := D) (W := P) (f := f) (m := L) (fun k hk => hf k hk)
      (i := L - i) (j := L) (by omega) le_rfl
    rwa [show L - (L - i) = i by omega, fL] at this
  have sub : (range (q - b)).image (fun i => f (L - i)) ⊆ om D P x := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
    rw [mem_range] at hi
    refine mem_om.mpr ⟨fP _ (by omega) (by omega), fun arc => ?_⟩
    exact free x (i + 1 + b) (by omega) (by omega)
      ((Walk.step (PV (fP _ (by omega) (by omega))) arc ((seg i (by omega)).mono PV)).append path)
  have inj : Set.InjOn (fun i => f (L - i)) (range (q - b) : Set ℕ) := by
    intro i hi j hj e
    simp only [coe_range, Set.mem_Iio] at hi hj
    have e' : f (L - i) = f (L - j) := e
    by_contra ne
    rcases lt_or_gt_of_ne ne with lt | lt
    · have w := walk_between (D := D) (W := P) (f := f) (m := L) (fun k hk => hf k hk)
        (i := L - j) (j := L - i) (by omega) (by omega)
      rw [e'] at w
      exact free _ (L - i - (L - j)) (by omega) (by omega) (w.mono PV)
    · have w := walk_between (D := D) (W := P) (f := f) (m := L) (fun k hk => hf k hk)
        (i := L - i) (j := L - j) (by omega) (by omega)
      rw [← e'] at w
      exact free _ (L - j - (L - i)) (by omega) (by omega) (w.mono PV)
  have := card_le_card sub
  rwa [card_image_of_injOn inj, card_range] at this

/-- In a `q`-free set of at most `q + 1` labels with minimum out-degree one every row lies on a
closed walk. -/
theorem oncyc_of_deg {P : Finset ℕ} (free : QFree D P q) (deg : ∀ v ∈ P, 1 ≤ (outN D P v).card)
    (size : P.card ≤ q + 1) {v : ℕ} (hv : v ∈ P) : OnCyc D P v := by
  obtain ⟨w, hw⟩ := card_pos.mp (show 0 < (outN D P v).card by have := deg v hv; omega)
  obtain ⟨wP, vw⟩ := mem_outN.mp hw
  have big := LoopCollar.ball_grow free deg wP q le_rfl
  have e : ball D P w q = P := eq_of_subset_of_card_le ball_subset (by omega)
  have vb : v ∈ ball D P w q := by rw [e]; exact hv
  obtain ⟨-, L, -, walk⟩ := mem_ball.mp vb
  exact ⟨w, wP, vw, L, walk⟩

/-- The next row on a closed walk is again on a closed walk. -/
theorem oncyc_next (free : QFree D V q) (hq : 1 ≤ q) {P : Finset ℕ} (PV : P ⊆ V) {v : ℕ}
    (vP : v ∈ P) (hv : OnCyc D P v) : ∃ w ∈ P, D v w = true ∧ OnCyc D P w := by
  obtain ⟨w, wP, vw, L, back⟩ := hv
  cases back with
  | refl => exact absurd vw (loopfree free hq (PV vP))
  | step h1 a1 rest => exact ⟨w, wP, vw, _, h1, a1, _, rest.snoc wP vw⟩

/-- **Bank or acyclic (generic).** A set of `q + 1` labels in a `q`-free digraph: every row has
exactly one inner head, or the set has a sink and no closed walk of length at most `q + 1`. -/
theorem split_bank (free : QFree D V q) (hq : 1 ≤ q) {P : Finset ℕ} (PV : P ⊆ V)
    (cP : P.card = q + 1) :
    (∀ v ∈ P, (outN D P v).card = 1) ∨ (QFree D P (q + 1) ∧ ∃ s ∈ P, outN D P s = ∅) := by
  by_cases h : ∀ v ∈ P, 1 ≤ (outN D P v).card
  · exact Or.inl (LoopCollar.loop_unique_head (free.mono_set PV) hq cP h)
  · push Not at h
    obtain ⟨s, sP, hs⟩ := h
    have e : outN D P s = ∅ := card_eq_zero.mp (by omega)
    exact Or.inr ⟨qfree_succ_of_sink (free.mono_set PV) cP sP (sink_of_empty e), s, sP, e⟩

theorem not_deep {P : Finset ℕ} {t x : ℕ} (h : ¬ Deep D P t x) :
    ∃ s ∈ P, Sink D P s ∧ ∃ k, k < t ∧ Walk D P x s k := by
  by_contra none
  apply h
  intro s sP sk k w
  by_contra lt
  exact none ⟨s, sP, sk, k, by omega, w⟩

theorem deep_head {P : Finset ℕ} {t t' x c : ℕ} (h : Deep D P t x) (ht : t' + 1 ≤ t)
    (cP : c ∈ P) (xc : D x c = true) : Deep D P t' c := fun s sP sk k w => by
  have := h s sP sk (k + 1) (.step cP xc w)
  omega

/-- **L2 counting (generic).** In a `q'`-free set `P` with `|P| ≤ q'`: a nonempty set `T` of
`t`-deep rows (`1 ≤ t`) and any set `K` of sinks satisfy `t + |T| ≤ |P|` and
`t - 1 + |K| + |T| ≤ |P|` (a shortest sink path from a deep row, and the sinks). -/
theorem deep_bound {P : Finset ℕ} {q' t : ℕ} (free : QFree D P q') (size : P.card ≤ q')
    (ht : 1 ≤ t) {T K : Finset ℕ} (TP : T ⊆ P) (hT : ∀ x ∈ T, Deep D P t x) (KP : K ⊆ P)
    (hK : ∀ s ∈ K, Sink D P s) (ne : T.Nonempty) :
    t + T.card ≤ P.card ∧ t - 1 + K.card + T.card ≤ P.card := by
  classical
  obtain ⟨x0, hx0⟩ := ne
  obtain ⟨p⟩ := exists_shortest_sink_path free size (TP hx0)
  have len : t ≤ p.len := (SinkDepthReturn.deep_iff_len p).mp (hT x0 hx0)
  have gmem : ∀ j, j < t - 1 → p.vertex (p.len - (j + 1)) ∈ P := fun j hj => p.mem _ (by omega)
  have gshallow : ∀ j, j < t - 1 → ¬ Deep D P t (p.vertex (p.len - (j + 1))) := by
    intro j hj deep
    have walk := p.walk (i := p.len - (j + 1)) (j := p.len) (by omega) le_rfl
    have := deep _ (p.mem _ le_rfl) (fun z zm => p.sink z zm) _ walk
    omega
  have gnot : ∀ j, j < t - 1 → ¬ Sink D P (p.vertex (p.len - (j + 1))) := by
    intro j hj sk
    have e := p.edge (p.len - (j + 1)) (by omega)
    exact sk _ (p.mem (p.len - (j + 1) + 1) (by omega)) e
  have inj : Set.InjOn (fun j => p.vertex (p.len - (j + 1))) (range (t - 1) : Set ℕ) := by
    intro i hi j hj e
    simp only [coe_range, Set.mem_Iio] at hi hj
    have := p.injective free size (x₁ := p.len - (i + 1)) (x₂ := p.len - (j + 1))
      (by simp only [coe_range, Set.mem_Iio]; omega) (by simp only [coe_range, Set.mem_Iio]; omega) e
    omega
  set S := (range (t - 1)).image (fun j => p.vertex (p.len - (j + 1))) with hS
  set E := insert (p.vertex p.len) K with hE
  have cS : S.card = t - 1 := by rw [hS, card_image_of_injOn inj, card_range]
  have Esink : ∀ s ∈ E, Sink D P s := by
    intro s hs
    rcases mem_insert.mp hs with rfl | h
    · exact fun z zm => p.sink z zm
    · exact hK s h
  have dSE : Disjoint S E := by
    rw [disjoint_left]
    intro a aS aE
    obtain ⟨j, hj, rfl⟩ := mem_image.mp aS
    exact gnot j (mem_range.mp hj) (Esink _ aE)
  have dST : Disjoint (S ∪ E) T := by
    rw [disjoint_left]
    intro a aSE aT
    rcases mem_union.mp aSE with aS | aE
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp aS
      exact gshallow j (mem_range.mp hj) (hT _ aT)
    · have := hT a aT a (TP aT) (Esink a aE) 0 (.refl a)
      omega
  have sub : S ∪ E ∪ T ⊆ P := by
    refine union_subset (union_subset ?_ ?_) TP
    · intro a aS
      obtain ⟨j, hj, rfl⟩ := mem_image.mp aS
      exact gmem j (mem_range.mp hj)
    · intro a aE
      rcases mem_insert.mp aE with rfl | h
      · exact p.mem _ le_rfl
      · exact KP h
  have c := card_le_card sub
  rw [card_union_of_disjoint dST, card_union_of_disjoint dSE, cS] at c
  have e1 : 1 ≤ E.card := card_pos.mpr ⟨_, mem_insert_self _ _⟩
  have e2 : K.card ≤ E.card := card_le_card (subset_insert _ _)
  constructor <;> omega

/-- At least `min |P| t` rows of an acyclic `P` are not `t`-deep (they reach a sink in fewer than
`t` steps). -/
theorem near_exists {P : Finset ℕ} {q' t : ℕ} (free : QFree D P q') (size : P.card ≤ q')
    (ht : 1 ≤ t) : ∃ N ⊆ P, min P.card t ≤ N.card ∧ ∀ y ∈ N, ¬ Deep D P t y := by
  classical
  refine ⟨P.filter (fun x => ¬ Deep D P t x), filter_subset _ _, ?_,
    fun y hy => (mem_filter.mp hy).2⟩
  have split := card_filter_add_card_filter_not (s := P) (fun x => Deep D P t x)
  by_cases ne : (P.filter (fun x => Deep D P t x)).Nonempty
  · have := (deep_bound free size ht (T := P.filter (fun x => Deep D P t x)) (K := ∅)
      (filter_subset _ _) (fun x hx => (mem_filter.mp hx).2) (empty_subset _)
      (fun s hs => absurd hs (Finset.notMem_empty s)) ne).1
    omega
  · rw [not_nonempty_iff_eq_empty] at ne
    rw [ne, card_empty] at split
    omega

/-- An acyclic set `A` (`|A| ≥ 2`) and a row `x` that points to all of `A` but at most one label:
`x` reaches a sink of `A` within two steps. -/
theorem reach_sink_two {A : Finset ℕ} {q' : ℕ} (AV : A ⊆ V) (acA : QFree D A q') (cA : A.card ≤ q')
    (two : 2 ≤ A.card) {x : ℕ}
    (one : ∀ a ∈ A, ∀ b ∈ A, ¬ D x a = true → ¬ D x b = true → a = b) :
    ∃ s ∈ A, (∀ a ∈ A, ¬ D s a = true) ∧ s ∈ ball D V x 2 := by
  obtain ⟨s, sA, sk⟩ := exists_sink acA (card_pos.mp (by omega)) cA
  by_cases xs : D x s = true
  · exact ⟨s, sA, sk, ball_mono_radius (by norm_num) (ball_arc (AV sA) xs)⟩
  · obtain ⟨a, aA, as⟩ := exists_mem_ne (by omega : 1 < A.card) s
    obtain ⟨s', s'A, sk', m, -, w⟩ := reach_sink_of_card acA cA aA
    by_cases e : s' = s
    · rw [e] at w
      cases m with
      | zero => cases w; exact absurd rfl as
      | succ m =>
        obtain ⟨p, wp, -, ps⟩ := w.unsnoc
        have pA : p ∈ A := by
          rcases wp.end_mem_or with h | h
          · rw [h]; exact aA
          · exact h
        have pne : p ≠ s := fun h => by rw [h] at ps; exact sk s sA ps
        have xp : D x p = true := by
          by_contra xp
          exact pne (one p pA s sA xp xs)
        exact ⟨s, sA, sk, mem_ball.mpr ⟨AV sA, 2, le_rfl, .step (AV pA) xp (.step (AV sA) ps (.refl s))⟩⟩
    · have xs' : D x s' = true := by
        by_contra h
        exact e (one s' s'A s sA h xs)
      exact ⟨s', s'A, sk', ball_mono_radius (by norm_num) (ball_arc (AV s'A) xs')⟩

/-! ### Root facts -/

/-- **Omission accounting.** A head `x` of `u` omits `|Y| + h - (q + 1)` labels of `Y`, where `h`
is its number of heads in `X` (`2 ≤ q`). -/
theorem x_acct (free : QFree D V q) (hq : 2 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 1)
    (hu : u ∈ V) {x : ℕ} (hx : x ∈ outN D V u) :
    (om D (layer D V 2 u) x).card + (q + 1) =
      (layer D V 2 u).card + (outN D (outN D V u) x).card := by
  have keep := LoopCollar.head_keep free hq hu x hx
  have dXY : Disjoint (outN D V u) (layer D V 2 u) := Supplier54.heads_disj hu le_rfl
  have e : outN D V x = outN D (outN D V u) x ∪ outN D (layer D V 2 u) x := by
    ext w
    constructor
    · intro hw
      obtain ⟨-, a⟩ := mem_outN.mp hw
      rcases mem_union.mp (keep hw) with h | h
      · exact mem_union_left _ (mem_outN.mpr ⟨h, a⟩)
      · exact mem_union_right _ (mem_outN.mpr ⟨h, a⟩)
    · intro hw
      rcases mem_union.mp hw with h | h
      · obtain ⟨h1, a⟩ := mem_outN.mp h
        exact mem_outN.mpr ⟨outN_subset h1, a⟩
      · obtain ⟨h1, a⟩ := mem_outN.mp h
        exact mem_outN.mpr ⟨layer_subset h1, a⟩
  have d2 : Disjoint (outN D (outN D V u) x) (outN D (layer D V 2 u) x) :=
    dXY.mono outN_subset outN_subset
  have c := card_union_of_disjoint d2
  rw [← e, reg x (outN_subset hx)] at c
  have := om_card (D := D) (layer D V 2 u) x
  omega

/-- A row of `X` has at most `q` heads in `X`. -/
theorem x_heads_le (free : QFree D V q) (hq : 1 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 1)
    (hu : u ∈ V) {x : ℕ} (hx : x ∈ outN D V u) : (outN D (outN D V u) x).card ≤ q := by
  have sub : outN D (outN D V u) x ⊆ (outN D V u).erase x := by
    intro w hw
    obtain ⟨wX, xw⟩ := mem_outN.mp hw
    refine mem_erase.mpr ⟨fun e => ?_, wX⟩
    subst e
    exact loopfree free hq (outN_subset hx) xw
  have := card_le_card sub
  rw [card_erase_of_mem hx, reg u hu] at this
  omega

/-- Heads of a row of `Z`: never `u` (`4 ≤ q`). -/
theorem z_heads (free : QFree D V q) (hq : 4 ≤ q) (hu : u ∈ V) {z w : ℕ}
    (hz : z ∈ layer D V 3 u) (zw : D z w = true) (wV : w ∈ V) :
    w ∈ outN D V u ∨ w ∈ layer D V 2 u ∨ w ∈ layer D V 3 u ∨ w ∈ layer D V 4 u := by
  have wb : w ∈ ball D V u (2 + 2) := ball_step (mem_layer.mp hz).1 wV zw
  by_cases n2 : w ∈ ball D V u 2
  · rcases in_ball_two hu n2 with e | hx | hy
    · subst e
      exact absurd zw (no_back_arc free hu (mem_layer.mp hz).1 (by omega))
    · exact Or.inl hx
    · exact Or.inr (Or.inl hy)
  · rcases mem_union.mp (two_layers wb n2) with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

/-- A row of `Y` with no head in `Y` has a head in `X`, when `|Z| ≤ q`. -/
theorem ysink_tail (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 1)
    (hu : u ∈ V) (hZ : (layer D V 3 u).card ≤ q) {y : ℕ} (hy : y ∈ layer D V 2 u)
    (sk : ∀ a ∈ layer D V 2 u, ¬ D y a = true) : ∃ x ∈ outN D V u, D y x = true := by
  by_contra none
  push Not at none
  have sub : outN D V y ⊆ layer D V 3 u := by
    intro w hw
    obtain ⟨-, yw⟩ := mem_outN.mp hw
    rcases mem_union.mp (SupplierFat54.y_cover free hq hu hy hw) with h | h
    · rcases mem_union.mp h with hx | hy'
      · exact (none w hx yw).elim
      · exact (sk w hy' yw).elim
    · exact h
  have := card_le_card sub
  rw [reg y (layer_subset hy)] at this
  omega

/-- A sink of `X` sees all of `Y` when `|Y| = q + 1`. -/
theorem xsink_full1 (free : QFree D V q) (hq : 2 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 1)
    (hu : u ∈ V) (hY : (layer D V 2 u).card = q + 1) {s : ℕ} (sX : s ∈ outN D V u)
    (sk : Sink D (outN D V u) s) {y : ℕ} (hy : y ∈ layer D V 2 u) : D s y = true := by
  have a := x_acct free hq reg hu sX
  rw [hY, sink_empty sk, card_empty] at a
  by_contra h
  have : 0 < (om D (layer D V 2 u) s).card := card_pos.mpr ⟨y, mem_om.mpr ⟨hy, h⟩⟩
  omega

/-- A row of `aSet` with no head in `aSet` points to all of `Z`, when `|Z| = q + 1`. -/
theorem asink_full (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 1)
    (hu : u ∈ V) (hZ : (layer D V 3 u).card = q + 1) {s : ℕ} (hs : s ∈ aSet D V u)
    (sk : ∀ a ∈ aSet D V u, ¬ D s a = true) : layer D V 3 u ⊆ outN D V s := by
  have sub : outN D V s ⊆ layer D V 3 u := by
    intro w hw
    rcases mem_union.mp (a_cover free hu hq hs hw) with h | h
    · exact ((sk w h) (mem_outN.mp hw).2).elim
    · exact h
  have e := eq_of_subset_of_card_le sub (by have := reg s (aSet_V hs); omega)
  intro z hz
  rw [e]
  exact hz

/-! ### Profile 0: `|Y| = q + 1`, `|Z| = q` -/

/-- **Profile 0 (generic, `8 ≤ q`).** `Y` is a bank complete to `Z` (each row of `Y` has exactly one
head in `Y`, its heads lie in `Y ∪ Z`, and it points to all of `Z`); no row of `Z` or `W` points to
`u`, into `X` or into `Y`; and `|W| ≥ q + 1`. -/
theorem profile0 (free : QFree D V q) (hq : 8 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 1)
    (hu : u ∈ V) (hY : (layer D V 2 u).card = q + 1) (hZ : (layer D V 3 u).card = q) :
    (∀ a ∈ layer D V 2 u, (outN D (layer D V 2 u) a).card = 1) ∧
    (∀ a ∈ layer D V 2 u, outN D V a ⊆ layer D V 2 u ∪ layer D V 3 u) ∧
    (∀ a ∈ layer D V 2 u, layer D V 3 u ⊆ outN D V a) ∧
    (∀ j, 3 ≤ j → j ≤ 4 → ∀ t ∈ layer D V j u, ∀ v,
      (v = u ∨ v ∈ outN D V u ∨ v ∈ layer D V 2 u) → ¬ D t v = true) ∧
    q + 1 ≤ (layer D V 4 u).card := by
  have free' : QFree D V (q - 2) := free.mono_bound (by omega)
  have reg' : ∀ v ∈ V, (outN D V v).card = q - 2 + 3 := fun v hv => by rw [reg v hv]; omega
  have hY' : (layer D V 2 u).card = q - 2 + 3 := by rw [hY]; omega
  have hZ' : (layer D V 3 u).card = q - 2 + 2 := by rw [hZ]; omega
  have hq' : 6 ≤ q - 2 := by omega
  have ne := SupplierFat54.a_nonempty (AncestorRow.lemma5_row free' hq' reg' hu hY')
  have deg := SupplierFat54.a_deg free' hu (by omega) reg' hZ'
  have big := DipCost.order_one q D (aSet D V u) (free.mono_set aSet_V) deg ne
  have AY : aSet D V u = layer D V 2 u := eq_of_subset_of_card_le aSet_subset (by omega)
  have keep : ∀ a ∈ layer D V 2 u, outN D V a ⊆ layer D V 2 u ∪ layer D V 3 u := by
    intro a ha
    have h := a_cover free' hu (by omega) (show a ∈ aSet D V u by rw [AY]; exact ha)
    rwa [AY] at h
  have L := TopRowFat.loop_complete free (by omega) (layer_subset (D := D) (V := V) (R := 2) (u := u))
    hY (layer_disj (by norm_num : 2 < 3)) (by omega : (layer D V 3 u).card + 1 ≤ q + 1)
    (fun a ha => reg a (layer_subset ha)) keep
  refine ⟨fun a ha => (L a ha).1, keep, fun a ha => (L a ha).2.1, ?_, ?_⟩
  · intro j hj3 hj4 t ht v hv
    exact SupplierFat54.no_return free' hu hq' reg' hY' hZ' ne hj3 hj4 ht hv
  · obtain ⟨s, sZ, sk⟩ := exists_sink (free.mono_set (layer_subset (D := D) (V := V) (R := 3) (u := u)))
      (card_pos.mp (by omega)) (by omega)
    have cov := SupplierFat54.z_cover free' hu hq' reg' hY' hZ' ne sZ
    have sub : outN D V s ⊆ layer D V 4 u := by
      intro w hw
      rcases mem_union.mp (cov hw) with h | h
      · exact (sk w h (mem_outN.mp hw).2).elim
      · exact h
    have := card_le_card sub
    rw [reg s (layer_subset sZ)] at this
    exact this

/-! ### Profile I: `|Y| = |Z| = q + 1`, `|W| = q` -/

/-- An arc `y → x` from `Y` into an acyclic `X` (`|Y| = q + 1`): `x` is `(q - 1)`-deep in `X`. -/
theorem tgt_deep1 (free : QFree D V q) (hq : 2 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 1)
    (hu : u ∈ V) (hY : (layer D V 2 u).card = q + 1) {y x : ℕ} (hy : y ∈ layer D V 2 u)
    (hx : x ∈ outN D V u) (yx : D y x = true) : Deep D (outN D V u) (q - 1) x :=
  return_deep (m := 1) free outN_subset hx (fun _ sX sk =>
    .step (layer_subset hy) (xsink_full1 free hq reg hu hY sX sk hy) (.refl y)) yx

/-- **I.1.** If `Y` is a bank (one head in `Y` each), no row of `Y` points into `X`. -/
theorem ycyc_noX (free : QFree D V q) (hq : 8 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 1)
    (hu : u ∈ V) (hY : (layer D V 2 u).card = q + 1)
    (cyc : ∀ y ∈ layer D V 2 u, (outN D (layer D V 2 u) y).card = 1)
    {y x : ℕ} (hy : y ∈ layer D V 2 u) (hx : x ∈ outN D V u) (yx : D y x = true) : False := by
  have YV : layer D V 2 u ⊆ V := layer_subset
  have oc := oncyc_of_deg (free.mono_set YV) (fun v hv => (cyc v hv).ge) (by omega) hy
  have c1 := cyc_omit (b := 1) free YV oc (.step (outN_subset hx) yx (.refl x)) (by omega)
  have acct := x_acct free (by omega) reg hu hx
  have cX := reg u hu
  rcases split_bank free (by omega) (outN_subset (D := D) (W := V) (y := u)) (reg u hu)
    with cycX | ⟨acX, -⟩
  · have := cycX x hx
    omega
  · have dp := tgt_deep1 free (by omega) reg hu hY hy hx yx
    have := deep_heads acX (reg u hu).le hx dp
    omega

/-- **I.2.** If `Y` is a bank, no row of `Z` points into `X ∪ Y`. -/
theorem ycyc_noRet (free : QFree D V q) (hq : 8 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 1)
    (hu : u ∈ V) (hY : (layer D V 2 u).card = q + 1) (hZ : (layer D V 3 u).card = q + 1)
    (hW : (layer D V 4 u).card = q)
    (cyc : ∀ y ∈ layer D V 2 u, (outN D (layer D V 2 u) y).card = 1) :
    ∀ z ∈ layer D V 3 u, ∀ v, (v ∈ outN D V u ∨ v ∈ layer D V 2 u) → ¬ D z v = true := by
  have XV : outN D V u ⊆ V := outN_subset
  have YV : layer D V 2 u ⊆ V := layer_subset
  have ZV : layer D V 3 u ⊆ V := layer_subset
  -- each row of `Y` omits at most one label of `Z`
  have yZ : ∀ y ∈ layer D V 2 u, (om D (layer D V 3 u) y).card ≤ 1 := by
    intro y hy
    have cover : outN D V y ⊆ layer D V 2 u ∪ layer D V 3 u := by
      intro w hw
      obtain ⟨-, yw⟩ := mem_outN.mp hw
      rcases mem_union.mp (SupplierFat54.y_cover free (by omega) hu hy hw) with h | h
      · rcases mem_union.mp h with hx | hy'
        · exact (ycyc_noX free hq reg hu hY cyc hy hx yw).elim
        · exact mem_union_left _ hy'
      · exact mem_union_right _ h
    have c := split_count cover
    rw [reg y (YV hy), cyc y hy] at c
    have e := om_card (D := D) (layer D V 3 u) y
    omega
  have degY : ∀ v ∈ layer D V 2 u, 1 ≤ (outN D (layer D V 2 u) v).card := fun v hv => (cyc v hv).ge
  -- a returning row of `Z` is omitted by at least `q - 2` rows of `Y`, one of them within two steps
  have ret : ∀ z ∈ layer D V 3 u, ∀ v, (v ∈ outN D V u ∨ v ∈ layer D V 2 u) → D z v = true →
      q - 2 ≤ (omx D (layer D V 2 u) z).card ∧
        ∃ y1 ∈ layer D V 2 u, ¬ D y1 z = true ∧ y1 ∈ ball D V z 2 := by
    intro z hz v hv zv
    rcases hv with hx | hy
    · -- `z → x`: the heads of `x` in `Y` omit `z`
      have sub : outN D (layer D V 2 u) v ⊆ omx D (layer D V 2 u) z := by
        intro y hy'
        obtain ⟨yY, xy⟩ := mem_outN.mp hy'
        refine mem_omx.mpr ⟨yY, fun yz => ?_⟩
        exact free z 3 (by norm_num) (by omega)
          (.step (XV hx) zv (.step (YV yY) xy (.step (ZV hz) yz (.refl z))))
      have h3 : (outN D (outN D V u) v).card ≤ 3 := by
        rcases split_bank free (by omega) XV (reg u hu) with cycX | ⟨acX, -⟩
        · rw [cycX v hx]; omega
        · obtain ⟨p, hp, pz⟩ := ShapeClimbRoot.parent_mem hu (i := 2) (by norm_num) hz
          have dp := return_deep (m := 2) free XV hx (fun s sX sk =>
            .step (YV hp) (xsink_full1 free (by omega) reg hu hY sX sk hp)
              (.step (ZV hz) pz (.refl z))) zv
          have := deep_heads acX (reg u hu).le hx dp
          have := reg u hu
          omega
      have acct := x_acct free (by omega) reg hu hx
      have oc := om_card (D := D) (layer D V 2 u) v
      have c := card_le_card sub
      obtain ⟨y1, hy1⟩ := card_pos.mp (show 0 < (outN D (layer D V 2 u) v).card by omega)
      obtain ⟨y1Y, xy1⟩ := mem_outN.mp hy1
      refine ⟨by omega, y1, y1Y, (mem_omx.mp (sub hy1)).2, ?_⟩
      exact ball_trans (ball_arc (XV hx) zv) (ball_arc (YV y1Y) xy1)
    · -- `z → y'`: the rows of `Y` within `q - 2` of `y'` omit `z`
      have sub : ball D (layer D V 2 u) v (q - 2) ⊆ omx D (layer D V 2 u) z := by
        intro y hy'
        obtain ⟨yY, j, hj, w⟩ := mem_ball.mp hy'
        refine mem_omx.mpr ⟨yY, fun yz => ?_⟩
        exact free z (j + 1 + 1) (by omega) (by omega)
          (.step (YV hy) zv ((w.mono YV).snoc (ZV hz) yz))
      have g := LoopCollar.ball_grow (free.mono_set YV) degY hy (q - 2) (by omega)
      have c := card_le_card sub
      refine ⟨by omega, v, hy, fun vz => digonfree free (by omega) (ZV hz) (YV hy) zv vz, ?_⟩
      exact ball_mono_radius (by norm_num) (ball_arc (YV hy) zv)
  -- two returning labels have disjoint omitter sets
  have uniq : ∀ z1 ∈ layer D V 3 u, ∀ z2 ∈ layer D V 3 u,
      q - 2 ≤ (omx D (layer D V 2 u) z1).card → q - 2 ≤ (omx D (layer D V 2 u) z2).card →
      z1 = z2 := by
    intro z1 h1 z2 h2 c1 c2
    by_contra ne
    have d : Disjoint (omx D (layer D V 2 u) z1) (omx D (layer D V 2 u) z2) := by
      rw [disjoint_left]
      intro y a b
      obtain ⟨yY, n1⟩ := mem_omx.mp a
      obtain ⟨-, n2⟩ := mem_omx.mp b
      have := two_le_card ne (mem_om.mpr ⟨h1, n1⟩) (mem_om.mpr ⟨h2, n2⟩)
      have := yZ y yY
      omega
    have sub : omx D (layer D V 2 u) z1 ∪ omx D (layer D V 2 u) z2 ⊆ layer D V 2 u :=
      union_subset (filter_subset _ _) (filter_subset _ _)
    have := card_le_card sub
    rw [card_union_of_disjoint d, hY] at this
    omega
  intro z0 hz0 v0 hv0 zv0
  obtain ⟨c0, y1, hy1, ny1, yb⟩ := ret z0 hz0 v0 hv0 zv0
  -- `y1` points to every other row of `Z`
  have y1all : ∀ z ∈ layer D V 3 u, z ≠ z0 → D y1 z = true := by
    intro z hz ne
    by_contra h
    have := two_le_card ne (mem_om.mpr ⟨hz, h⟩) (mem_om.mpr ⟨hz0, ny1⟩)
    have := yZ y1 hy1
    omega
  -- so no other row of `Z` points to `z0`, and no other row returns
  have deg : ∀ z ∈ (layer D V 3 u).erase z0, 1 ≤ (outN D ((layer D V 3 u).erase z0) z).card := by
    intro z hz
    obtain ⟨ne, zZ⟩ := mem_erase.mp hz
    have cover : outN D V z ⊆ (layer D V 3 u).erase z0 ∪ layer D V 4 u := by
      intro w hw
      obtain ⟨wV, zw⟩ := mem_outN.mp hw
      rcases z_heads free (by omega) hu zZ zw wV with h | h | h | h
      · exact (ne (uniq z zZ z0 hz0 (ret z zZ w (Or.inl h) zw).1 c0)).elim
      · exact (ne (uniq z zZ z0 hz0 (ret z zZ w (Or.inr h) zw).1 c0)).elim
      · refine mem_union_left _ (mem_erase.mpr ⟨fun e => ?_, h⟩)
        rw [e] at zw
        have zb : z ∈ ball D V z0 (2 + 1) := ball_trans yb (ball_arc (ZV zZ) (y1all z zZ ne))
        exact no_back_arc free (ZV hz0) zb (by omega) zw
      · exact mem_union_right _ h
    have c := keep_count cover
    rw [reg z (ZV zZ), hW] at c
    omega
  have := DipCost.order_one q D ((layer D V 3 u).erase z0) (free.mono_set ((erase_subset _ _).trans ZV))
    deg (by
      obtain ⟨z, hz, ne⟩ := exists_mem_ne (by omega : 1 < (layer D V 3 u).card) z0
      exact ⟨z, mem_erase.mpr ⟨ne, hz⟩⟩)
  rw [card_erase_of_mem hz0, hZ] at this
  omega

/-- **I.5.** `Y` acyclic, no arc from `Z` into `X` or into the tail ancestors `oSet`: then no arc
from `Z` into `Y`. With `A = aSet`, a return `z → a` makes `a` deep in `A`, so `a` omits at most two
labels of `Z`; an acyclic `Z` sends every sink back into such rows (Fact C covers `Z` by at most
four labels), a bank `Z` makes `a` omit `q - 1`. -/
theorem acycA_finish (free : QFree D V q) (hq : 8 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 1)
    (hu : u ∈ V) (hY : (layer D V 2 u).card = q + 1) (hZ : (layer D V 3 u).card = q + 1)
    (hW : (layer D V 4 u).card = q) (acY : QFree D (layer D V 2 u) (q + 1))
    (noX : ∀ z ∈ layer D V 3 u, ∀ x ∈ outN D V u, ¬ D z x = true)
    (noO : ∀ z ∈ layer D V 3 u, ∀ o ∈ oSet D V u, ¬ D z o = true) :
    ∀ z ∈ layer D V 3 u, ∀ y ∈ layer D V 2 u, ¬ D z y = true := by
  classical
  have YV : layer D V 2 u ⊆ V := layer_subset
  have ZV : layer D V 3 u ⊆ V := layer_subset
  have AV : aSet D V u ⊆ V := aSet_V
  have acA : QFree D (aSet D V u) (q + 1) := acY.mono_set aSet_subset
  have cA : (aSet D V u).card ≤ q + 1 := by
    have := card_le_card (aSet_subset (D := D) (V := V) (u := u))
    omega
  have deepOm : ∀ a ∈ aSet D V u, Deep D (aSet D V u) (q - 1) a →
      (om D (layer D V 3 u) a).card ≤ 2 := by
    intro a ha dp
    have h1 := deep_heads acA cA ha dp
    have c := split_count (a_cover free hu (by omega) ha)
    rw [reg a (AV ha)] at c
    have e := om_card (D := D) (layer D V 3 u) a
    omega
  have land : ∀ z ∈ layer D V 3 u, ∀ y ∈ layer D V 2 u, D z y = true →
      y ∈ aSet D V u ∧ Deep D (aSet D V u) (q - 1) y := by
    intro z hz y hy zy
    have yA : y ∈ aSet D V u := mem_sdiff.mpr ⟨hy, fun ho => noO z hz y ho zy⟩
    exact ⟨yA, return_deep (m := 1) free AV yA (fun s sA sk =>
      .step (ZV hz) (mem_outN.mp (asink_full free (by omega) reg hu hZ sA (fun a ha => sk a ha) hz)).2
        (.refl z)) zy⟩
  rcases split_bank free (by omega) ZV hZ with cycZ | ⟨acZ, -⟩
  · intro z hz y hy zy
    obtain ⟨yA, dp⟩ := land z hz y hy zy
    have oc := oncyc_of_deg (free.mono_set ZV) (fun v hv => (cycZ v hv).ge) (by omega) hz
    have c1 := cyc_omit (b := 1) free ZV oc (.step (YV hy) zy (.refl y)) (by omega)
    have := deepOm y yA dp
    omega
  · exfalso
    set T := (aSet D V u).filter (fun a => Deep D (aSet D V u) (q - 1) a) with hT
    have cover : layer D V 3 u ⊆ T.biUnion (om D (layer D V 3 u)) := by
      intro z hz
      obtain ⟨s, sZ, sk, m, -, walk⟩ := reach_sink_of_card acZ (by omega) hz
      have notall : ¬ outN D V s ⊆ layer D V 4 u := by
        intro h
        have := card_le_card h
        rw [reg s (ZV sZ)] at this
        omega
      obtain ⟨v, hv, vW⟩ := not_subset.mp notall
      obtain ⟨vV, sv⟩ := mem_outN.mp hv
      rcases z_heads free (by omega) hu sZ sv vV with hx | hy | hz' | hw
      · exact (noX s sZ v hx sv).elim
      · obtain ⟨vA, dp⟩ := land s sZ v hy sv
        have small : (om D (layer D V 3 u) v).card + 0 + 2 ≤ q := by
          have := deepOm v vA dp
          omega
        exact mem_biUnion.mpr ⟨v, mem_filter.mpr ⟨vA, dp⟩,
          fact_C free ZV vV sv (.refl v) small hz walk⟩
      · exact (sk v hz' sv).elim
      · exact (vW hw).elim
    have cT : T.card ≤ 2 := by
      by_cases ne : T.Nonempty
      · have := (deep_bound acA cA (by omega : 1 ≤ q - 1) (T := T) (filter_subset _ _)
          (fun a ha => (mem_filter.mp ha).2) (empty_subset _)
          (fun s hs => absurd hs (Finset.notMem_empty s)) ne).1
        omega
      · rw [not_nonempty_iff_eq_empty] at ne
        rw [ne, card_empty]
        omega
    have sum : ∑ a ∈ T, (om D (layer D V 3 u) a).card ≤ T.card * 2 := by
      have := sum_le_card_nsmul T (fun a => (om D (layer D V 3 u) a).card) 2
        (fun a ha => deepOm a (mem_filter.mp ha).1 (mem_filter.mp ha).2)
      rw [smul_eq_mul] at this
      exact this
    have c1 := card_le_card cover
    have c2 := card_biUnion_le (s := T) (t := om D (layer D V 3 u))
    omega

/-- **I.3.** `Y` and `X` acyclic: no arc from `Z` into `X` or into `oSet`. -/
theorem xacyc_part (free : QFree D V q) (hq : 8 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 1)
    (hu : u ∈ V) (hY : (layer D V 2 u).card = q + 1) (hZ : (layer D V 3 u).card = q + 1)
    (acY : QFree D (layer D V 2 u) (q + 1)) (acX : QFree D (outN D V u) (q + 1)) :
    (∀ z ∈ layer D V 3 u, ∀ x ∈ outN D V u, ¬ D z x = true) ∧
      (∀ z ∈ layer D V 3 u, ∀ o ∈ oSet D V u, ¬ D z o = true) := by
  classical
  have XV : outN D V u ⊆ V := outN_subset
  have YV : layer D V 2 u ⊆ V := layer_subset
  have ZV : layer D V 3 u ⊆ V := layer_subset
  have AV : aSet D V u ⊆ V := aSet_V
  have cX : (outN D V u).card = q + 1 := reg u hu
  have acA : QFree D (aSet D V u) (q + 1) := acY.mono_set aSet_subset
  have cAle : (aSet D V u).card ≤ q + 1 := by
    have := card_le_card (aSet_subset (D := D) (V := V) (u := u))
    omega
  -- a `(q - 1)`-deep row of `X`, in particular a target, omits at most two labels of `Y`
  have deepOm2 : ∀ x ∈ outN D V u, Deep D (outN D V u) (q - 1) x →
      (om D (layer D V 2 u) x).card ≤ 2 := by
    intro x hx dp
    have h := deep_heads acX cX.le hx dp
    have acct := x_acct free (by omega) reg hu hx
    omega
  have tgtOm : ∀ y ∈ layer D V 2 u, ∀ x ∈ outN D V u, D y x = true →
      (om D (layer D V 2 u) x).card ≤ 2 ∧ Deep D (outN D V u) (q - 1) x := by
    intro y hy x hx yx
    have dp := tgt_deep1 free (by omega) reg hu hY hy hx yx
    exact ⟨deepOm2 x hx dp, dp⟩
  have tailY : ∀ {o t j : ℕ}, o ∈ layer D V 2 u → Walk D (layer D V 2 u) o t j → t ∈ layer D V 2 u :=
    fun oY w => by
      rcases w.end_mem_or with e | h
      · rw [e]; exact oY
      · exact h
  -- `|O| ≤ 4`
  set TX := (outN D V u).filter (fun x => Deep D (outN D V u) (q - 1) x) with hTX
  have cTX : TX.card ≤ 2 := by
    by_cases ne : TX.Nonempty
    · have := (deep_bound acX cX.le (by omega : 1 ≤ q - 1) (T := TX) (filter_subset _ _)
        (fun a ha => (mem_filter.mp ha).2) (empty_subset _)
        (fun s hs => absurd hs (Finset.notMem_empty s)) ne).1
      omega
    · rw [not_nonempty_iff_eq_empty] at ne
      rw [ne, card_empty]
      omega
  have Ocover : oSet D V u ⊆ TX.biUnion (om D (layer D V 2 u)) := by
    intro o ho
    obtain ⟨oY, t, ⟨x, hx, tx⟩, j, w⟩ := mem_oSet.mp ho
    obtain ⟨om2, dp⟩ := tgtOm t (tailY oY w) x hx tx
    exact mem_biUnion.mpr ⟨x, mem_filter.mpr ⟨hx, dp⟩,
      fact_C free YV (XV hx) tx (.refl x) (by omega) oY w⟩
  have cO : (oSet D V u).card ≤ 4 := by
    have c1 := card_le_card Ocover
    have c2 := card_biUnion_le (s := TX) (t := om D (layer D V 2 u))
    have c3 := sum_le_card_nsmul TX (fun a => (om D (layer D V 2 u) a).card) 2
      (fun a ha => deepOm2 a (mem_filter.mp ha).1 (mem_filter.mp ha).2)
    rw [smul_eq_mul] at c3
    omega
  have cA : q - 3 ≤ (aSet D V u).card := by
    have := oa_card (D := D) (V := V) (u := u)
    omega
  obtain ⟨sA, sAA, sAk⟩ := exists_sink acA (card_pos.mp (by omega)) cAle
  have fullA := asink_full free (by omega) reg hu hZ sAA sAk
  refine ⟨?_, ?_⟩
  · -- no arc `Z → X`: the target would be `(q - 2)`-deep, yet omit every row of `A` near a sink
    intro z hz x hx zx
    have dp : Deep D (outN D V u) (q - 2) x := return_deep (m := 2) free XV hx (fun s sX sk =>
      .step (AV sAA) (xsink_full1 free (by omega) reg hu hY sX sk (aSet_subset sAA))
        (.step (ZV hz) (mem_outN.mp (fullA hz)).2 (.refl z))) zx
    have h3 := deep_heads acX cX.le hx dp
    have acct := x_acct free (by omega) reg hu hx
    obtain ⟨N, NA, cN, hN⟩ := near_exists acA cAle (t := q - 2) (by omega)
    have sub : N ⊆ om D (layer D V 2 u) x := by
      intro a ha
      have aA := NA ha
      obtain ⟨s, sA, sk, k, hk, w⟩ := not_deep (hN a ha)
      refine mem_om.mpr ⟨aSet_subset aA, fun xa => ?_⟩
      have full := asink_full free (by omega) reg hu hZ sA (fun b hb => sk b hb) hz
      exact free x (k + 1 + 1 + 1) (by omega) (by omega)
        (((Walk.step (AV aA) xa (w.mono AV)).snoc (ZV hz) (mem_outN.mp full).2).snoc (XV hx) zx)
    have := card_le_card sub
    omega
  · -- no arc `Z → O`: a row of `O` reaches its tail in one step, then all of `Z` within five
    intro z hz o ho zo
    obtain ⟨oY, t, ⟨x, hx, tx⟩, i, w⟩ := mem_oSet.mp ho
    have tY := tailY oY w
    obtain ⟨om2, dp⟩ := tgtOm t tY x hx tx
    have hi : i ≤ 1 := by
      by_contra hi
      obtain ⟨f, f0, fi, hf⟩ := w.toFun
      have fY : ∀ j, j ≤ i → f j ∈ layer D V 2 u := by
        intro j hj
        rcases Nat.eq_zero_or_pos j with rfl | hp
        · rw [f0]; exact oY
        · have := (hf (j - 1) (by omega)).1
          rwa [show j - 1 + 1 = j by omega] at this
      have inom : ∀ j, j ≤ i → f j ∈ om D (layer D V 2 u) x := by
        intro j hj
        have wj := walk_between (D := D) (W := layer D V 2 u) (f := f) (m := i)
          (fun k hk => hf k hk) (i := j) (j := i) hj le_rfl
        rw [fi] at wj
        exact fact_C free YV (XV hx) tx (.refl x) (by omega) (fY j hj) wj
      have dist : ∀ a b, a < b → b ≤ i → b - a ≤ 2 → f a ≠ f b := by
        intro a b hab hb hd e
        have wab := walk_between (D := D) (W := layer D V 2 u) (f := f) (m := i)
          (fun k hk => hf k hk) (i := a) (j := b) hab.le hb
        rw [e] at wab
        exact acY _ (b - a) (by omega) (by omega) wab
      have sub : ({f (i - 2), f (i - 1), f i} : Finset ℕ) ⊆ om D (layer D V 2 u) x := by
        intro a ha
        simp only [mem_insert, mem_singleton] at ha
        rcases ha with h | h | h
        · rw [h]; exact inom _ (by omega)
        · rw [h]; exact inom _ (by omega)
        · rw [h]; exact inom _ le_rfl
      have c := card_le_card sub
      rw [card_insert_of_notMem, card_pair (dist (i - 1) i (by omega) le_rfl (by omega))] at c
      · omega
      · simp only [mem_insert, mem_singleton, not_or]
        exact ⟨dist (i - 2) (i - 1) (by omega) (by omega) (by omega),
          dist (i - 2) i (by omega) le_rfl (by omega)⟩
    have xt : ¬ D x t = true := fun a => digonfree free (by omega) (YV tY) (XV hx) tx a
    have tO : t ∈ oSet D V u := tail_o tY ⟨x, hx, tx⟩
    have oneA : ∀ a ∈ aSet D V u, ∀ b ∈ aSet D V u, ¬ D x a = true → ¬ D x b = true → a = b := by
      intro a ha b hb xa xb
      by_contra ne
      have ta : t ≠ a := fun e => (mem_sdiff.mp ha).2 (by rw [← e]; exact tO)
      have tb : t ≠ b := fun e => (mem_sdiff.mp hb).2 (by rw [← e]; exact tO)
      have sub : ({t, a, b} : Finset ℕ) ⊆ om D (layer D V 2 u) x := by
        intro c hc
        simp only [mem_insert, mem_singleton] at hc
        rcases hc with h | h | h
        · rw [h]; exact mem_om.mpr ⟨tY, xt⟩
        · rw [h]; exact mem_om.mpr ⟨aSet_subset ha, xa⟩
        · rw [h]; exact mem_om.mpr ⟨aSet_subset hb, xb⟩
      have c := card_le_card sub
      rw [card_insert_of_notMem, card_pair ne] at c
      · omega
      · simp [ta, tb]
    obtain ⟨s, sA, sk, sb⟩ := reach_sink_two AV acA cAle (by omega) oneA
    have fullS := asink_full free (by omega) reg hu hZ sA sk
    have tb : t ∈ ball D V o i := mem_ball.mpr ⟨YV tY, i, le_rfl, w.mono YV⟩
    have xb : x ∈ ball D V o (i + 1) := ball_step tb (XV hx) tx
    have zb : z ∈ ball D V o (i + 1 + (2 + 1)) :=
      ball_trans xb (ball_trans sb (ball_arc (ZV hz) (mem_outN.mp (fullS hz)).2))
    exact no_back_arc free (YV oY) (ball_mono_radius (by omega) zb) (by omega : 5 + 1 ≤ q) zo

/-- **I.4.** `Y` acyclic, `X` a bank: no arc from `Z` into `X` or into `oSet`. Every head of `u`
omits exactly one label of `Y`; a tail of `x` is omitted by the `q - 1` rows of `X` after `x`, a
`Y`-parent of a row of `Z` returning to `x` by `q - 2` of them, so all such labels coincide. -/
theorem xcyc_part (free : QFree D V q) (hq : 8 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 1)
    (hu : u ∈ V) (hY : (layer D V 2 u).card = q + 1) (hZ : (layer D V 3 u).card = q + 1)
    (acY : QFree D (layer D V 2 u) (q + 1))
    (cycX : ∀ x ∈ outN D V u, (outN D (outN D V u) x).card = 1) :
    (∀ z ∈ layer D V 3 u, ∀ x ∈ outN D V u, ¬ D z x = true) ∧
      (∀ z ∈ layer D V 3 u, ∀ o ∈ oSet D V u, ¬ D z o = true) := by
  have XV : outN D V u ⊆ V := outN_subset
  have YV : layer D V 2 u ⊆ V := layer_subset
  have ZV : layer D V 3 u ⊆ V := layer_subset
  have AV : aSet D V u ⊆ V := aSet_V
  have acA : QFree D (aSet D V u) (q + 1) := acY.mono_set aSet_subset
  have cAle : (aSet D V u).card ≤ q + 1 := by
    have := card_le_card (aSet_subset (D := D) (V := V) (u := u))
    omega
  have tailY : ∀ {o t j : ℕ}, o ∈ layer D V 2 u → Walk D (layer D V 2 u) o t j → t ∈ layer D V 2 u :=
    fun oY w => by
      rcases w.end_mem_or with e | h
      · rw [e]; exact oY
      · exact h
  have om1 : ∀ x ∈ outN D V u, (om D (layer D V 2 u) x).card = 1 := by
    intro x hx
    have := x_acct free (by omega) reg hu hx
    rw [cycX x hx, hY] at this
    omega
  have omitOne : ∀ x ∈ outN D V u, ∀ a ∈ layer D V 2 u, ∀ b ∈ layer D V 2 u,
      ¬ D x a = true → ¬ D x b = true → a = b := by
    intro x hx a ha b hb xa xb
    by_contra ne
    have := two_le_card ne (mem_om.mpr ⟨ha, xa⟩) (mem_om.mpr ⟨hb, xb⟩)
    rw [om1 x hx] at this
    omega
  have degX : ∀ v ∈ outN D V u, 1 ≤ (outN D (outN D V u) v).card := fun v hv => (cycX v hv).ge
  have growX : ∀ x ∈ outN D V u, ∀ j, j ≤ q → j + 1 ≤ (ball D (outN D V u) x j).card :=
    fun x hx j hj => LoopCollar.ball_grow (free.mono_set XV) degX hx j hj
  have mark1 : ∀ y ∈ layer D V 2 u, ∀ x ∈ outN D V u, D y x = true →
      q - 2 ≤ (omx D (outN D V u) y).card := by
    intro y hy x hx yx
    have sub : ball D (outN D V u) x (q - 2) ⊆ omx D (outN D V u) y := by
      intro x' hx'
      obtain ⟨x'X, j, hj, w⟩ := mem_ball.mp hx'
      refine mem_omx.mpr ⟨x'X, fun arc => ?_⟩
      exact free y (j + 1 + 1) (by omega) (by omega)
        ((Walk.step (XV hx) yx (w.mono XV)).snoc (YV hy) arc)
    have := card_le_card sub
    have := growX x hx (q - 2) (by omega)
    omega
  have mark2 : ∀ z ∈ layer D V 3 u, ∀ x ∈ outN D V u, D z x = true →
      ∀ p ∈ layer D V 2 u, D p z = true → q - 2 ≤ (omx D (outN D V u) p).card := by
    intro z hz x hx zx p hp pz
    have sub : ball D (outN D V u) x (q - 3) ⊆ omx D (outN D V u) p := by
      intro x' hx'
      obtain ⟨x'X, j, hj, w⟩ := mem_ball.mp hx'
      refine mem_omx.mpr ⟨x'X, fun arc => ?_⟩
      exact free p (j + 1 + 1 + 1) (by omega) (by omega)
        ((Walk.step (ZV hz) pz (.step (XV hx) zx (w.mono XV))).snoc (YV hp) arc)
    have := card_le_card sub
    have := growX x hx (q - 3) (by omega)
    omega
  have uniq : ∀ y1 ∈ layer D V 2 u, ∀ y2 ∈ layer D V 2 u,
      q - 2 ≤ (omx D (outN D V u) y1).card → q - 2 ≤ (omx D (outN D V u) y2).card → y1 = y2 := by
    intro y1 h1 y2 h2 c1 c2
    by_contra ne
    have d : Disjoint (omx D (outN D V u) y1) (omx D (outN D V u) y2) := by
      rw [disjoint_left]
      intro x a b
      obtain ⟨xX, n1⟩ := mem_omx.mp a
      obtain ⟨-, n2⟩ := mem_omx.mp b
      exact ne (omitOne x xX y1 h1 y2 h2 n1 n2)
    have sub : omx D (outN D V u) y1 ∪ omx D (outN D V u) y2 ⊆ outN D V u :=
      union_subset (filter_subset _ _) (filter_subset _ _)
    have := card_le_card sub
    rw [card_union_of_disjoint d, reg u hu] at this
    omega
  by_cases ht : ∃ y0 ∈ layer D V 2 u, ∃ x0 ∈ outN D V u, D y0 x0 = true
  · obtain ⟨y0, hy0, x0, hx0, yx0⟩ := ht
    have m0 := mark1 y0 hy0 x0 hx0 yx0
    have xy0 : ¬ D x0 y0 = true := fun a => digonfree free (by omega) (YV hy0) (XV hx0) yx0 a
    have nopar : ∀ p ∈ layer D V 2 u, ¬ D p y0 = true := by
      intro p hp py
      have ne : p ≠ y0 := fun e => by
        rw [e] at py
        exact loopfree free (by omega) (YV hy0) py
      have xp : D x0 p = true := by
        by_contra xp
        exact ne (omitOne x0 hx0 p hp y0 hy0 xp xy0)
      exact free x0 3 (by norm_num) (by omega)
        (.step (YV hp) xp (.step (YV hy0) py (.step (XV hx0) yx0 (.refl x0))))
    have Oy0 : ∀ o ∈ oSet D V u, o = y0 := by
      intro o ho
      obtain ⟨oY, t, ⟨x, hx, tx⟩, i, w⟩ := mem_oSet.mp ho
      have tY := tailY oY w
      have tt : t = y0 := uniq t tY y0 hy0 (mark1 t tY x hx tx) m0
      rw [tt] at w
      cases i with
      | zero => cases w; rfl
      | succ i =>
        obtain ⟨p, wp, -, py⟩ := w.unsnoc
        exact (nopar p (tailY oY wp) py).elim
    obtain ⟨y1, hy1, ne1⟩ := exists_mem_ne (by omega : 1 < (layer D V 2 u).card) y0
    have y1A : y1 ∈ aSet D V u := mem_sdiff.mpr ⟨hy1, fun h => ne1 (Oy0 y1 h)⟩
    obtain ⟨sA, sAA, sk⟩ := exists_sink acA ⟨y1, y1A⟩ cAle
    have fullA := asink_full free (by omega) reg hu hZ sAA sk
    have sAne : sA ≠ y0 := fun e =>
      (mem_sdiff.mp sAA).2 (by rw [e]; exact tail_o hy0 ⟨x0, hx0, yx0⟩)
    refine ⟨fun z hz x hx zx => ?_, fun z hz o ho zo => ?_⟩
    · exact sAne (uniq sA (aSet_subset sAA) y0 hy0
        (mark2 z hz x hx zx sA (aSet_subset sAA) (mem_outN.mp (fullA hz)).2) m0)
    · rw [Oy0 o ho] at zo
      have xs : D x0 sA = true := by
        by_contra xs
        exact sAne (omitOne x0 hx0 sA (aSet_subset sAA) y0 hy0 xs xy0)
      exact free y0 4 (by norm_num) (by omega)
        (.step (XV hx0) yx0 (.step (AV sAA) xs (.step (ZV hz) (mem_outN.mp (fullA hz)).2
          (.step (YV hy0) zo (.refl y0)))))
  · push Not at ht
    have noO : ∀ o ∈ oSet D V u, False := fun o ho => by
      obtain ⟨oY, t, ⟨x, hx, tx⟩, i, w⟩ := mem_oSet.mp ho
      exact ht t (tailY oY w) x hx tx
    refine ⟨fun z hz x hx zx => ?_, fun z _ o ho _ => (noO o ho).elim⟩
    obtain ⟨y1, hy1, sk1⟩ := exists_sink acY (card_pos.mp (by omega)) (by omega)
    have y1A : y1 ∈ aSet D V u := mem_sdiff.mpr ⟨hy1, fun h => noO y1 h⟩
    have full1 := asink_full free (by omega) reg hu hZ y1A (fun a ha => sk1 a (aSet_subset ha))
    have m1 := mark2 z hz x hx zx y1 hy1 (mem_outN.mp (full1 hz)).2
    obtain ⟨y2, hy2, ne2⟩ := exists_mem_ne (by omega : 1 < (layer D V 2 u).card) y1
    obtain ⟨s, sY, sks, m, -, w⟩ := reach_sink_of_card acY (by omega) hy2
    have sA : s ∈ aSet D V u := mem_sdiff.mpr ⟨sY, fun h => noO s h⟩
    have fulls := asink_full free (by omega) reg hu hZ sA (fun a ha => sks a (aSet_subset ha))
    have e : s = y1 := uniq s sY y1 hy1 (mark2 z hz x hx zx s sY (mem_outN.mp (fulls hz)).2) m1
    rw [e] at w
    cases m with
    | zero => cases w; exact ne2 rfl
    | succ m =>
      obtain ⟨p, wp, -, py⟩ := w.unsnoc
      have pY := tailY hy2 wp
      have pne : p ≠ y1 := fun h => by
        rw [h] at py
        exact sk1 y1 hy1 py
      have xy1 : ¬ D x y1 = true := fun a => free z 3 (by norm_num) (by omega)
        (.step (XV hx) zx (.step (YV hy1) a (.step (ZV hz) (mem_outN.mp (full1 hz)).2 (.refl z))))
      have xp : D x p = true := by
        by_contra xp
        exact pne (omitOne x hx p pY y1 hy1 xp xy1)
      exact free z 4 (by norm_num) (by omega)
        (.step (XV hx) zx (.step (YV pY) xp (.step (YV hy1) py
          (.step (ZV hz) (mem_outN.mp (full1 hz)).2 (.refl z)))))

/-- **Profile I (generic, `8 ≤ q`).** `|Y| = |Z| = q + 1`, `|W| = q`: no row of `Z` points to `u`,
into `X` or into `Y`; hence `Z` is a bank complete to `W` (each row of `Z` has exactly one head in
`Z`, its heads lie in `Z ∪ W`, and it points to all of `W`). -/
theorem profileI (free : QFree D V q) (hq : 8 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = q + 1)
    (hu : u ∈ V) (hY : (layer D V 2 u).card = q + 1) (hZ : (layer D V 3 u).card = q + 1)
    (hW : (layer D V 4 u).card = q) :
    (∀ z ∈ layer D V 3 u, ∀ v, (v = u ∨ v ∈ outN D V u ∨ v ∈ layer D V 2 u) → ¬ D z v = true) ∧
    (∀ z ∈ layer D V 3 u, (outN D (layer D V 3 u) z).card = 1) ∧
    (∀ z ∈ layer D V 3 u, outN D V z ⊆ layer D V 3 u ∪ layer D V 4 u) ∧
    (∀ z ∈ layer D V 3 u, layer D V 4 u ⊆ outN D V z) := by
  have XV : outN D V u ⊆ V := outN_subset
  have YV : layer D V 2 u ⊆ V := layer_subset
  have ZV : layer D V 3 u ⊆ V := layer_subset
  have noXY : ∀ z ∈ layer D V 3 u, ∀ v, (v ∈ outN D V u ∨ v ∈ layer D V 2 u) → ¬ D z v = true := by
    rcases split_bank free (by omega) YV hY with cycY | ⟨acY, -⟩
    · exact ycyc_noRet free hq reg hu hY hZ hW cycY
    · have parts : (∀ z ∈ layer D V 3 u, ∀ x ∈ outN D V u, ¬ D z x = true) ∧
          (∀ z ∈ layer D V 3 u, ∀ o ∈ oSet D V u, ¬ D z o = true) := by
        rcases split_bank free (by omega) XV (reg u hu) with cycX | ⟨acX, -⟩
        · exact xcyc_part free hq reg hu hY hZ acY cycX
        · exact xacyc_part free hq reg hu hY hZ acY acX
      have noY := acycA_finish free hq reg hu hY hZ hW acY parts.1 parts.2
      intro z hz v hv
      rcases hv with hx | hy
      · exact parts.1 z hz v hx
      · exact noY z hz v hy
  have keep : ∀ z ∈ layer D V 3 u, outN D V z ⊆ layer D V 3 u ∪ layer D V 4 u := by
    intro z hz w hw
    obtain ⟨wV, zw⟩ := mem_outN.mp hw
    rcases z_heads free (by omega) hu hz zw wV with h | h | h | h
    · exact (noXY z hz w (Or.inl h) zw).elim
    · exact (noXY z hz w (Or.inr h) zw).elim
    · exact mem_union_left _ h
    · exact mem_union_right _ h
  have L := TopRowFat.loop_complete free (by omega) ZV hZ (layer_disj (by norm_num : 3 < 4))
    (by omega : (layer D V 4 u).card + 1 ≤ q + 1) (fun z hz => reg z (ZV hz)) keep
  refine ⟨?_, fun z hz => (L z hz).1, keep, fun z hz => (L z hz).2.1⟩
  intro z hz v hv
  rcases hv with e | h
  · subst e
    exact no_back_arc free hu (mem_layer.mp hz).1 (by omega)
  · exact noXY z hz v h

/-! ### Instances at `q = 8`, `r = 9` -/

/-- **Profile 0 at order 72** (`q = 8`, `r = 9`, layers `(9, 8, ·)`). -/
theorem profile0_72 (free : QFree D V 8) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (hY : (layer D V 2 u).card = 9) (hZ : (layer D V 3 u).card = 8) :
    (∀ a ∈ layer D V 2 u, (outN D (layer D V 2 u) a).card = 1) ∧
    (∀ a ∈ layer D V 2 u, outN D V a ⊆ layer D V 2 u ∪ layer D V 3 u) ∧
    (∀ a ∈ layer D V 2 u, layer D V 3 u ⊆ outN D V a) ∧
    (∀ j, 3 ≤ j → j ≤ 4 → ∀ t ∈ layer D V j u, ∀ v,
      (v = u ∨ v ∈ outN D V u ∨ v ∈ layer D V 2 u) → ¬ D t v = true) ∧
    9 ≤ (layer D V 4 u).card :=
  profile0 (q := 8) free le_rfl reg hu hY hZ

/-- **Profile I at order 72** (`q = 8`, `r = 9`, layers `(9, 9, 8)`). -/
theorem profileI_72 (free : QFree D V 8) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (hY : (layer D V 2 u).card = 9) (hZ : (layer D V 3 u).card = 9)
    (hW : (layer D V 4 u).card = 8) :
    (∀ z ∈ layer D V 3 u, ∀ v, (v = u ∨ v ∈ outN D V u ∨ v ∈ layer D V 2 u) → ¬ D z v = true) ∧
    (∀ z ∈ layer D V 3 u, (outN D (layer D V 3 u) z).card = 1) ∧
    (∀ z ∈ layer D V 3 u, outN D V z ⊆ layer D V 3 u ∪ layer D V 4 u) ∧
    (∀ z ∈ layer D V 3 u, layer D V 4 u ⊆ outN D V z) :=
  profileI (q := 8) free le_rfl reg hu hY hZ hW

#print axioms cyc_omit
#print axioms split_bank
#print axioms deep_bound
#print axioms near_exists
#print axioms reach_sink_two
#print axioms x_acct
#print axioms profile0
#print axioms ycyc_noX
#print axioms ycyc_noRet
#print axioms acycA_finish
#print axioms xacyc_part
#print axioms xcyc_part
#print axioms profileI
#print axioms profile0_72
#print axioms profileI_72

end LeanCH.BR.Profiles72
