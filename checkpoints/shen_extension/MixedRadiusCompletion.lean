import checkpoints.shen_extension.ReachLedgerCatalog
import checkpoints.shen_extension.DotFourthPrefixQuadratic_20261118
import checkpoints.shen_extension.ContainerTransfer

/-!
# Mixed-radius quadratic completion, full columns, hereditary deletion

Lean 4.35.0. Every statement is generic in the graph, the order `n`, the cutoff `q`, the host
degree `r`, the comparison degree `d`, the radii and the floors. No number is fixed here.

A *floor* `Floor q d i a` says every `q`-free graph of minimum outdegree `d` has closed `i`-balls
of at least `a` labels; an *order* `Order q d L` says every such nonempty graph has at least `L`
labels. These are the universal suppliers the paper feeds into completions.

* `order_of_noHost`, `order_of_floors`, `floor_zero`: where orders come from (a lower quota, or
  two floors at complementary radii).
* `capacity_regime`: two floors at radii `i + j ≤ q` with `n + 1 < a + b` close every host of
  order `n`.
* `completion` (Appendix 7, general rule): a `q`-free graph of positive minimum outdegree, completed
  by clones to degree `d`, has `K ≥ L` labels and pays `Q + K (a + b) ≤ K (K + 1)`, where `K` is
  the order plus the total deficit and `Q = ∑ g (g + 1)`. The pair count is `ReachLedger.budget`.
* `prefix_completion`: the same at the punctured `(k+1)`-ball of a root: only the last layer
  `c` loses heads, each at most `d + t - r`, the deficit `G` and the missing cells share `c t`,
  and Cauchy gives `G² + c G ≤ c Q`.
* `window_false`: the quadratic test is concave in the deficit, so it suffices to check the two
  ends of the admissible window.
* `Pass`, `pass_false`, `advance`: a floor advances from `F` to `F + 1` at radius `k + 2` once
  every root profile `(x, c)` fails the order or the quadratic test at one of two comparison
  degrees. `Pass` is decidable; the regime is a finite arithmetic check.
* `hereditary` (Appendix 10): deleting `A` from a capped prefix changes the deficits exactly by
  the deleted heads `ℓ`, so `K_A`, `Q_A` are explicit updates and obey the same two bounds.
* `hit_of_floor`, `column_exit`, `column_regime` (Appendix 8): full columns of a prefix have their
  `L`-balls in the complement of the prefix; `e + 2` of them with `e` omissions close the host, and
  the prefix completion supplies them once `e + 2 + c t ≤ t + G`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.MixedRadiusCompletion
open Finset BRq2 BRq3 BR45 BypassRepair ReachLedger
open DotTwoPassShellTransport (shell layer holes fullColumns full_bank_avoids full_columns_bound)
open DotClonePairCompletion (exists_deficiency_completion_bundles bundle_pairs_le_incomparable
  incomparable_card_rows gap_cauchy)

/-! ### Universal suppliers -/

/-- Every `q`-free graph of minimum outdegree `d` has closed `i`-balls of at least `a` labels. -/
def Floor (q d i a : ℕ) : Prop :=
  ∀ (F : CH.Digraph) (U : Finset ℕ), QFree F U q → (∀ x ∈ U, d ≤ (outN F U x).card) →
    ∀ x ∈ U, a ≤ (ball F U x i).card

/-- Every nonempty `q`-free graph of minimum outdegree `d` has at least `L` labels. -/
def Order (q d L : ℕ) : Prop :=
  ∀ (F : CH.Digraph) (U : Finset ℕ), QFree F U q → (∀ x ∈ U, d ≤ (outN F U x).card) →
    U.Nonempty → L ≤ U.card

theorem floor_zero {q d i : ℕ} : Floor q d i 0 := fun _ _ _ _ _ _ => Nat.zero_le _

theorem Floor.weaken {q d i a a' : ℕ} (h : Floor q d i a) (le : a' ≤ a) : Floor q d i a' :=
  fun F U free deg x hx => le.trans (h F U free deg x hx)

theorem Order.weaken {q d L L' : ℕ} (h : Order q d L) (le : L' ≤ L) : Order q d L' :=
  fun F U free deg ne => le.trans (h F U free deg ne)

theorem order_of_noHost {q d : ℕ} (none : NoHost q d) : Order q d (q*d+1) := by
  intro F U free deg ne
  by_contra! small
  exact none F U ne (by omega) free deg

theorem order_of_floors {q d i j a b : ℕ} (hij : i + j ≤ q) (fi : Floor q d i a)
    (fj : Floor q d j b) : Order q d (a + b - 1) := by
  intro F U free deg ne
  have := card_ge_of_two_balls free hij (fi F U free deg) (fj F U free deg) ne
  omega

/-- **Capacity regime.** Floors `a`, `b` at radii `i + j ≤ q` close every host of order `n` with
`n + 1 < a + b`. -/
theorem capacity_regime {D : CH.Digraph} {V : Finset ℕ} {q r n i j a b : ℕ}
    (free : QFree D V q) (degree : ∀ v ∈ V, r ≤ (outN D V v).card) (size : V.card = n)
    (pos : 0 < n) (hij : i + j ≤ q) (fi : Floor q r i a) (fj : Floor q r j b)
    (arith : n + 1 < a + b) : False := by
  have := order_of_floors hij fi fj D V free degree (card_pos.mp (by omega))
  omega

/-! ### The completion (Appendix 7, general rule) -/

/-- **Completion.** Clone-complete a `q`-free graph of positive minimum outdegree to degree `d`.
The completion has `K = |V| + ∑ g` labels, at least the universal order `L`, and its clone bundles
are gaps of the mixed `(i, j)` ledger, so `Q + K (a + b) ≤ K (K + 1)` with `Q = ∑ g (g + 1)`. -/
theorem completion {q d i j a b L : ℕ} (hij : i + j ≤ q) (order : Order q d L)
    (fi : Floor q d i a) (fj : Floor q d j b) {D : CH.Digraph} {V : Finset ℕ}
    (free : QFree D V q) (live : ∀ x ∈ V, 1 ≤ (outN D V x).card) (ne : V.Nonempty) :
    L ≤ V.card + ∑ x ∈ V, (d - (outN D V x).card) ∧
    ∑ x ∈ V, (d - (outN D V x).card) * (d - (outN D V x).card + 1)
      + (V.card + ∑ x ∈ V, (d - (outN D V x).card)) * (a + b)
      ≤ (V.card + ∑ x ∈ V, (d - (outN D V x).card))
        * (V.card + ∑ x ∈ V, (d - (outN D V x).card) + 1) := by
  classical
  obtain ⟨F, U, f, p, hF, hm, hc, hn, hp, hedge, hBU, hproj⟩ :=
    exists_deficiency_completion_bundles (d := d) free live
  have hU := hn ne
  have hQ := bundle_pairs_le_incomparable (r := max i j) free hp hedge (by omega) hBU hproj
  rw [incomparable_card_rows] at hQ
  have rows : ∀ x ∈ U, (U \ (ball F U x (max i j) ∪ reverseBall F U x (max i j))).card
      ≤ (gap F U i j x).card := by
    intro x _
    apply card_le_card
    intro y hy
    obtain ⟨hyU, hn'⟩ := mem_sdiff.mp hy
    exact mem_gap.mpr ⟨hyU,
      fun w => hn' (mem_union_left _ (ball_mono_radius (Nat.le_max_left _ _) w)),
      fun w => hn' (mem_union_right _ (mem_filter.mpr ⟨hyU, ball_mono_radius (Nat.le_max_right _ _) w⟩))⟩
  have hsum := hQ.trans (sum_le_sum rows)
  have spend := budget hF hij (fi F U hF hm) (fj F U hF hm)
  rw [← hc]
  exact ⟨order F U hF hm hU, by omega⟩

/-- **Prefix completion.** At a root `u` with shell `t = |shell (k+1)| < r`, the punctured
`(k+1)`-ball `U` (of `m` labels, last layer `c`) completes to degree `d ≤ r` with deficit `G`:
`G ≤ c (d + t - r)`, `G` and the missing cells share `c t`, `L ≤ m + G`, Cauchy `G² + c G ≤ c Q`,
and the mixed pair bound. -/
theorem prefix_completion {q r d i j a b L k u : ℕ} (hij : i + j ≤ q) (order : Order q d L)
    (fi : Floor q d i a) (fj : Floor q d j b) (hd : d ≤ r) {D : CH.Digraph} {V : Finset ℕ}
    (free : QFree D V q) (degree : ∀ v ∈ V, r ≤ (outN D V v).card) (hu : u ∈ V)
    (hk : k + 2 ≤ q) (ht : (shell D V (k+1) u).card < r) :
    ∃ G Q : ℕ,
      G ≤ (layer D V (k+1) u).card * (d + (shell D V (k+1) u).card - r) ∧
      G + holes D V (k+1) u ≤ (layer D V (k+1) u).card * (shell D V (k+1) u).card ∧
      L ≤ ((ball D V u (k+1)).erase u).card + G ∧
      G * G + (layer D V (k+1) u).card * G ≤ (layer D V (k+1) u).card * Q ∧
      Q + (((ball D V u (k+1)).erase u).card + G) * (a + b) ≤
        (((ball D V u (k+1)).erase u).card + G) * (((ball D V u (k+1)).erase u).card + G + 1) := by
  classical
  have pg := DotFourthPrefixQuadratic.prefix_gap_budget free degree hu (by omega : 1 ≤ r) hk ht
  dsimp only at pg
  obtain ⟨hne, hret, hSU, hz, hbudget⟩ := pg
  have hUV : (ball D V u (k+1)).erase u ⊆ V := (erase_subset _ _).trans ball_subset
  have rows := minOut_prefix_erase (d := r - (shell D V (k+1) u).card) free hu
    (show (k+1)+1 ≤ q by omega) degree
    (by change _ + (shell D V (k+1) u).card ≤ r; omega)
  obtain ⟨lower, pairs⟩ := completion (d := d) hij order fi fj (free.mono_set hUV) hret hne
  have zero : ∀ v ∈ (ball D V u (k+1)).erase u, v ∉ layer D V (k+1) u →
      d - (outN D ((ball D V u (k+1)).erase u) v).card = 0 := by
    intro v hv hn
    have := hz v (mem_sdiff.mpr ⟨hv, hn⟩)
    omega
  have sG : ∑ v ∈ layer D V (k+1) u, (d - (outN D ((ball D V u (k+1)).erase u) v).card)
      = ∑ v ∈ (ball D V u (k+1)).erase u, (d - (outN D ((ball D V u (k+1)).erase u) v).card) :=
    sum_subset hSU zero
  have sQ : ∑ v ∈ layer D V (k+1) u, (d - (outN D ((ball D V u (k+1)).erase u) v).card)
        * (d - (outN D ((ball D V u (k+1)).erase u) v).card + 1)
      = ∑ v ∈ (ball D V u (k+1)).erase u, (d - (outN D ((ball D V u (k+1)).erase u) v).card)
        * (d - (outN D ((ball D V u (k+1)).erase u) v).card + 1) :=
    sum_subset hSU (fun v hv hn => by simp [zero v hv hn])
  have cap : ∑ v ∈ layer D V (k+1) u, (d - (outN D ((ball D V u (k+1)).erase u) v).card)
      ≤ ∑ _v ∈ layer D V (k+1) u, (d + (shell D V (k+1) u).card - r) := by
    refine sum_le_sum (fun v hv => ?_)
    have := rows v (hSU hv)
    omega
  rw [sum_const, smul_eq_mul] at cap
  have below : ∑ v ∈ (ball D V u (k+1)).erase u, (d - (outN D ((ball D V u (k+1)).erase u) v).card)
      ≤ ∑ v ∈ (ball D V u (k+1)).erase u, (r - (outN D ((ball D V u (k+1)).erase u) v).card) :=
    sum_le_sum (fun v _ => by omega)
  have cauchy := gap_cauchy (layer D V (k+1) u)
    (fun v => d - (outN D ((ball D V u (k+1)).erase u) v).card)
  rw [sG, sQ, pow_two] at cauchy
  exact ⟨_, _, by omega, by omega, lower, cauchy, pairs⟩

/-! ### The arithmetic window -/

/-- The quadratic test is violated at deficit `G`: Cauchy and the pair bound cannot both hold. -/
def Pos (c m s G : ℕ) : Prop :=
  c * ((m + G) * (m + G + 1)) < G * G + c * G + c * ((m + G) * s)

instance (c m s G : ℕ) : Decidable (Pos c m s G) := inferInstanceAs (Decidable (_ < _))

/-- **Window.** The test `G² + c G + c K s - c K (K + 1)` is concave in `G` (leading coefficient
`1 - c`), so it is positive on a whole window once it is positive at both ends. -/
theorem window_false {c m s G Q G0 G1 : ℕ} (h0 : G0 ≤ G) (h1 : G ≤ G1) (hc : 1 ≤ c)
    (cauchy : G * G + c * G ≤ c * Q) (pairs : Q + (m + G) * s ≤ (m + G) * (m + G + 1))
    (e0 : Pos c m s G0) (e1 : Pos c m s G1) : False := by
  unfold Pos at e0 e1
  have hP : c * Q + c * ((m + G) * s) ≤ c * ((m + G) * (m + G + 1)) := by
    have := Nat.mul_le_mul_left c pairs
    rwa [Nat.mul_add] at this
  have cz : (G:ℤ) * G + c * G ≤ c * Q := by exact_mod_cast cauchy
  have pz : (c:ℤ) * Q + c * ((m + G) * s) ≤ c * ((m + G) * (m + G + 1)) := by exact_mod_cast hP
  have e0z : (c:ℤ) * ((m + G0) * (m + G0 + 1)) < G0 * G0 + c * G0 + c * ((m + G0) * s) := by
    exact_mod_cast e0
  have e1z : (c:ℤ) * ((m + G1) * (m + G1 + 1)) < G1 * G1 + c * G1 + c * ((m + G1) * s) := by
    exact_mod_cast e1
  have h0z : (G0:ℤ) ≤ G := by exact_mod_cast h0
  have h1z : (G:ℤ) ≤ G1 := by exact_mod_cast h1
  have hcz : (1:ℤ) ≤ c := by exact_mod_cast hc
  have fG : (G:ℤ) * G + c * G + c * ((m + G) * s) - c * ((m + G) * (m + G + 1)) ≤ 0 := by linarith
  have key : ((G1:ℤ) - G0) * ((G:ℤ) * G + c * G + c * ((m + G) * s) - c * ((m + G) * (m + G + 1)))
      = ((G1:ℤ) - G) * ((G0:ℤ) * G0 + c * G0 + c * ((m + G0) * s) - c * ((m + G0) * (m + G0 + 1)))
        + ((G:ℤ) - G0) * ((G1:ℤ) * G1 + c * G1 + c * ((m + G1) * s) - c * ((m + G1) * (m + G1 + 1)))
        + ((c:ℤ) - 1) * ((G1:ℤ) - G0) * ((G:ℤ) - G0) * ((G1:ℤ) - G) := by ring
  have curv : 0 ≤ ((c:ℤ) - 1) * ((G1:ℤ) - G0) * ((G:ℤ) - G0) * ((G1:ℤ) - G) := by
    apply mul_nonneg (mul_nonneg (mul_nonneg _ _) _) _ <;> linarith
  have a0 : (G1:ℤ) - G ≤ ((G1:ℤ) - G) *
      ((G0:ℤ) * G0 + c * G0 + c * ((m + G0) * s) - c * ((m + G0) * (m + G0 + 1))) := by
    nlinarith
  have a1 : (G:ℤ) - G0 ≤ ((G:ℤ) - G0) *
      ((G1:ℤ) * G1 + c * G1 + c * ((m + G1) * s) - c * ((m + G1) * (m + G1 + 1))) := by
    nlinarith
  have lhs : ((G1:ℤ) - G0) * ((G:ℤ) * G + c * G + c * ((m + G) * s) - c * ((m + G) * (m + G + 1)))
      ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) fG
  rcases eq_or_lt_of_le (h0z.trans h1z) with e | lt
  · have g0 : (G:ℤ) = G0 := le_antisymm (by linarith) h0z
    rw [g0] at fG
    linarith
  · linarith

/-- One comparison test at a root profile: `x = |ball (k+1)|`, layer `c`, target `F` for
`|ball (k+2)|`. Either the completion is below the order `L`, or the quadratic test fails at both
ends of the deficit window `[L + 1 - x, c (d + F - x - r)]`. -/
def Pass (x c F r d L s : ℕ) : Prop :=
  c * (d + (F - x) - r) + x < L + 1 ∨
    (1 ≤ c ∧ Pos c (x - 1) s (L + 1 - x) ∧ Pos c (x - 1) s (c * (d + (F - x) - r)))

instance (x c F r d L s : ℕ) : Decidable (Pass x c F r d L s) := by
  unfold Pass
  infer_instance

/-- A passing profile closes the prefix completion. -/
theorem pass_false {x c t F r d L s m G Q : ℕ} (hm : m + 1 = x) (ht : t + x ≤ F)
    (hG : G ≤ c * (d + t - r)) (hL : L ≤ m + G) (cauchy : G * G + c * G ≤ c * Q)
    (pairs : Q + (m + G) * s ≤ (m + G) * (m + G + 1)) (pass : Pass x c F r d L s) : False := by
  have mono : c * (d + t - r) ≤ c * (d + (F - x) - r) := Nat.mul_le_mul_left c (by omega)
  have xm : x - 1 = m := by omega
  rcases pass with low | ⟨hc, e0, e1⟩
  · omega
  · rw [xm] at e0 e1
    exact window_false (G0 := L + 1 - x) (G1 := c * (d + (F - x) - r)) (by omega) (by omega)
      hc cauchy pairs e0 e1

/-- **Floor advance.** Floors `p` at radius `k` and `β` at radius `k + 1`, a target `F` within one
degree of `β`, and two comparison suppliers (degrees `d, d' ≤ r` with orders and mixed floors).
If every root profile passes one of the two tests, every `q`-free graph of degree `r` has
`|ball (k + 2)| ≥ F + 1`. -/
theorem advance {q r k p β F d L i j a b d' L' i' j' a' b' : ℕ}
    (inner : Floor q r k p) (outer : Floor q r (k+1) β) (hk : k + 2 ≤ q) (narrow : F < β + r)
    (hd : d ≤ r) (hij : i + j ≤ q) (order : Order q d L) (fi : Floor q d i a) (fj : Floor q d j b)
    (hd' : d' ≤ r) (hij' : i' + j' ≤ q) (order' : Order q d' L') (fi' : Floor q d' i' a')
    (fj' : Floor q d' j' b')
    (arith : ∀ x ∈ Icc β F, ∀ c ∈ range (x - p + 1),
      Pass x c F r d L (a + b) ∨ Pass x c F r d' L' (a' + b')) :
    Floor q r (k+2) (F+1) := by
  classical
  intro D V free degree u hu
  by_contra! small
  have y0 := inner D V free degree u hu
  have x0 := outer D V free degree u hu
  have inc1 : ball D V u k ⊆ ball D V u (k+1) := ball_mono_radius (by omega)
  have inc2 : ball D V u (k+1) ⊆ ball D V u (k+2) := ball_mono_radius (by omega)
  have lay : (layer D V (k+1) u).card + (ball D V u k).card = (ball D V u (k+1)).card := by
    simpa only [layer, Nat.add_sub_cancel] using card_sdiff_add_card_eq_card inc1
  have sh : (shell D V (k+1) u).card + (ball D V u (k+1)).card = (ball D V u (k+2)).card :=
    card_sdiff_add_card_eq_card inc2
  have er : ((ball D V u (k+1)).erase u).card + 1 = (ball D V u (k+1)).card :=
    card_erase_add_one (self_mem_ball hu)
  have ht : (shell D V (k+1) u).card < r := by omega
  have hx : (ball D V u (k+1)).card ∈ Icc β F := mem_Icc.mpr ⟨x0, by omega⟩
  have hc : (layer D V (k+1) u).card ∈ range ((ball D V u (k+1)).card - p + 1) :=
    mem_range.mpr (by omega)
  rcases arith _ hx _ hc with pass | pass
  · obtain ⟨G, Q, hG, -, hL, cauchy, pairs⟩ :=
      prefix_completion hij order fi fj hd free degree hu hk ht
    exact pass_false er (by omega) hG hL cauchy pairs pass
  · obtain ⟨G, Q, hG, -, hL, cauchy, pairs⟩ :=
      prefix_completion hij' order' fi' fj' hd' free degree hu hk ht
    exact pass_false er (by omega) hG hL cauchy pairs pass

/-! ### Hereditary completion (Appendix 10) -/

/-- **Hereditary completion.** In a `q`-free graph `U` of maximum outdegree `r`, delete `A`; the
survivors keep positive outdegree. A survivor's new deficit is exactly `g + ℓ`, with `ℓ` its heads
in `A`. Hence `K_A`, `Q_A` are explicit updates of `K`, `Q`, and they obey the completion bounds. -/
theorem hereditary {q r i j a b L : ℕ} (hij : i + j ≤ q) (order : Order q r L)
    (fi : Floor q r i a) (fj : Floor q r j b) {D : CH.Digraph} {U A : Finset ℕ}
    (free : QFree D U q) (cap : ∀ x ∈ U, (outN D U x).card ≤ r) (hA : A ⊆ U)
    (live : ∀ x ∈ U \ A, 1 ≤ (outN D (U \ A) x).card) (ne : (U \ A).Nonempty) :
    (U \ A).card + ∑ x ∈ U \ A, ((r - (outN D U x).card) + (outN D A x).card)
        + ∑ x ∈ A, (1 + (r - (outN D U x).card))
      = U.card + ∑ x ∈ U, (r - (outN D U x).card) + ∑ x ∈ U \ A, (outN D A x).card ∧
    ∑ x ∈ U \ A, ((r - (outN D U x).card) + (outN D A x).card)
          * ((r - (outN D U x).card) + (outN D A x).card + 1)
        + ∑ x ∈ A, (r - (outN D U x).card) * (r - (outN D U x).card + 1)
      = ∑ x ∈ U, (r - (outN D U x).card) * (r - (outN D U x).card + 1)
        + ∑ x ∈ U \ A, (outN D A x).card * (2 * (r - (outN D U x).card) + (outN D A x).card + 1) ∧
    L ≤ (U \ A).card + ∑ x ∈ U \ A, ((r - (outN D U x).card) + (outN D A x).card) ∧
    ∑ x ∈ U \ A, ((r - (outN D U x).card) + (outN D A x).card)
          * ((r - (outN D U x).card) + (outN D A x).card + 1)
        + ((U \ A).card + ∑ x ∈ U \ A, ((r - (outN D U x).card) + (outN D A x).card)) * (a + b)
      ≤ ((U \ A).card + ∑ x ∈ U \ A, ((r - (outN D U x).card) + (outN D A x).card))
        * ((U \ A).card + ∑ x ∈ U \ A, ((r - (outN D U x).card) + (outN D A x).card) + 1) := by
  classical
  have split : ∀ x ∈ U \ A, r - (outN D (U \ A) x).card
      = (r - (outN D U x).card) + (outN D A x).card := by
    intro x hx
    have h := card_outN_union (D := D) (show Disjoint (U \ A) A from sdiff_disjoint) x
    rw [sdiff_union_of_subset hA] at h
    have := cap x (mem_sdiff.mp hx).1
    omega
  obtain ⟨lower, pairs⟩ := completion (d := r) hij order fi fj
    (free.mono_set sdiff_subset) live ne
  have sq2 : ∑ x ∈ U \ A, (r - (outN D (U \ A) x).card) * (r - (outN D (U \ A) x).card + 1)
      = ∑ x ∈ U \ A, ((r - (outN D U x).card) + (outN D A x).card)
          * ((r - (outN D U x).card) + (outN D A x).card + 1) :=
    sum_congr rfl (fun x hx => by rw [split x hx])
  rw [sq2, sum_congr rfl split] at pairs
  rw [sum_congr rfl split] at lower
  have cardA := card_sdiff_add_card_eq_card hA
  have sg := sum_sdiff hA (f := fun x => r - (outN D U x).card)
  have sq := sum_sdiff hA (f := fun x => (r - (outN D U x).card) * (r - (outN D U x).card + 1))
  have one : ∑ x ∈ A, (1 + (r - (outN D U x).card)) = A.card + ∑ x ∈ A, (r - (outN D U x).card) := by
    rw [sum_add_distrib, sum_const, smul_eq_mul, Nat.mul_one]
  have gl : ∑ x ∈ U \ A, ((r - (outN D U x).card) + (outN D A x).card)
      = ∑ x ∈ U \ A, (r - (outN D U x).card) + ∑ x ∈ U \ A, (outN D A x).card := sum_add_distrib
  have ql : ∑ x ∈ U \ A, ((r - (outN D U x).card) + (outN D A x).card)
          * ((r - (outN D U x).card) + (outN D A x).card + 1)
      = ∑ x ∈ U \ A, (r - (outN D U x).card) * (r - (outN D U x).card + 1)
        + ∑ x ∈ U \ A, (outN D A x).card * (2 * (r - (outN D U x).card) + (outN D A x).card + 1) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun x _ => by ring)
  refine ⟨by omega, by omega, lower, pairs⟩

/-! ### Full columns (Appendix 8) -/

/-- A root at the floor of the `k`-balls: every label of its punctured `(k+1)`-ball has a larger
`k`-ball than the root's punctured one, which is the hitting condition of the full-column rule. -/
theorem hit_of_floor {D : CH.Digraph} {V : Finset ℕ} {k u p : ℕ} (hu : u ∈ V)
    (fl : ∀ y ∈ V, p ≤ (ball D V y k).card) (tight : (ball D V u k).card ≤ p) :
    ∀ y ∈ (ball D V u (k+1)).erase u, ((ball D V u k).erase u).card < (ball D V y k).card := by
  intro y hy
  have e := card_erase_add_one (self_mem_ball hu : u ∈ ball D V u k)
  have := fl y (ball_subset (mem_of_mem_erase hy))
  omega

/-- **Column exit.** Full columns of the `(k+1)`-prefix keep their `L`-balls in the complement of
the punctured prefix. If those balls have at least `M` labels, the complement has at most
`M + e`, and there are `e + 2` full columns with `L + e + 1 ≤ q` and `e (e + 2) ≤ q`, the host
closes. -/
theorem column_exit {D : CH.Digraph} {V : Finset ℕ} {q k L e M u : ℕ} (free : QFree D V q)
    (hu : u ∈ V) (fit : k + 1 + L ≤ q)
    (hit : ∀ y ∈ (ball D V u (k+1)).erase u, ((ball D V u k).erase u).card < (ball D V y k).card)
    (wide : ∀ h ∈ V, M ≤ (ball D V h L).card)
    (room : V.card ≤ ((ball D V u (k+1)).erase u).card + M + e)
    (many : e + 2 ≤ (fullColumns D V (k+1) u).card) (ret : L + e + 1 ≤ q)
    (cyc : e * (e + 2) ≤ q) : False := by
  classical
  have boxes := full_bank_avoids free hu fit hit
  have hCV : fullColumns D V (k+1) u ⊆ V :=
    fun h hh => DotTwoPassShellTransport.shell_subset (mem_filter.mp hh).1
  have hUV : (ball D V u (k+1)).erase u ⊆ V := (erase_subset _ _).trans ball_subset
  refine ShenContainerTransfer.container_false free hCV
    (fun h hh => boxes h hh (self_mem_ball (hCV hh))) boxes ?_ many ret cyc
  intro h hh
  have e1 := card_sdiff_add_card_eq_card (boxes h hh)
  have e2 := card_sdiff_add_card_eq_card hUV
  have := wide h (hCV hh)
  omega

/-- **Column regime.** At a root whose shell `t` is below `r`, the degree-`r` prefix completion
pays `G + holes ≤ c t`, and every nonfull column costs a hole. If every deficit admitted by the
completion bounds has `e + 2 + c t ≤ t + G`, the full columns close the host. -/
theorem column_regime {D : CH.Digraph} {V : Finset ℕ} {q r k L e M u i j a b Lo : ℕ}
    (hij : i + j ≤ q) (order : Order q r Lo) (fi : Floor q r i a) (fj : Floor q r j b)
    (free : QFree D V q) (degree : ∀ v ∈ V, r ≤ (outN D V v).card) (hu : u ∈ V)
    (hk : k + 2 ≤ q) (ht : (shell D V (k+1) u).card < r) (fit : k + 1 + L ≤ q)
    (hit : ∀ y ∈ (ball D V u (k+1)).erase u, ((ball D V u k).erase u).card < (ball D V y k).card)
    (wide : ∀ h ∈ V, M ≤ (ball D V h L).card)
    (room : V.card ≤ ((ball D V u (k+1)).erase u).card + M + e)
    (ret : L + e + 1 ≤ q) (cyc : e * (e + 2) ≤ q)
    (arith : ∀ G Q, Lo ≤ ((ball D V u (k+1)).erase u).card + G →
      G * G + (layer D V (k+1) u).card * G ≤ (layer D V (k+1) u).card * Q →
      Q + (((ball D V u (k+1)).erase u).card + G) * (a + b) ≤
        (((ball D V u (k+1)).erase u).card + G) * (((ball D V u (k+1)).erase u).card + G + 1) →
      G ≤ (layer D V (k+1) u).card * (shell D V (k+1) u).card →
      e + 2 + (layer D V (k+1) u).card * (shell D V (k+1) u).card ≤ (shell D V (k+1) u).card + G) :
    False := by
  obtain ⟨G, Q, -, hh, hL, cauchy, pairs⟩ :=
    prefix_completion (d := r) hij order fi fj le_rfl free degree hu hk ht
  have gain := arith G Q hL cauchy pairs (by omega)
  have cols := full_columns_bound (D := D) (V := V) (R := k+1) (u := u)
  exact column_exit free hu fit hit wide room (by omega) ret cyc

/-- **Two-column cap.** With one omission at most, three full columns are already too many. -/
theorem columns_le_two {D : CH.Digraph} {V : Finset ℕ} {q k L M u : ℕ} (free : QFree D V q)
    (hu : u ∈ V) (fit : k + 1 + L ≤ q) (hL : L + 2 ≤ q) (h3 : 3 ≤ q)
    (hit : ∀ y ∈ (ball D V u (k+1)).erase u, ((ball D V u k).erase u).card < (ball D V y k).card)
    (wide : ∀ h ∈ V, M ≤ (ball D V h L).card)
    (room : V.card ≤ ((ball D V u (k+1)).erase u).card + M + 1) :
    (fullColumns D V (k+1) u).card ≤ 2 := by
  classical
  by_contra! many
  obtain ⟨C, hC, hc⟩ := exists_subset_card_eq (show 3 ≤ (fullColumns D V (k+1) u).card by omega)
  have boxes := full_bank_avoids free hu fit hit
  have hCV : fullColumns D V (k+1) u ⊆ V :=
    fun h hh => DotTwoPassShellTransport.shell_subset (mem_filter.mp hh).1
  have hUV : (ball D V u (k+1)).erase u ⊆ V := (erase_subset _ _).trans ball_subset
  refine ShenFirstStrip.near_full_container_false free hL (hC.trans hCV)
    (fun h hh => boxes h (hC hh) (self_mem_ball (hCV (hC hh)))) (fun h hh => boxes h (hC hh)) ?_
    (by omega) (by omega)
  intro h hh
  have e1 := card_sdiff_add_card_eq_card (boxes h (hC hh))
  have e2 := card_sdiff_add_card_eq_card hUV
  have := wide h (hCV (hC hh))
  omega

/-! ### The endpoint `n + 1 = a + b` -/

/-- At the capacity endpoint every row sits exactly at the floor of both radii. -/
theorem tight_row {D : CH.Digraph} {V : Finset ℕ} {q i j a b : ℕ} (free : QFree D V q)
    (hij : i + j ≤ q) (hi : ∀ v ∈ V, a ≤ (ball D V v i).card)
    (hj : ∀ v ∈ V, b ≤ (ball D V v j).card) (tight : V.card + 1 = a + b) :
    ∀ v ∈ V, (ball D V v i).card = a := by
  have spend := budget free hij hi hj
  rw [← tight] at spend
  have zero : ∑ v ∈ V, ((ball D V v i).card - a) = 0 := by
    have := Nat.mul_comm V.card (V.card + 1)
    omega
  intro v hv
  have := (sum_eq_zero_iff.mp zero) v hv
  have := hi v hv
  omega

/-- Cauchy and the pair bound together forbid the test. -/
theorem not_pos {c m s G Q : ℕ} (cauchy : G * G + c * G ≤ c * Q)
    (pairs : Q + (m + G) * s ≤ (m + G) * (m + G + 1)) : ¬ Pos c m s G := by
  unfold Pos
  have := Nat.mul_le_mul_left c pairs
  rw [Nat.mul_add] at this
  omega

/-- The full-column test at an endpoint profile: the root is at the inner floor (`c + p = x`),
the container leaves `e = n + 1 - x - M` omissions within the cutoff, and every deficit `G`
allowed by the completion leaves `e + 2` full columns. -/
def ColumnPass (x c t n p M Lr q s Lo : ℕ) : Prop :=
  c + p = x ∧ Lr + (n + 1 - x - M) + 1 ≤ q ∧ (n + 1 - x - M) * (n + 1 - x - M + 2) ≤ q ∧
    ∀ G ∈ range (c * t + 1), Lo ≤ x - 1 + G → ¬ Pos c (x - 1) s G →
      n + 1 - x - M + 2 + c * t ≤ t + G

instance (x c t n p M Lr q s Lo : ℕ) : Decidable (ColumnPass x c t n p M Lr q s Lo) := by
  unfold ColumnPass
  infer_instance

/-- **Column endpoint regime.** A host of order `n` with `n + 1 = a + b` for floors at radii
`k + 2` and `j`: every root has `|ball (k+2)| = a`. If every profile `(x, c)` of the `(k+1)`-prefix
passes the comparison test at degree `d`, the degree-`r` test, or the full-column test against the
floor `M` of the `Lr`-balls, the host closes. -/
theorem column_endpoint {D : CH.Digraph} {V : Finset ℕ}
    {q r n k Lr p β M j b d L' i' j' a' b' a : ℕ}
    (free : QFree D V q) (degree : ∀ v ∈ V, r ≤ (outN D V v).card) (size : V.card = n)
    (pos : 0 < n) (hij : k + 2 + j ≤ q) (fa : Floor q r (k+2) a) (fb : Floor q r j b)
    (tight : n + 1 = a + b) (inner : Floor q r k p) (outer : Floor q r (k+1) β)
    (wide : Floor q r Lr M) (fit : k + 1 + Lr ≤ q) (narrow : a < β + r)
    (hd' : d ≤ r) (hij' : i' + j' ≤ q) (order' : Order q d L') (fi' : Floor q d i' a')
    (fj' : Floor q d j' b')
    (arith : ∀ x ∈ Icc β a, ∀ c ∈ range (x - p + 1),
      Pass x c a r d L' (a' + b') ∨ Pass x c a r r n (a + b) ∨
        ColumnPass x c (a - x) n p M Lr q (a + b) n) : False := by
  classical
  have ord : Order q r n := by
    have := order_of_floors hij fa fb
    rwa [show a + b - 1 = n by omega] at this
  obtain ⟨u, hu⟩ := card_pos.mp (show 0 < V.card by omega)
  have exact := tight_row free hij (fa D V free degree) (fb D V free degree) (by omega) u hu
  have y0 := inner D V free degree u hu
  have x0 := outer D V free degree u hu
  have inc1 : ball D V u k ⊆ ball D V u (k+1) := ball_mono_radius (by omega)
  have inc2 : ball D V u (k+1) ⊆ ball D V u (k+2) := ball_mono_radius (by omega)
  have lay : (layer D V (k+1) u).card + (ball D V u k).card = (ball D V u (k+1)).card := by
    simpa only [layer, Nat.add_sub_cancel] using card_sdiff_add_card_eq_card inc1
  have sh : (shell D V (k+1) u).card + (ball D V u (k+1)).card = (ball D V u (k+2)).card :=
    card_sdiff_add_card_eq_card inc2
  have er : ((ball D V u (k+1)).erase u).card + 1 = (ball D V u (k+1)).card :=
    card_erase_add_one (self_mem_ball hu)
  have ht : (shell D V (k+1) u).card < r := by omega
  have hx : (ball D V u (k+1)).card ∈ Icc β a := mem_Icc.mpr ⟨x0, by omega⟩
  have hc : (layer D V (k+1) u).card ∈ range ((ball D V u (k+1)).card - p + 1) :=
    mem_range.mpr (by omega)
  rcases arith _ hx _ hc with pass | pass | ⟨hcp, hret, hcyc, cols⟩
  · obtain ⟨G, Q, hG, -, hL, cauchy, pairs⟩ :=
      prefix_completion hij' order' fi' fj' hd' free degree hu (by omega) ht
    exact pass_false er (by omega) hG hL cauchy pairs pass
  · obtain ⟨G, Q, hG, -, hL, cauchy, pairs⟩ :=
      prefix_completion (d := r) (show k + 2 + j ≤ q from hij) ord fa fb le_rfl free degree hu
        (by omega) ht
    exact pass_false er (by omega) hG hL cauchy pairs pass
  · have tEq : (shell D V (k+1) u).card = a - (ball D V u (k+1)).card := by omega
    have xm : (ball D V u (k+1)).card - 1 = ((ball D V u (k+1)).erase u).card := by omega
    have hit := hit_of_floor hu (inner D V free degree) (show (ball D V u k).card ≤ p by omega)
    refine column_regime (e := n + 1 - (ball D V u (k+1)).card - M) hij ord fa fb free degree hu
      (by omega) ht fit hit (wide D V free degree) (by omega) hret hcyc ?_
    intro G Q hL cauchy pairs hG
    have np := not_pos cauchy pairs
    rw [tEq] at hG ⊢
    rw [xm] at cols
    exact cols G (mem_range.mpr (by omega)) (by omega) np

#print axioms floor_zero
#print axioms order_of_noHost
#print axioms order_of_floors
#print axioms capacity_regime
#print axioms completion
#print axioms prefix_completion
#print axioms window_false
#print axioms pass_false
#print axioms advance
#print axioms hereditary
#print axioms hit_of_floor
#print axioms column_exit
#print axioms column_regime
#print axioms columns_le_two
#print axioms tight_row
#print axioms not_pos
#print axioms column_endpoint
end LeanCH.BR.MixedRadiusCompletion
