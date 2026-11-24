import checkpoints.shen_extension.BoundaryReceiverWitness

/-!
# Mixing the two receiver supports (20 November 2026)

Keep the receiver `z`, the failed least boundary attachment `L` and the full old family `F` fixed. Let `A`
and `B` be old cycles supporting `p → z` and `t → z` (`BoundaryReceiverWitness.on_boundary`), so that
`L ∩ A` and `L ∩ B` are disjoint. Write `G = graph D (insert L F)` and, for a cycle `K`,

  `count K j = [j ∈ K] + q · #(G-parents of j in K)`,

so that the uniform price of `K` gives column `j` the value `count K j / (q+1)`.

* `mix`, `col_mix`, `mix_dual_iff`: the mixture `λ·u_A + (1-λ)·u_B` pays every column, old columns included,
  exactly when `λ·count A j + (1-λ)·count B j ≤ q+1` for every `j`.
* `interval`: exact elimination of `λ ∈ [0,1]`. A paying `λ` exists iff no column fails both prices, and for
  each column `j` failing only `u_A` and each column `k` failing only `u_B` the two ceilings sum to at least
  one. As an inequality this reads
  `(x_j - y_j)(y_k - x_k) ≤ (c - y_j)(y_k - x_k) + (c - x_k)(x_j - y_j)`.
* `half_pays`: the even mixture pays when `count A j + count B j ≤ 2(q+1)` for every `j`.
* `common_failure_is_old`: a column failing both prices lies off `A` and `B` and has two **old** parents in
  `A` or in `B`. At most one new arc enters it, and its tail lies on `L ∩ A` or on `L ∩ B` but not both.
* `receiver_mixture`: on a failed attachment no mixture pays. The obstruction is labelled: a common failing
  column that is an old double receiver, or a pair `j, k` violating the ceiling inequality. Some column also
  has `count A j + count B j > 2(q+1)`.
* `retry_support`: a column failing `u_A` through a new arc `x → j` from `L ∩ A`, with an old parent in `A`
  and an old arc back into `A`. Then either `L` adds exactly the one arc `x → j`, or `A - x + j` is another
  old family cycle. When `x ≠ p` it still supports `p → z`.
-/

namespace LeanCH.BR.Closure.ReceiverMixture
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights
open FirstPacketBarrier MarkedCyclePeeling SharedArcBarrier SharedArcComponentExchange
open EndpointBills

/-! ### One mixing coefficient on `[0,1]` -/

/-- **Exact elimination of a mixing coefficient.** -/
theorem interval {J : Finset ℕ} (x y : ℕ → ℝ) (c : ℝ) :
    (∃ l : ℝ, 0 ≤ l ∧ l ≤ 1 ∧ ∀ j ∈ J, l * x j + (1 - l) * y j ≤ c) ↔
      (∀ j ∈ J, x j ≤ c ∨ y j ≤ c) ∧
        ∀ j ∈ J, ∀ k ∈ J, c < x j → c < y k →
          (x j - y j) * (y k - x k) ≤ (c - y j) * (y k - x k) + (c - x k) * (x j - y j) := by
  classical
  constructor
  · rintro ⟨l, l0, l1, all⟩
    have one : ∀ j ∈ J, x j ≤ c ∨ y j ≤ c := by
      intro j jm
      by_contra! both
      have h := all j jm
      have m0 : 0 < min (x j - c) (y j - c) := lt_min (by linarith [both.1]) (by linarith [both.2])
      have e1 := mul_le_mul_of_nonneg_left (min_le_left (x j - c) (y j - c)) l0
      have e2 := mul_le_mul_of_nonneg_left (min_le_right (x j - c) (y j - c)) (sub_nonneg.mpr l1)
      nlinarith [e1, e2, m0]
    refine ⟨one, fun j jm k km xj yk => ?_⟩
    have yj := (one j jm).resolve_left (not_le.mpr xj)
    have xk := (one k km).resolve_right (not_le.mpr yk)
    have hj := all j jm
    have hk := all k km
    have dj : 0 < x j - y j := by linarith
    have dk : 0 < y k - x k := by linarith
    have e1 : l * (x j - y j) ≤ c - y j := by linarith
    have e2 : (1 - l) * (y k - x k) ≤ c - x k := by linarith
    have f1 := mul_le_mul_of_nonneg_right e1 dk.le
    have f2 := mul_le_mul_of_nonneg_right e2 dj.le
    nlinarith [f1, f2]
  · rintro ⟨one, pair⟩
    by_cases some : (J.filter (fun j => c < x j)).Nonempty
    · obtain ⟨m, mm, low⟩ := (J.filter (fun j => c < x j)).exists_min_image
        (fun j => (c - y j) / (x j - y j)) some
      obtain ⟨mJ, xm⟩ := mem_filter.mp mm
      have ym := (one m mJ).resolve_left (not_le.mpr xm)
      have dm : 0 < x m - y m := by linarith
      set l := (c - y m) / (x m - y m) with hl
      have ld : l * (x m - y m) = c - y m := by rw [hl]; field_simp
      have l0 : 0 ≤ l := div_nonneg (by linarith) dm.le
      have l1 : l ≤ 1 := by rw [hl, div_le_one dm]; linarith
      refine ⟨l, l0, l1, fun j jm => ?_⟩
      by_cases xj : c < x j
      · have yj := (one j jm).resolve_left (not_le.mpr xj)
        have dj : 0 < x j - y j := by linarith
        have le : l ≤ (c - y j) / (x j - y j) := low j (mem_filter.mpr ⟨jm, xj⟩)
        rw [le_div_iff₀ dj] at le
        linarith
      · push Not at xj
        by_cases yj : c < y j
        · have p := pair m mJ j jm xm yj
          have dj : 0 < y j - x j := by linarith
          suffices (x m - y m) * (l * x j + (1 - l) * y j) ≤ (x m - y m) * c by
            exact le_of_mul_le_mul_left this dm
          have expand : (x m - y m) * (l * x j + (1 - l) * y j) =
              (l * (x m - y m)) * x j + ((x m - y m) - l * (x m - y m)) * y j := by ring
          rw [expand, ld]
          nlinarith [p]
        · push Not at yj
          nlinarith [mul_le_mul_of_nonneg_left xj l0,
            mul_le_mul_of_nonneg_left yj (sub_nonneg.mpr l1)]
    · refine ⟨1, zero_le_one, le_rfl, fun j jm => ?_⟩
      have xj : x j ≤ c := by
        by_contra! h
        exact some ⟨j, mem_filter.mpr ⟨jm, h⟩⟩
      linarith

/-! ### The mixed uniform price -/

/-- The count whose quotient by `q+1` is the uniform price of `K` at column `j`. -/
noncomputable def count (q : ℕ) (E : CH.Digraph) (K : Finset ℕ) (j : ℕ) : ℝ :=
  (if j ∈ K then 1 else 0) + q * (inN E K j).card

/-- The mixture of the two uniform supports. -/
noncomputable def mix (q : ℕ) (A B : Finset ℕ) (l : ℝ) (i : ℕ) : ℝ :=
  l * uniform q A i + (1 - l) * uniform q B i

theorem col_mix {q : ℕ} {E : CH.Digraph} {V A B : Finset ℕ} (as : A ⊆ V) (bs : B ⊆ V)
    (l : ℝ) (j : ℕ) :
    realCol q E V (mix q A B l) j = (l * count q E A j + (1 - l) * count q E B j) / ((q : ℝ) + 1) := by
  have inw : realInW E V (mix q A B l) j =
      l * realInW E V (uniform q A) j + (1 - l) * realInW E V (uniform q B) j := by
    unfold realInW mix
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    split_ifs <;> ring
  have lin : realCol q E V (mix q A B l) j =
      l * realCol q E V (uniform q A) j + (1 - l) * realCol q E V (uniform q B) j := by
    rw [realCol, inw, realCol, realCol]
    simp only [mix]
    ring
  rw [lin, col_uniform as, col_uniform bs]
  unfold count
  ring

theorem mass_uniform {q : ℕ} {D : CH.Digraph} {V K : Finset ℕ} (ck : Cycle D V q K) :
    realMass V (uniform q K) = 1 := by
  classical
  unfold realMass uniform
  rw [sum_ite_mem, inter_eq_right.mpr ck.sub, sum_const, nsmul_eq_mul, ck.size]
  push_cast
  field_simp

/-- **The mixture pays every column iff the mixed counts stay below `q+1`.** -/
theorem mix_dual_iff {q : ℕ} {D E : CH.Digraph} {V A B : Finset ℕ} (ca : Cycle D V q A)
    (cb : Cycle D V q B) {l : ℝ} (l0 : 0 ≤ l) (l1 : l ≤ 1) :
    RealDual q E V 1 (mix q A B l) ↔
      ∀ j ∈ V, l * count q E A j + (1 - l) * count q E B j ≤ q + 1 := by
  have den : (0 : ℝ) < q + 1 := by positivity
  constructor
  · intro dual j jv
    have h := dual.columns j jv
    rw [col_mix ca.sub cb.sub, div_le_iff₀ den, one_mul] at h
    exact h
  · intro bills
    refine ⟨fun i _ => ?_, ?_, fun j jv => ?_⟩
    · unfold mix uniform
      have q0 : (0 : ℝ) ≤ 1 / ((q : ℝ) + 1) := by positivity
      split_ifs <;> nlinarith [mul_nonneg l0 q0, mul_nonneg (sub_nonneg.mpr l1) q0]
    · unfold realMass mix
      rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      have ma := mass_uniform ca
      have mb := mass_uniform cb
      unfold realMass at ma mb
      rw [ma, mb]
      ring
    · rw [col_mix ca.sub cb.sub, div_le_iff₀ den, one_mul]
      exact bills j jv

/-- **Exact mixture test.** -/
theorem mixture_iff {q : ℕ} {D E : CH.Digraph} {V A B : Finset ℕ} (ca : Cycle D V q A)
    (cb : Cycle D V q B) :
    (∃ l : ℝ, 0 ≤ l ∧ l ≤ 1 ∧ RealDual q E V 1 (mix q A B l)) ↔
      (∀ j ∈ V, count q E A j ≤ q + 1 ∨ count q E B j ≤ q + 1) ∧
        ∀ j ∈ V, ∀ k ∈ V, (q : ℝ) + 1 < count q E A j → (q : ℝ) + 1 < count q E B k →
          (count q E A j - count q E B j) * (count q E B k - count q E A k) ≤
            ((q + 1) - count q E B j) * (count q E B k - count q E A k) +
              ((q + 1) - count q E A k) * (count q E A j - count q E B j) := by
  rw [← interval]
  constructor
  · rintro ⟨l, l0, l1, dual⟩
    exact ⟨l, l0, l1, (mix_dual_iff ca cb l0 l1).mp dual⟩
  · rintro ⟨l, l0, l1, bills⟩
    exact ⟨l, l0, l1, (mix_dual_iff ca cb l0 l1).mpr bills⟩

/-- **The even mixture.** -/
theorem half_pays {q : ℕ} {D E : CH.Digraph} {V A B : Finset ℕ} (ca : Cycle D V q A)
    (cb : Cycle D V q B) (sum : ∀ j ∈ V, count q E A j + count q E B j ≤ 2 * ((q : ℝ) + 1)) :
    RealDual q E V 1 (mix q A B (1 / 2)) := by
  refine (mix_dual_iff ca cb (by norm_num) (by norm_num)).mpr fun j jv => ?_
  have := sum j jv
  linarith

/-! ### The labels in the actual attachment -/

/-- A count above `q+1` means two parents and no membership. -/
theorem over_count {q : ℕ} (hq : 2 ≤ q) {D E : CH.Digraph} {V K : Finset ℕ} (ck : Cycle D V q K)
    (sub : ∀ a b, E a b = true → D a b = true) {j : ℕ} (big : (q : ℝ) + 1 < count q E K j) :
    j ∉ K ∧ 2 ≤ (inN E K j).card := by
  classical
  have q2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  by_cases jk : j ∈ K
  · exfalso
    have one : (inN E K j).card ≤ 1 := by
      have s : inN E K j ⊆ inN D K j := fun x hx =>
        mem_inN.mpr ⟨(mem_inN.mp hx).1, sub _ _ (mem_inN.mp hx).2⟩
      have := card_le_card s
      have c1 : (inN D K j).card = 1 := ck.incoming j jk
      omega
    have h1 : ((inN E K j).card : ℝ) ≤ 1 := by exact_mod_cast one
    simp only [count, jk, ↓reduceIte] at big
    nlinarith
  · refine ⟨jk, ?_⟩
    by_contra! few
    have h1 : ((inN E K j).card : ℝ) ≤ 1 := by exact_mod_cast (show (inN E K j).card ≤ 1 by omega)
    simp only [count, jk, ↓reduceIte, zero_add] at big
    nlinarith

/-- **A column failing both supports is an old double receiver of one of them.** -/
theorem common_failure_is_old {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph} {V L A B : Finset ℕ}
    {F : Family} (cl : Cycle D V q L) (ca : Cycle D V q A) (cb : Cycle D V q B)
    (apart : Disjoint (L ∩ A) (L ∩ B)) {j : ℕ}
    (fa : (q : ℝ) + 1 < count q (graph D (insert L F)) A j)
    (fb : (q : ℝ) + 1 < count q (graph D (insert L F)) B j) :
    j ∉ A ∧ j ∉ B ∧ (2 ≤ (inN (graph D F) A j).card ∨ 2 ≤ (inN (graph D F) B j).card) := by
  classical
  have sub : ∀ a b, graph D (insert L F) a b = true → D a b = true :=
    fun _ _ e => CrossValueOmissions.selected_sub e
  obtain ⟨ja, twoA⟩ := over_count hq ca sub fa
  obtain ⟨jb, twoB⟩ := over_count hq cb sub fb
  refine ⟨ja, jb, ?_⟩
  by_contra! few
  have fresh (K : Finset ℕ) (two : 2 ≤ (inN (graph D (insert L F)) K j).card)
      (one : (inN (graph D F) K j).card < 2) : ∃ x ∈ K, (x, j) ∈ added D F L := by
    by_contra! none
    have s : inN (graph D (insert L F)) K j ⊆ inN (graph D F) K j := by
      intro x hx
      obtain ⟨xk, e⟩ := mem_inN.mp hx
      rcases union_arc.mp e with old | nw
      · exact mem_inN.mpr ⟨xk, old⟩
      · exact (none x xk nw).elim
    have := card_le_card s
    omega
  obtain ⟨x, xa, hx⟩ := fresh A twoA few.1
  obtain ⟨y, yb, hy⟩ := fresh B twoB few.2
  have xy := ThirdPrice.new_parent_unique cl hx hy
  subst xy
  have xl := (mem_added.mp hx).1
  exact disjoint_left.mp apart (mem_inter.mpr ⟨xl, xa⟩) (mem_inter.mpr ⟨xl, yb⟩)

/-- **No mixture of the two receiver supports pays a failed attachment, and the obstruction is labelled.** -/
theorem receiver_mixture {q n : ℕ} (X : Model q n) (hq : 2 ≤ q) {F : Family} {L A B : Finset ℕ}
    (cl : Cycle X.D X.V q L) (ca : Cycle X.D X.V q A) (cb : Cycle X.D X.V q B)
    (apart : Disjoint (L ∩ A) (L ∩ B)) (bad : ¬ SmallRow q (graph X.D (insert L F)) X.V) :
    (∀ l : ℝ, 0 ≤ l → l ≤ 1 → ¬ RealDual q (graph X.D (insert L F)) X.V 1 (mix q A B l)) ∧
    (∃ j ∈ X.V, 2 * ((q : ℝ) + 1) <
        count q (graph X.D (insert L F)) A j + count q (graph X.D (insert L F)) B j) ∧
    ((∃ j ∈ X.V, j ∉ A ∧ j ∉ B ∧
        (q : ℝ) + 1 < count q (graph X.D (insert L F)) A j ∧
        (q : ℝ) + 1 < count q (graph X.D (insert L F)) B j ∧
        (2 ≤ (inN (graph X.D F) A j).card ∨ 2 ≤ (inN (graph X.D F) B j).card)) ∨
      (∃ j ∈ X.V, ∃ k ∈ X.V,
        (q : ℝ) + 1 < count q (graph X.D (insert L F)) A j ∧
        count q (graph X.D (insert L F)) B j ≤ q + 1 ∧
        (q : ℝ) + 1 < count q (graph X.D (insert L F)) B k ∧
        count q (graph X.D (insert L F)) A k ≤ q + 1 ∧
        ((q + 1) - count q (graph X.D (insert L F)) B j) *
            (count q (graph X.D (insert L F)) B k - count q (graph X.D (insert L F)) A k) +
          ((q + 1) - count q (graph X.D (insert L F)) A k) *
            (count q (graph X.D (insert L F)) A j - count q (graph X.D (insert L F)) B j) <
        (count q (graph X.D (insert L F)) A j - count q (graph X.D (insert L F)) B j) *
          (count q (graph X.D (insert L F)) B k - count q (graph X.D (insert L F)) A k))) := by
  classical
  set G := graph X.D (insert L F)
  have none : ∀ l : ℝ, 0 ≤ l → l ≤ 1 → ¬ RealDual q G X.V 1 (mix q A B l) :=
    fun l _ _ dual => bad (smallRow_of_realDual dual)
  refine ⟨none, ?_, ?_⟩
  · by_contra! low
    exact none (1 / 2) (by norm_num) (by norm_num) (half_pays ca cb low)
  · have empty : ¬ ∃ l : ℝ, 0 ≤ l ∧ l ≤ 1 ∧ RealDual q G X.V 1 (mix q A B l) :=
      fun ⟨l, l0, l1, d⟩ => none l l0 l1 d
    rw [mixture_iff ca cb, not_and_or] at empty
    rcases empty with first | second
    · push Not at first
      obtain ⟨j, jv, fa, fb⟩ := first
      obtain ⟨ja, jb, old⟩ := common_failure_is_old hq cl ca cb apart fa fb
      exact Or.inl ⟨j, jv, ja, jb, fa, fb, old⟩
    · push Not at second
      obtain ⟨j, jv, k, kv, fa, fb, viol⟩ := second
      by_cases both : (q : ℝ) + 1 < count q G B j
      · obtain ⟨ja, jb, old⟩ := common_failure_is_old hq cl ca cb apart fa both
        exact Or.inl ⟨j, jv, ja, jb, fa, both, old⟩
      · by_cases both' : (q : ℝ) + 1 < count q G A k
        · obtain ⟨ka, kb, old⟩ := common_failure_is_old hq cl ca cb apart both' fb
          exact Or.inl ⟨k, kv, ka, kb, both', fb, old⟩
        · push Not at both both'
          exact Or.inr ⟨j, jv, k, kv, fa, both, fb, both', viol⟩

/-! ### Retrying with another support through the same parent -/

/-- **Retry at a new-arc failure.** Let column `j ∉ A` receive the new arc `x → j` of `L` from `x ∈ A`, an
old arc from `y ∈ A`, and have an old arc back to `b ∈ A`, with `A` an old family cycle. Then either `L`
adds exactly the arc `x → j`, or `A - x + j` is an old family cycle with `y → x → b` on `A`. When `x ≠ p`
the new cycle still contains `p` and `z`. -/
theorem retry_support {q n : ℕ} (X : Model q n) (hq : 2 ≤ q) {F : Family} {L A : Finset ℕ}
    (small : SmallRow q (graph X.D F) X.V)
    (every : ∀ M, Boundary X F M → ¬ SmallRow q (graph X.D (insert M F)) X.V)
    (least : ∀ M, Boundary X F M → (targets X.D X.V F L).card ≤ (targets X.D X.V F M).card)
    (cl : Cycle X.D X.V q L) (ca : Cycle X.D X.V q A) (af : A ∈ F)
    {x y j b : ℕ} (jv : j ∈ X.V) (ja : j ∉ A) (xa : x ∈ A) (hx : (x, j) ∈ added X.D F L)
    (ya : y ∈ A) (yj : graph X.D F y j = true) (ba : b ∈ A) (jb : X.D j b = true)
    (oldjb : graph X.D F j b = true) :
    added X.D F L = {(x, j)} ∨
      (insert j (A.erase x) ∈ F ∧ Cycle X.D X.V q (insert j (A.erase x)) ∧
        X.D y x = true ∧ X.D x b = true ∧
        ∀ w ∈ A, w ≠ x → w ∈ insert j (A.erase x)) := by
  classical
  have oldA : ∀ c ∈ A, ∀ d ∈ A, X.D c d = true → graph X.D F c d = true :=
    fun c cm d dm cd => active.mpr ⟨A, mem_col.mpr ⟨af, cm, dm, cd⟩⟩
  rcases ThirdPrice.new_obstruction_exchange X hq ca oldA jv ja xa hx ya yj ba jb oldjb with
    ⟨cn, bd, eq⟩ | ⟨yx, xb, cn, empty⟩
  · left
    have tN : (targets X.D X.V F (insert j (A.erase y))).card ≤ 1 := by
      have s : targets X.D X.V F (insert j (A.erase y)) ⊆ {j} := by
        intro w hw
        obtain ⟨_, wm, u, um, uw, miss⟩ := mem_filter.mp hw
        have : (u, w) ∈ added X.D F (insert j (A.erase y)) := mem_added.mpr ⟨um, wm, uw, miss⟩
        rw [eq, mem_singleton] at this
        rw [mem_singleton]
        exact (Prod.ext_iff.mp this).2
      simpa using card_le_card s
    have tL := (least _ bd).trans tN
    have jT : j ∈ targets X.D X.V F L := by
      obtain ⟨xl, jl, xj, miss⟩ := mem_added.mp hx
      exact mem_filter.mpr ⟨jv, jl, x, xl, xj, miss⟩
    ext e
    obtain ⟨c, d⟩ := e
    simp only [mem_singleton]
    constructor
    · intro he
      obtain ⟨cl', dl, cd, miss⟩ := mem_added.mp he
      have dT : d ∈ targets X.D X.V F L := mem_filter.mpr ⟨cl.sub dl, dl, c, cl', cd, miss⟩
      have dj : d = j := card_le_one.mp tL d dT j jT
      subst dj
      have cx := ThirdPrice.new_parent_unique cl he hx
      rw [cx]
    · rintro ⟨⟩
      exact hx
  · right
    have oldN : ∀ c ∈ insert j (A.erase x), ∀ d ∈ insert j (A.erase x), X.D c d = true →
        graph X.D F c d = true := by
      intro c cm d dm cd
      by_contra miss
      have : (c, d) ∈ added X.D F (insert j (A.erase x)) :=
        mem_added.mpr ⟨cm, dm, cd, Bool.eq_false_iff.mpr miss⟩
      rw [empty] at this
      exact notMem_empty _ this
    exact ⟨AttachmentLaws.closed_family X small every _ cn oldN, cn, yx, xb,
      fun w wa wx => mem_insert_of_mem (mem_erase.mpr ⟨wx, wa⟩)⟩

#print axioms interval
#print axioms mix_dual_iff
#print axioms mixture_iff
#print axioms half_pays
#print axioms common_failure_is_old
#print axioms receiver_mixture
#print axioms retry_support

end LeanCH.BR.Closure.ReceiverMixture
