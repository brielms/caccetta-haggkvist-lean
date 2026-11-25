import checkpoints.shen_extension.FragmentBudget

/-!
# Full rows at radius four, ordinary rows at degree three, class budgets

Generic in `D`, `q`, the fragment `F`, the slack `t`, the degree `r` and the radii.
Setting: `QFree D F q`, every row of `F` keeps at least `2 + t` (P1) or `3 + t` (P2) heads in
`F`; `reach D F i x` (`Profile54.reach`) counts the other labels within `i` steps inside `F`.

* P1 `full_row_core` (`t = 0`): a row with `n` heads, `n + 5 ≤ 2q`, reaches at least `n + 5`
  labels within four steps. Proof: `|P_3| ≥ n + 3` (`head_reach`), `|P_2| ≥ n + 1`
  (`head_second`); if `|P_4| ≤ n + 4` the shell step (lower degree two, `|P_3| ≤ 2q`) forces
  `|P_3| = n + 3` and at most one label in `P_4 \ P_3`. Then every row of `P_3` keeps a head in
  `P_3`, the rows of `P_2` keep all of theirs, so the one-head rows of `P_3` lie in `P_3 \ P_2`
  (at most two of them), and `ThinSuppliers.lone_count` gives `2q + 2 ≤ |P_3| + 2 = n + 5`.
* P1 `full_row` (general `t`, every radius `i ≥ 4`): `r + 5 + t ≤ reach D F i x` for a row with
  exactly `r` heads, `r + 5 ≤ 2q`, `r + 1 + t ≤ |F|`. The protected-head deletion of
  `FragmentBudget.full_floor`.
* P2 `shell_gain` (generic shell form), `ordinary_core` (`t = 0`, degree three, `6 ≤ q`):
  `9 ≤ reach 3`, `11 ≤ reach 4`; `lift_heads` (delete `t` direct heads) and `ordinary_rows`:
  `9 + t ≤ reach 3`, `11 + t ≤ reach 4` when every row keeps `3 + t` heads.
* P3 `class_budget` (any finite family of disjoint classes with floors at radii `(i, j)`,
  `i + j ≤ q`): `∑ |C_k| f_k ≤ |F| (|F| - 1)`; `class_budget3`, three classes.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.FullRow
open Finset BRq2 BRq3
open Profile54 (reach)

variable {D : CH.Digraph} {q : ℕ}

/-! ### P1: a full row at radius four -/

/-- **P1, `t = 0`.** In a `q`-free set of minimum out-degree two, a row with `n` heads,
`n + 5 ≤ 2q`, reaches at least `n + 5` other labels within four steps. -/
theorem full_row_core {F : Finset ℕ} (free : QFree D F q)
    (deg : ∀ v ∈ F, 2 ≤ (outN D F v).card) {x : ℕ} (hx : x ∈ F)
    (hn : (outN D F x).card + 5 ≤ 2 * q) :
    (outN D F x).card + 5 ≤ reach D F 4 x := by
  classical
  have hq : 4 ≤ q := by have := deg x hx; omega
  have b2 := Profile54.head_second free (by omega) hx (by omega) deg
  have c2 := Profile54.card_ball_erase (D := D) (k := 2) hx
  have r3 := Profile54.head_reach free (by omega) hx (by omega) deg
  unfold reach at r3 ⊢
  have S23 : (ball D F x 2).erase x ⊆ (ball D F x 3).erase x :=
    erase_subset_erase x (ball_mono_radius (by omega))
  have S34 : (ball D F x 3).erase x ⊆ (ball D F x 4).erase x :=
    erase_subset_erase x (ball_mono_radius (by omega))
  have P3F : (ball D F x 3).erase x ⊆ F := (erase_subset _ _).trans ball_subset
  have m34 := card_le_card S34
  by_contra hlt
  have small : ((ball D F x 3).erase x).card ≤ 2 * q := by omega
  have ne3 : ((ball D F x 3).erase x).Nonempty := card_pos.mp (by omega)
  have host2 : BypassRepair.NoHost q 2 :=
    ShapeClimbMono.lower_hosts_every q 2 (by rw [Profile54.floor_nine]; norm_num)
  have sh : ((ball D F x 3).erase x).card + 2 + 1 ≤ ((ball D F x 4).erase x).card + 2 :=
    Profile54.shell_step free hx (k := 3) (by omega) host2 deg ne3 (by omega)
  have d34 : (((ball D F x 4).erase x) \ (ball D F x 3).erase x).card ≤ 1 := by
    rw [card_sdiff_of_subset S34]; omega
  have one : ∀ v ∈ (ball D F x 3).erase x, 1 ≤ (outN D ((ball D F x 3).erase x) v).card := by
    intro v hv
    have cover : outN D F v ⊆ outN D ((ball D F x 3).erase x) v ∪
        (((ball D F x 4).erase x) \ (ball D F x 3).erase x) := by
      intro w hw
      by_cases ws : w ∈ (ball D F x 3).erase x
      · exact mem_union_left _ (mem_outN.mpr ⟨ws, (mem_outN.mp hw).2⟩)
      · exact mem_union_right _ (mem_sdiff.mpr
          ⟨Profile54.step_erase free hx (k := 3) (by omega) (mem_of_mem_erase hv) hw, ws⟩)
    have := (card_le_card cover).trans (card_union_le _ _)
    have := deg v (P3F hv)
    omega
  have loneSub : ThinSuppliers.lone D ((ball D F x 3).erase x) ⊆
      ((ball D F x 3).erase x) \ (ball D F x 2).erase x := by
    intro v hv
    obtain ⟨vP, le⟩ := ThinSuppliers.mem_lone.mp hv
    refine mem_sdiff.mpr ⟨vP, fun v2 => ?_⟩
    have keep : outN D F v ⊆ (ball D F x 3).erase x := fun w hw =>
      Profile54.step_erase free hx (k := 2) (by omega) (mem_of_mem_erase v2) hw
    rw [Profile54.out_restrict P3F keep] at le
    have := deg v (P3F vP)
    omega
  have lc := ThinSuppliers.lone_count (free.mono_set P3F) (by omega) one ne3 small
  have := card_le_card loneSub
  rw [card_sdiff_of_subset S23] at this
  omega

/-- **P1.** A row with exactly `r` heads in a `q`-free fragment where every row keeps `2 + t`
heads, `r + 5 ≤ 2q`, `r + 1 + t ≤ |F|`: for every radius `i ≥ 4`, `r + 5 + t ≤ reach D F i x`.
Delete `t` labels away from the row and its heads, all inside its `i`-ball if there are `t`
such, else covering them (as in `FragmentBudget.full_floor`); `full_row_core` in the rest. -/
theorem full_row {F : Finset ℕ} {t r i : ℕ} (free : QFree D F q) (hi4 : 4 ≤ i)
    (hr : r + 5 ≤ 2 * q) (hN : r + 1 + t ≤ F.card)
    (deg : ∀ v ∈ F, 2 + t ≤ (outN D F v).card) {x : ℕ} (hx : x ∈ F)
    (full : (outN D F x).card = r) : r + 5 + t ≤ reach D F i x := by
  classical
  set H := outN D F x with hH
  set E := insert x H with hE
  set U := ((ball D F x i).erase x) \ H with hU
  have xH : x ∉ H := fun h => loopfree free (by omega) hx (mem_outN.mp h).2
  have EF : E ⊆ F := insert_subset hx outN_subset
  have Ec : E.card = r + 1 := by rw [hE, card_insert_of_notMem xH, full]
  have UE : U ⊆ F \ E := by
    intro w hw
    obtain ⟨hw1, wH⟩ := mem_sdiff.mp hw
    obtain ⟨wx, wb⟩ := mem_erase.mp hw1
    refine mem_sdiff.mpr ⟨ball_subset wb, fun h => ?_⟩
    rcases mem_insert.mp h with e | e
    · exact wx e
    · exact wH e
  have FE : t ≤ (F \ E).card := by rw [card_sdiff_of_subset EF]; omega
  obtain ⟨T, TF, Tc, hT⟩ : ∃ T, T ⊆ F \ E ∧ T.card = t ∧ (T ⊆ U ∨ U ⊆ T) := by
    by_cases hUc : t ≤ U.card
    · obtain ⟨T, TU, Tc⟩ := exists_subset_card_eq hUc
      exact ⟨T, TU.trans UE, Tc, Or.inl TU⟩
    · obtain ⟨T, UT, TF, Tc⟩ := exists_subsuperset_card_eq UE (by omega) FE
      exact ⟨T, TF, Tc, Or.inr UT⟩
  have offT : ∀ w ∈ E, w ∉ T := fun w hw h => (mem_sdiff.mp (TF h)).2 hw
  have xF' : x ∈ F \ T := mem_sdiff.mpr ⟨hx, offT x (mem_insert_self x H)⟩
  have keepH : outN D (F \ T) x = H := Profile54.out_restrict sdiff_subset (fun w hw =>
    mem_sdiff.mpr ⟨(mem_outN.mp hw).1, offT w (mem_insert_of_mem hw)⟩)
  have d2 := FragmentBudget.delete_deg (a := 2) Tc.le deg
  have hrch := full_row_core (free.mono_set sdiff_subset) d2 xF' (by rw [keepH, full]; omega)
  rw [keepH, full] at hrch
  have mono := FragmentBudget.reach_mono (D := D) (F := F \ T) (x := x) hi4
  have sub : (ball D (F \ T) x i).erase x ⊆ ((ball D F x i).erase x) \ T := by
    intro w hw
    obtain ⟨wx, wb⟩ := mem_erase.mp hw
    exact mem_sdiff.mpr ⟨mem_erase.mpr ⟨wx, FragmentBudget.ball_mono_set sdiff_subset wb⟩,
      (mem_sdiff.mp (ball_subset wb)).2⟩
  have c1 := card_le_card sub
  unfold reach at mono hrch ⊢
  rcases hT with TU | UT
  · have TB : T ⊆ (ball D F x i).erase x := fun w hw => (mem_sdiff.mp (TU hw)).1
    have := card_sdiff_of_subset TB
    have := card_le_card TB
    omega
  · have sH : ((ball D F x i).erase x) \ T ⊆ H := by
      intro w hw
      obtain ⟨wb, wT⟩ := mem_sdiff.mp hw
      by_contra wH
      exact wT (UT (mem_sdiff.mpr ⟨wb, wH⟩))
    have := card_le_card sH
    rw [full] at this
    omega

/-! ### P2: ordinary rows at minimum out-degree three -/

/-- **Shell gain (generic).** Rows of out-degree `≥ d ≥ 1`, `1 ≤ k`, `k + 1 ≤ q`: a punctured
`k`-ball of at most `q` labels gains `d` labels at radius `k + 1`, one of at most `2q` labels
gains `d - 1`. -/
theorem shell_gain {F : Finset ℕ} (free : QFree D F q) {x k d : ℕ} (hx : x ∈ F) (hk1 : 1 ≤ k)
    (hk : k + 1 ≤ q) (hd : 1 ≤ d) (deg : ∀ v ∈ F, d ≤ (outN D F v).card) :
    (reach D F k x ≤ q → reach D F k x + d ≤ reach D F (k + 1) x) ∧
      (reach D F k x ≤ 2 * q → reach D F k x + d ≤ reach D F (k + 1) x + 1) := by
  have h1 : outN D F x ⊆ (ball D F x k).erase x := by
    intro v hv
    refine mem_erase.mpr ⟨?_, ball_mono_radius hk1 ((mem_ball_one hx).mpr (Or.inr hv))⟩
    intro e
    rw [e] at hv
    exact loopfree free (by omega) hx (mem_outN.mp hv).2
  have ne : ((ball D F x k).erase x).Nonempty :=
    card_pos.mp (lt_of_lt_of_le (by have := deg x hx; omega) (card_le_card h1))
  have host1 : BypassRepair.NoHost q 1 :=
    ShapeClimbMono.lower_hosts_every q 1 (by rw [Profile54.floor_nine]; norm_num)
  have host2 : BypassRepair.NoHost q 2 :=
    ShapeClimbMono.lower_hosts_every q 2 (by rw [Profile54.floor_nine]; norm_num)
  unfold reach
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := Profile54.shell_step free hx hk host1 deg ne (by omega)
    omega
  · have := Profile54.shell_step free hx hk host2 deg ne (by omega)
    omega

/-- **P2, `t = 0`.** Minimum out-degree three, `6 ≤ q`: `9 ≤ reach 3` and `11 ≤ reach 4`. -/
theorem ordinary_core {F : Finset ℕ} (free : QFree D F q) (hq : 6 ≤ q)
    (deg : ∀ v ∈ F, 3 ≤ (outN D F v).card) {x : ℕ} (hx : x ∈ F) :
    9 ≤ reach D F 3 x ∧ 11 ≤ reach D F 4 x := by
  obtain ⟨a, b, c, e, f, g, h⟩ := Profile54.growth_facts free (by omega) hx (by omega) deg
  have r3 : 9 ≤ reach D F 3 x := by omega
  have s2 : reach D F 3 x ≤ 2 * q → reach D F 3 x + 3 ≤ reach D F 4 x + 1 :=
    (shell_gain free hx (k := 3) (by omega) (by omega) (by omega) deg).2
  refine ⟨r3, ?_⟩
  have m := FragmentBudget.reach_mono (D := D) (F := F) (x := x) (show 3 ≤ 4 by omega)
  by_cases h3 : reach D F 3 x ≤ 2 * q
  · have := s2 h3; omega
  · omega

/-- **Lifting by deleted heads (generic).** If every `q`-free subfragment with minimum out-degree
`d` has `a ≤ reach i` at each row, then in a fragment where every row keeps `d + t` heads each row
has `a + t ≤ reach i` (`1 ≤ i`). Delete `t` direct heads of the row. -/
theorem lift_heads {F : Finset ℕ} {t i d a : ℕ} (free : QFree D F q) (hq : 1 ≤ q) (hi1 : 1 ≤ i)
    (deg : ∀ v ∈ F, d + t ≤ (outN D F v).card)
    (base : ∀ F' : Finset ℕ, F' ⊆ F → QFree D F' q → (∀ v ∈ F', d ≤ (outN D F' v).card) →
      ∀ x ∈ F', a ≤ reach D F' i x)
    {x : ℕ} (hx : x ∈ F) : a + t ≤ reach D F i x := by
  classical
  obtain ⟨T, TH, Tc⟩ := exists_subset_card_eq (s := outN D F x) (n := t)
    (by have := deg x hx; omega)
  have xT : x ∉ T := fun h => loopfree free hq hx (mem_outN.mp (TH h)).2
  have dd := FragmentBudget.delete_deg (a := d) Tc.le deg
  have g := base (F \ T) sdiff_subset (free.mono_set sdiff_subset) dd x (mem_sdiff.mpr ⟨hx, xT⟩)
  have sub : (ball D (F \ T) x i).erase x ∪ T ⊆ (ball D F x i).erase x := by
    refine union_subset (erase_subset_erase x (FragmentBudget.ball_mono_set sdiff_subset))
      (fun w hw => mem_erase.mpr ⟨fun e => xT (by rw [← e]; exact hw), ball_mono_radius hi1
        ((mem_ball_one hx).mpr (Or.inr (TH hw)))⟩)
  have dis : Disjoint ((ball D (F \ T) x i).erase x) T :=
    disjoint_left.mpr (fun w hw hwT =>
      (mem_sdiff.mp (ball_subset (mem_of_mem_erase hw))).2 hwT)
  have c := card_le_card sub
  rw [card_union_of_disjoint dis] at c
  unfold reach at g ⊢
  omega

/-- **P2.** Every row keeps `3 + t` heads, `6 ≤ q`: `9 + t ≤ reach 3` and `11 + t ≤ reach 4`. -/
theorem ordinary_rows {F : Finset ℕ} {t : ℕ} (free : QFree D F q) (hq : 6 ≤ q)
    (deg : ∀ v ∈ F, 3 + t ≤ (outN D F v).card) {x : ℕ} (hx : x ∈ F) :
    9 + t ≤ reach D F 3 x ∧ 11 + t ≤ reach D F 4 x :=
  ⟨lift_heads free (by omega) (by omega) deg
      (fun _ _ fr dg y hy => (ordinary_core fr hq dg hy).1) hx,
    lift_heads free (by omega) (by omega) deg
      (fun _ _ fr dg y hy => (ordinary_core fr hq dg hy).2) hx⟩

/-! ### P3: budgets with classes -/

/-- **P3 (general).** Pairwise disjoint classes `C k ⊆ F` (`k ∈ I`) whose rows have
`f k ≤ reach i + reach j`, `i + j ≤ q`: `∑_k |C k| f k ≤ |F| (|F| - 1)`. -/
theorem class_budget {ι : Type*} [DecidableEq ι] {F : Finset ℕ} {I : Finset ι}
    {C : ι → Finset ℕ} {f : ι → ℕ} {i j : ℕ} (free : QFree D F q) (hij : i + j ≤ q)
    (CF : ∀ k ∈ I, C k ⊆ F) (dis : ∀ k ∈ I, ∀ l ∈ I, k ≠ l → Disjoint (C k) (C l))
    (floor : ∀ k ∈ I, ∀ x ∈ C k, f k ≤ reach D F i x + reach D F j x) :
    ∑ k ∈ I, (C k).card * f k ≤ F.card * (F.card - 1) := by
  have h1 : ∑ k ∈ I, (C k).card * f k ≤
      ∑ k ∈ I, ∑ x ∈ C k, (reach D F i x + reach D F j x) :=
    sum_le_sum (fun k hk => by
      rw [← smul_eq_mul]
      exact card_nsmul_le_sum _ _ _ (floor k hk))
  have h2 : ∑ x ∈ I.biUnion C, (reach D F i x + reach D F j x) =
      ∑ k ∈ I, ∑ x ∈ C k, (reach D F i x + reach D F j x) :=
    sum_biUnion (fun k hk l hl ne => dis k hk l hl ne)
  have h3 : ∑ x ∈ I.biUnion C, (reach D F i x + reach D F j x) ≤
      ∑ x ∈ F, (reach D F i x + reach D F j x) :=
    sum_le_sum_of_subset (biUnion_subset.mpr CF)
  have h4 := FragmentBudget.mixed_budget free hij (D := D) (F := F) (i := i) (j := j)
  omega

/-- **P3, three classes.** -/
theorem class_budget3 {F C1 C2 C3 : Finset ℕ} {a b c i j : ℕ} (free : QFree D F q)
    (hij : i + j ≤ q) (C1F : C1 ⊆ F) (C2F : C2 ⊆ F) (C3F : C3 ⊆ F) (d12 : Disjoint C1 C2)
    (d13 : Disjoint C1 C3) (d23 : Disjoint C2 C3)
    (f1 : ∀ x ∈ C1, a ≤ reach D F i x + reach D F j x)
    (f2 : ∀ x ∈ C2, b ≤ reach D F i x + reach D F j x)
    (f3 : ∀ x ∈ C3, c ≤ reach D F i x + reach D F j x) :
    C1.card * a + C2.card * b + C3.card * c ≤ F.card * (F.card - 1) := by
  classical
  have s1 : C1.card • a ≤ ∑ x ∈ C1, (reach D F i x + reach D F j x) := card_nsmul_le_sum _ _ _ f1
  have s2 : C2.card • b ≤ ∑ x ∈ C2, (reach D F i x + reach D F j x) := card_nsmul_le_sum _ _ _ f2
  have s3 : C3.card • c ≤ ∑ x ∈ C3, (reach D F i x + reach D F j x) := card_nsmul_le_sum _ _ _ f3
  rw [smul_eq_mul] at s1 s2 s3
  have d : Disjoint (C1 ∪ C2) C3 := disjoint_union_left.mpr ⟨d13, d23⟩
  have u1 : ∑ x ∈ C1 ∪ C2 ∪ C3, (reach D F i x + reach D F j x) =
      ∑ x ∈ C1, (reach D F i x + reach D F j x) + ∑ x ∈ C2, (reach D F i x + reach D F j x) +
        ∑ x ∈ C3, (reach D F i x + reach D F j x) := by
    rw [sum_union d, sum_union d12]
  have sub : C1 ∪ C2 ∪ C3 ⊆ F := union_subset (union_subset C1F C2F) C3F
  have le : ∑ x ∈ C1 ∪ C2 ∪ C3, (reach D F i x + reach D F j x) ≤
      ∑ x ∈ F, (reach D F i x + reach D F j x) := sum_le_sum_of_subset sub
  have mb := FragmentBudget.mixed_budget free hij (D := D) (F := F) (i := i) (j := j)
  omega

#print axioms full_row_core
#print axioms full_row
#print axioms shell_gain
#print axioms ordinary_core
#print axioms lift_heads
#print axioms ordinary_rows
#print axioms class_budget
#print axioms class_budget3

end LeanCH.BR.FullRow
