import checkpoints.shen_extension.ShapeClimbFast
import checkpoints.shen_extension.ShapeClimbMono

/-!
# The reach climb at fat roots of out-regular digraphs

A root `u` is *fat* when its second layer has at least `r` labels. `FatFloor q r i a` says that
every fat root of every `q`-free digraph of out-degree exactly `r` has at least `a` labels in its
ball of radius `i`.

`advanceFat` is `ShapeClimbDead3.advance3` restricted to fat roots: the rows of the ball are
still bounded by floors `fs` valid for all roots (they feed `Dead3`), while the root's own
profile is bounded by its fat floors `g` and must list a second width of at least `r`
(`condFat`). `climbFat`, `layersFat` repeat the climb; at radius two the climb starts from
`2 r + 1`, since a fat root of out-degree `r` has `|B₂| = 1 + r + |L₂| ≥ 2 r + 1`.
`layersFatF` is the same list over the pruned search and the reach table of `ShapeClimbFast`.
Everything is generic in `q` and `r`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.ShapeClimbFat
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion RecursivePrefixBudget
open ShapeClimbRoot ShapeClimbDead ShapeClimb ShapeClimbDead2 ShapeClimbDead3 ReachCapacity
open DotTwoPassShellTransport (layer shell layer_subset)

/-- A floor for the fat roots of out-regular digraphs. -/
def FatFloor (q r i a : ℕ) : Prop :=
  ∀ (D : CH.Digraph) (V : Finset ℕ), QFree D V q → (∀ v ∈ V, (outN D V v).card = r) →
    ∀ u ∈ V, r ≤ (layer D V 2 u).card → a ≤ (ball D V u i).card

theorem fatFloor_zero {q r i : ℕ} : FatFloor q r i 0 := fun _ _ _ _ _ _ _ => Nat.zero_le _

theorem fatFloor_max {q r i a b : ℕ} (fa : FatFloor q r i a) (fb : FatFloor q r i b) :
    FatFloor q r i (max a b) :=
  fun D V free reg u hu fat => max_le (fa D V free reg u hu fat) (fb D V free reg u hu fat)

/-- A width profile whose second width, if present, is at least `r`. -/
def condFat (r : ℕ) (p : List ℕ) : Bool := decide (p.length < 2 ∨ r ≤ p.getD 1 0)

def deadAllFat (q r : ℕ) (degrees fs g : List ℕ) (k x c F : ℕ) : Bool :=
  (splits r k (x - 1 - c)).all
    (fun ws => !good g k ws || !condFat r (ws ++ [c]) || Dead3 q r degrees fs (ws ++ [c]) (F - x))

def CanRaiseFat (q r k : ℕ) (fs g : List ℕ) (F : ℕ) (bank : List Comparison) : Prop :=
  ∀ x ∈ Icc (g.getD (k + 1) 0) F, ∀ c ∈ range (x - g.getD k 0 + 1),
    (bank.any (fun b => decide (Pass x c F r b.degree (q * b.degree + 1) (b.left + b.right))) ||
      deadAllFat q r (bank.map Comparison.degree) fs g k x c F) = true

instance {q r k fs g F bank} : Decidable (CanRaiseFat q r k fs g F bank) := by
  unfold CanRaiseFat
  infer_instance

theorem advanceFat {q r k F : ℕ} {fs g : List ℕ} {bank : List Comparison}
    (floors : ∀ i, Floor q r i (fs.getD i 0)) (fats : ∀ i, FatFloor q r i (g.getD i 0))
    (time : k + 2 ≤ q) (narrow : F < g.getD (k + 1) 0 + r)
    (sound : ∀ b ∈ bank, Valid q b ∧ b.degree ≤ r ∧ NoHost q b.degree)
    (check : CanRaiseFat q r k fs g F bank) : FatFloor q r (k + 2) (F + 1) := by
  intro D V free reg u hu fat
  have deg : ∀ v ∈ V, r ≤ (outN D V v).card := fun v hv => (reg v hv).ge
  have root := reg u hu
  by_contra! small
  have prev := fats k D V free reg u hu fat
  have start := fats (k + 1) D V free reg u hu fat
  have inc : (ball D V u (k + 1)).card ≤ (ball D V u (k + 2)).card :=
    card_le_card (ball_mono_radius (by omega))
  have lay : (ball D V u (k + 1)).card = (layer D V (k + 1) u).card + (ball D V u k).card :=
    card_ball_succ k
  have sh : (ball D V u (k + 2)).card = (layer D V (k + 2) u).card + (ball D V u (k + 1)).card :=
    card_ball_succ (k + 1)
  have shl : shell D V (k + 1) u = layer D V (k + 2) u := by
    simp only [shell, layer, show k + 2 - 1 = k + 1 by omega]
  have hc := check (ball D V u (k + 1)).card (mem_Icc.mpr ⟨start, by omega⟩)
    (layer D V (k + 1) u).card (mem_range.mpr (by omega))
  rcases Bool.or_eq_true_iff.mp hc with pass | dead
  · obtain ⟨b, hb, pass⟩ := List.any_eq_true.mp pass
    obtain ⟨⟨left, right⟩, fit, lower⟩ := sound b hb
    obtain ⟨G, Q, hG, _, hL, quad, cap⟩ := prefix_completion (by omega : q / 2 + (q - q / 2) ≤ q)
      (order_of_noHost lower) left right fit free deg hu time (by rw [shl]; omega)
    exact pass_false (F := F) (card_erase_add_one (self_mem_ball hu)) (by rw [shl]; omega)
      hG hL quad cap (of_decide_eq_true pass)
  · set ws := (List.range k).map (fun j => (layer D V (j + 1) u).card) with hws
    have len : ws.length = k := by simp [hws]
    have exact : ∀ i < ws.length, (layer D V (i + 1) u).card = ws.getD i 0 :=
      fun i hi => (widths_getD (by omega)).symm
    have size := ball_card_take hu exact (n := k) len.ge
    rw [List.take_of_length_le (by omega)] at size
    have mem : ws ∈ splits r k ((ball D V u (k + 1)).card - 1 - (layer D V (k + 1) u).card) := by
      refine mem_splits len (by omega) (fun pos => ?_)
      rw [widths_getD pos]
      exact layer_one_card free (by omega) hu root
    have ok : good g k ws = true := by
      refine List.all_eq_true.mpr (fun j hj => decide_eq_true ?_)
      rw [List.mem_range] at hj
      rw [← ball_card_take hu exact (by omega)]
      exact fats j D V free reg u hu fat
    have exact' : ∀ i < (ws ++ [(layer D V (k + 1) u).card]).length,
        (layer D V (i + 1) u).card = (ws ++ [(layer D V (k + 1) u).card]).getD i 0 := by
      intro i hi
      rw [List.length_append, len, List.length_singleton] at hi
      rcases Nat.lt_or_ge i k with h | h
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact exact i (by omega)
      · obtain rfl : i = k := by omega
        rw [List.getD_append_right _ _ _ _ (by omega), len, Nat.sub_self]
        rfl
    have cf : condFat r (ws ++ [(layer D V (k + 1) u).card]) = true := by
      refine decide_eq_true ?_
      rcases Nat.lt_or_ge (ws ++ [(layer D V (k + 1) u).card]).length 2 with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [← exact' 1 (by omega)]; exact fat)
    have d := List.all_eq_true.mp dead ws mem
    rw [ok, cf, Bool.not_true, Bool.false_or, Bool.false_or] at d
    refine dead3_false free deg hu root (degrees := bank.map Comparison.degree) ?_ floors exact' ?_ d
    · intro t ht
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
      exact (sound b hb).2.2
    · rw [List.length_append, len, List.length_singleton]
      show (layer D V (k + 2) u).card ≤ _
      omega

def climbFat (q r k : ℕ) (fs g : List ℕ) (bank : List Comparison) (value fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => value
  | fuel + 1 =>
    if CanRaiseFat q r k fs g value bank then climbFat q r k fs g bank (value + 1) fuel else value

theorem climbFat_sound {q r k fs g bank} (floors : ∀ i, Floor q r i (fs.getD i 0))
    (fats : ∀ i, FatFloor q r i (g.getD i 0))
    (time : k + 2 ≤ q) (sound : ∀ b ∈ bank, Valid q b ∧ b.degree ≤ r ∧ NoHost q b.degree)
    (fuel value : ℕ) (start : FatFloor q r (k + 2) value)
    (budget : value + fuel ≤ g.getD (k + 1) 0 + r) :
    FatFloor q r (k + 2) (climbFat q r k fs g bank value fuel) := by
  induction fuel generalizing value with
  | zero => exact start
  | succ n ih =>
    simp only [climbFat]
    split
    next check => exact ih _ (advanceFat floors fats time (by omega) sound check) (by omega)
    next => exact start

/-- The fat floors at radii `0 … k + 1`, from the global floors `fs`. -/
def layersFat (q r : ℕ) (bank : List Comparison) (fs : List ℕ) : ℕ → List ℕ
  | 0 => [1, r + 1]
  | k + 1 =>
    let g := layersFat q r bank fs k
    let start := max (g.getD (k + 1) 0) (if k = 0 then 2 * r + 1 else 0)
    g ++ [climbFat q r k fs g bank start (g.getD (k + 1) 0 + r - start)]

/-- A fat root of out-degree `r` has at least `2 r + 1` labels within radius two. -/
theorem fat_two {q r : ℕ} (hq : 1 ≤ q) : FatFloor q r 2 (2 * r + 1) := by
  intro D V free reg u hu fat
  have e : (ball D V u 2).card = (layer D V 2 u).card + (ball D V u 1).card := card_ball_succ 1
  have one := ReachLedger.ball_one free hq hu
  rw [reg u hu] at one
  omega

theorem layersFat_sound {q r bank fs} (hq : 1 ≤ q)
    (sound : ∀ b ∈ bank, Valid q b ∧ b.degree ≤ r ∧ NoHost q b.degree)
    (floors : ∀ i, Floor q r i (fs.getD i 0)) (k : ℕ) (time : k + 1 ≤ q) :
    (layersFat q r bank fs k).length = k + 2 ∧
      ∀ i, FatFloor q r i ((layersFat q r bank fs k).getD i 0) := by
  induction k with
  | zero =>
    refine ⟨rfl, fun i => ?_⟩
    match i with
    | 0 => exact fun D V _ _ u hu _ => card_pos.mpr ⟨u, self_mem_ball hu⟩
    | 1 =>
      intro D V free reg u hu _
      change r + 1 ≤ (ball D V u 1).card
      rw [ReachLedger.ball_one free hq hu, reg u hu]
    | i + 2 => simpa [layersFat] using (fatFloor_zero : FatFloor q r (i + 2) 0)
  | succ k ih =>
    obtain ⟨len, fats⟩ := ih (by omega)
    set g := layersFat q r bank fs k with hg
    have start : FatFloor q r (k + 2) (max (g.getD (k + 1) 0) (if k = 0 then 2 * r + 1 else 0)) := by
      refine fatFloor_max (fun D V free reg u hu fat => (fats (k + 1) D V free reg u hu fat).trans
        (card_le_card (ball_mono_radius (Nat.le_succ (k + 1))))) ?_
      split
      next h => subst h; exact fat_two hq
      next => exact fatFloor_zero
    have top : FatFloor q r (k + 2)
        (climbFat q r k fs g bank (max (g.getD (k + 1) 0) (if k = 0 then 2 * r + 1 else 0))
          (g.getD (k + 1) 0 + r - max (g.getD (k + 1) 0) (if k = 0 then 2 * r + 1 else 0))) := by
      by_cases fit : max (g.getD (k + 1) 0) (if k = 0 then 2 * r + 1 else 0) ≤ g.getD (k + 1) 0 + r
      · exact climbFat_sound floors fats time sound _ _ start (by omega)
      · rw [show g.getD (k + 1) 0 + r - max (g.getD (k + 1) 0) (if k = 0 then 2 * r + 1 else 0) = 0
          by omega]
        exact start
    refine ⟨by simp [layersFat, ← hg, len], fun i => ?_⟩
    simp only [layersFat, ← hg]
    rcases Nat.lt_or_ge i (k + 2) with h | h
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact fats i
    · rcases Nat.eq_or_lt_of_le h with rfl | h
      · rw [List.getD_append_right _ _ _ _ (by omega), len, Nat.sub_self]
        exact top
      · rw [List.getD_eq_default _ _ (by simp [len]; omega)]
        exact fatFloor_zero

/-! ### The same list over the pruned search -/

open ShapeClimbFast

def deadAllFatF (T : Tbl) (q r : ℕ) (degrees fs g : List ℕ) (k x c F : ℕ) : Bool :=
  deadAllF r g (fun ws => !condFat r (ws ++ [c]) || Dead3F T q r degrees fs (ws ++ [c]) (F - x))
    (fun _ => false) (peelCap q r degrees) k (x - 1 - c)

theorem deadAllFatF_eq (q r : ℕ) (degrees fs g : List ℕ) (RB EB k x c F : ℕ) :
    deadAllFatF (mkT q r degrees fs RB EB) q r degrees fs g k x c F =
      deadAllFat q r degrees fs g k x c F := by
  rw [deadAllFatF, deadAllF_eq _ _ _ _ _
    (fun _ _ h => by simp at h)
    (fun pre a rest h => by
      rw [dead3_of_cap _ q r degrees fs c (F - x) pre a rest h, Bool.or_true])]
  unfold deadAllFat
  refine all_congr' (fun ws _ => ?_)
  rw [dead3F_eq, Bool.or_assoc]

def CanRaiseFatF (T : Tbl) (q r k : ℕ) (fs g : List ℕ) (F : ℕ) (bank : List Comparison) : Prop :=
  ∀ x ∈ Icc (g.getD (k + 1) 0) F, ∀ c ∈ range (x - g.getD k 0 + 1),
    (bank.any (fun b => decide (Pass x c F r b.degree (q * b.degree + 1) (b.left + b.right))) ||
      deadAllFatF T q r (bank.map Comparison.degree) fs g k x c F) = true

instance {T q r k fs g F bank} : Decidable (CanRaiseFatF T q r k fs g F bank) := by
  unfold CanRaiseFatF; infer_instance

theorem canRaiseFatF_iff (q r k : ℕ) (fs g : List ℕ) (F : ℕ) (bank : List Comparison) (RB EB : ℕ) :
    CanRaiseFatF (mkT q r (bank.map Comparison.degree) fs RB EB) q r k fs g F bank ↔
      CanRaiseFat q r k fs g F bank := by
  simp only [CanRaiseFatF, CanRaiseFat, deadAllFatF_eq]

def climbFatF (T : Tbl) (q r k : ℕ) (fs g : List ℕ) (bank : List Comparison) (value fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => value
  | fuel + 1 =>
    if CanRaiseFatF T q r k fs g value bank then climbFatF T q r k fs g bank (value + 1) fuel
    else value

theorem climbFatF_eq (q r k : ℕ) (fs g : List ℕ) (bank : List Comparison) (RB EB : ℕ) :
    ∀ fuel value, climbFatF (mkT q r (bank.map Comparison.degree) fs RB EB) q r k fs g bank value fuel =
      climbFat q r k fs g bank value fuel := by
  intro fuel
  induction fuel with
  | zero => intro value; rfl
  | succ n ih =>
    intro value
    simp only [climbFatF, climbFat]
    by_cases h : CanRaiseFat q r k fs g value bank
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ((canRaiseFatF_iff ..).mpr h)),
        ite_eq_left_of_eq_true _ _ (eq_true h), ih]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h' => h ((canRaiseFatF_iff ..).mp h'))),
        ite_eq_right_of_eq_false _ _ (eq_false h)]

def layersFatF (q r : ℕ) (bank : List Comparison) (fs : List ℕ) : ℕ → List ℕ
  | 0 => [1, r + 1]
  | k + 1 =>
    let g := layersFatF q r bank fs k
    let start := max (g.getD (k + 1) 0) (if k = 0 then 2 * r + 1 else 0)
    g ++ [climbFatF (tableAt q r bank fs k) q r k fs g bank start (g.getD (k + 1) 0 + r - start)]

theorem layersFatF_eq (q r : ℕ) (bank : List Comparison) (fs : List ℕ) :
    ∀ k, layersFatF q r bank fs k = layersFat q r bank fs k
  | 0 => rfl
  | k + 1 => by
    simp only [layersFatF, layersFat, tableAt, layersFatF_eq q r bank fs k, climbFatF_eq]

#print axioms advanceFat
#print axioms layersFat_sound
#print axioms layersFatF_eq

end LeanCH.BR.ShapeClimbFat
