import checkpoints.shen_extension.ShapeClimbDead2
import checkpoints.shen_extension.ReachCapacity

/-!
# The climb with the local-reach capacity

`Dead3 q r degrees fs ws last` is `Dead2` or `ReachCapacity.ReachDead`: the retained-layer reach
count of the punctured `R`-ball at some cut `R`, with the radius floors `fs` already proved,
overflows the capacity `|F| (|F| + 1)` at radii `a`, `q - a`. `dead3_false` is its soundness;
`advance3`, `climb3`, `layers3` repeat the climb of `ShapeClimbDead2` with `Dead3`. Generic in
`q` and `r`.
-/

namespace LeanCH.BR.ShapeClimbDead3
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion RecursivePrefixBudget
open ShapeClimbRoot ShapeClimbDead ShapeClimb ShapeClimbDead2 ReachCapacity
open DotTwoPassShellTransport (layer shell layer_subset)

def Dead3 (q r : ℕ) (degrees fs ws : List ℕ) (last : ℕ) : Bool :=
  Dead2 q r degrees ws last || ReachDead q r degrees fs ws last

/-- **Soundness of the checker with the reach capacity.** -/
theorem dead3_false {D : CH.Digraph} {V : Finset ℕ} {q r u : ℕ} {ws : List ℕ} {last : ℕ}
    {degrees fs : List ℕ} (free : QFree D V q) (deg : ∀ v ∈ V, r ≤ (outN D V v).card)
    (hu : u ∈ V) (root : (outN D V u).card = r) (lower : ∀ t ∈ degrees, NoHost q t)
    (floors : ∀ j, Floor q r j (fs.getD j 0))
    (exact : ∀ i < ws.length, (layer D V (i + 1) u).card = ws.getD i 0)
    (bound : (layer D V (ws.length + 1) u).card ≤ last)
    (dead : Dead3 q r degrees fs ws last = true) : False := by
  rcases Bool.or_eq_true_iff.mp dead with d | d
  · exact dead2_false free deg hu root lower exact bound d
  · exact reach_false free deg hu floors lower exact bound d

/-! ### The climb with `Dead3` -/

def deadAll3 (q r : ℕ) (degrees fs : List ℕ) (k x c F : ℕ) : Bool :=
  (splits r k (x - 1 - c)).all
    (fun ws => !good fs k ws || Dead3 q r degrees fs (ws ++ [c]) (F - x))

def CanRaise3 (q r k : ℕ) (fs : List ℕ) (F : ℕ) (bank : List Comparison) : Prop :=
  ∀ x ∈ Icc (fs.getD (k + 1) 0) F, ∀ c ∈ range (x - fs.getD k 0 + 1),
    (bank.any (fun b => decide (Pass x c F r b.degree (q * b.degree + 1) (b.left + b.right))) ||
      deadAll3 q r (bank.map Comparison.degree) fs k x c F) = true

instance {q r k fs F bank} : Decidable (CanRaise3 q r k fs F bank) := by
  unfold CanRaise3
  infer_instance

theorem advance3 {q r k F : ℕ} {fs : List ℕ} {bank : List Comparison}
    (floors : ∀ i, Floor q r i (fs.getD i 0)) (time : k + 2 ≤ q)
    (narrow : F < fs.getD (k + 1) 0 + r)
    (sound : ∀ b ∈ bank, Valid q b ∧ b.degree ≤ r ∧ NoHost q b.degree)
    (check : CanRaise3 q r k fs F bank) : Floor q r (k + 2) (F + 1) := by
  intro D V free deg u hu
  obtain ⟨E, -, -, root, degE, freeE, balls⟩ := exact_root (deg u hu) free deg
  refine le_trans ?_ (card_le_card (balls (k + 2)))
  by_contra! small
  have prev := floors k E V freeE degE u hu
  have start := floors (k + 1) E V freeE degE u hu
  have inc : (ball E V u (k + 1)).card ≤ (ball E V u (k + 2)).card :=
    card_le_card (ball_mono_radius (by omega))
  have lay : (ball E V u (k + 1)).card = (layer E V (k + 1) u).card + (ball E V u k).card :=
    card_ball_succ k
  have sh : (ball E V u (k + 2)).card = (layer E V (k + 2) u).card + (ball E V u (k + 1)).card :=
    card_ball_succ (k + 1)
  have shl : shell E V (k + 1) u = layer E V (k + 2) u := by
    simp only [shell, layer, show k + 2 - 1 = k + 1 by omega]
  have hc := check (ball E V u (k + 1)).card (mem_Icc.mpr ⟨start, by omega⟩)
    (layer E V (k + 1) u).card (mem_range.mpr (by omega))
  rcases Bool.or_eq_true_iff.mp hc with pass | dead
  · obtain ⟨b, hb, pass⟩ := List.any_eq_true.mp pass
    obtain ⟨⟨left, right⟩, fit, lower⟩ := sound b hb
    obtain ⟨G, Q, hG, _, hL, quad, cap⟩ := prefix_completion (by omega : q / 2 + (q - q / 2) ≤ q)
      (order_of_noHost lower) left right fit freeE degE hu time (by rw [shl]; omega)
    exact pass_false (F := F) (card_erase_add_one (self_mem_ball hu)) (by rw [shl]; omega)
      hG hL quad cap (of_decide_eq_true pass)
  · set ws := (List.range k).map (fun j => (layer E V (j + 1) u).card) with hws
    have len : ws.length = k := by simp [hws]
    have exact : ∀ i < ws.length, (layer E V (i + 1) u).card = ws.getD i 0 :=
      fun i hi => (widths_getD (by omega)).symm
    have size := ball_card_take hu exact (n := k) len.ge
    rw [List.take_of_length_le (by omega)] at size
    have mem : ws ∈ splits r k ((ball E V u (k + 1)).card - 1 - (layer E V (k + 1) u).card) := by
      refine mem_splits len (by omega) (fun pos => ?_)
      rw [widths_getD pos]
      exact layer_one_card freeE (by omega) hu root
    have ok : good fs k ws = true := by
      refine List.all_eq_true.mpr (fun j hj => decide_eq_true ?_)
      rw [List.mem_range] at hj
      rw [← ball_card_take hu exact (by omega)]
      exact floors j E V freeE degE u hu
    have d := List.all_eq_true.mp dead ws mem
    rw [ok, Bool.not_true, Bool.false_or] at d
    refine dead3_false freeE degE hu root (degrees := bank.map Comparison.degree) ?_ floors ?_ ?_ d
    · intro t ht
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
      exact (sound b hb).2.2
    · intro i hi
      rw [List.length_append, len, List.length_singleton] at hi
      rcases Nat.lt_or_ge i k with h | h
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact exact i (by omega)
      · obtain rfl : i = k := by omega
        rw [List.getD_append_right _ _ _ _ (by omega), len, Nat.sub_self]
        rfl
    · rw [List.length_append, len, List.length_singleton]
      show (layer E V (k + 2) u).card ≤ _
      omega

def climb3 (q r k : ℕ) (fs : List ℕ) (bank : List Comparison) (value fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => value
  | fuel + 1 => if CanRaise3 q r k fs value bank then climb3 q r k fs bank (value + 1) fuel else value

theorem climb3_sound {q r k fs bank} (floors : ∀ i, Floor q r i (fs.getD i 0))
    (time : k + 2 ≤ q) (sound : ∀ b ∈ bank, Valid q b ∧ b.degree ≤ r ∧ NoHost q b.degree)
    (fuel value : ℕ) (start : Floor q r (k + 2) value)
    (budget : value + fuel ≤ fs.getD (k + 1) 0 + r) :
    Floor q r (k + 2) (climb3 q r k fs bank value fuel) := by
  induction fuel generalizing value with
  | zero => exact start
  | succ n ih =>
    simp only [climb3]
    split
    next check => exact ih _ (advance3 floors time (by omega) sound check) (by omega)
    next => exact start

/-- The floors at radii `0 … k + 1` with the reach-capacity checker. -/
def layers3 (q r : ℕ) (bank : List Comparison) : ℕ → List ℕ
  | 0 => [1, r + 1]
  | k + 1 =>
    let fs := layers3 q r bank k
    fs ++ [climb3 q r k fs bank (fs.getD (k + 1) 0) r]

theorem layers3_sound {q r bank} (hq : 1 ≤ q)
    (sound : ∀ b ∈ bank, Valid q b ∧ b.degree ≤ r ∧ NoHost q b.degree) (k : ℕ) (time : k + 1 ≤ q) :
    (layers3 q r bank k).length = k + 2 ∧ ∀ i, Floor q r i ((layers3 q r bank k).getD i 0) := by
  induction k with
  | zero =>
    refine ⟨rfl, fun i => ?_⟩
    match i with
    | 0 => exact fun D V _ _ u hu => card_pos.mpr ⟨u, self_mem_ball hu⟩
    | 1 =>
      intro D V free deg u hu
      change r + 1 ≤ (ball D V u 1).card
      rw [ReachLedger.ball_one free hq hu]
      have := deg u hu
      omega
    | i + 2 => simpa [layers3] using (floor_zero : Floor q r (i + 2) 0)
  | succ k ih =>
    obtain ⟨len, floors⟩ := ih (by omega)
    have top := climb3_sound (bank := bank) floors time sound r ((layers3 q r bank k).getD (k + 1) 0)
      (fun D V free deg u hu => (floors (k + 1) D V free deg u hu).trans
        (card_le_card (ball_mono_radius (Nat.le_succ (k + 1))))) le_rfl
    refine ⟨by simp [layers3, len], fun i => ?_⟩
    simp only [layers3]
    rcases Nat.lt_or_ge i (k + 2) with h | h
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact floors i
    · rcases Nat.eq_or_lt_of_le h with rfl | h
      · rw [List.getD_append_right _ _ _ _ (by omega), len, Nat.sub_self]
        exact top
      · rw [List.getD_eq_default _ _ (by simp [len]; omega)]
        exact floor_zero

#print axioms dead3_false
#print axioms layers3_sound

end LeanCH.BR.ShapeClimbDead3
