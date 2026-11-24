import checkpoints.shen_extension.RecursivePrefixBudget
import checkpoints.shen_extension.ShapeClimbDead

/-!
# The ball climb with layer-shape exclusions

`advance'` extends `RecursivePrefixBudget.advance`. A root profile `(x, c)`,
`x = |ball (k + 1)|`, `c = |layer (k + 1)|`, with target `F` for `|ball (k + 2)|`, passes if
the old comparison bank passes it, or if every split of the inner layers into widths
`ws = [|L 1|, …, |L k|]` (first width `r`, sum `x - 1 - c`, every prefix above the floors
already proved) is `Dead` with the slot `c` appended and the bound `F - x` for the next
layer. The root is first trimmed to out-degree exactly `r` (`exact_root`), so the floors
carry no exact-degree hypothesis. Everything is generic in `q` and `r`.
-/

namespace LeanCH.BR.ShapeClimb
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion RecursivePrefixBudget
open ShapeClimbRoot ShapeClimbDead
open DotTwoPassShellTransport (layer shell)

/-! ### Enumerating the splits -/

/-- All lists of `n` naturals with sum `s`. -/
def comps : ℕ → ℕ → List (List ℕ)
  | 0, s => if s = 0 then [[]] else []
  | n + 1, s => (List.range (s + 1)).flatMap (fun a => (comps n (s - a)).map (a :: ·))

theorem mem_comps : ∀ (l : List ℕ) (n s : ℕ), l.length = n → l.sum = s → l ∈ comps n s
  | [], n, s, hl, hs => by
    subst hl
    simp only [List.sum_nil] at hs
    subst hs
    simp [comps]
  | a :: t, n, s, hl, hs => by
    cases n with
    | zero => simp at hl
    | succ n =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [List.sum_cons] at hs
      simp only [comps, List.mem_flatMap, List.mem_range, List.mem_map]
      exact ⟨a, by omega, t, mem_comps t n (s - a) hl (by omega), rfl⟩

/-- Inner splits of `s` into `k` widths, the first equal to `r`. -/
def splits (r k s : ℕ) : List (List ℕ) :=
  match k with
  | 0 => if s = 0 then [[]] else []
  | k + 1 => if r ≤ s then (comps k (s - r)).map (r :: ·) else []

theorem mem_splits {r s : ℕ} : ∀ {k : ℕ} {ws : List ℕ}, ws.length = k → ws.sum = s →
    (0 < k → ws.getD 0 0 = r) → ws ∈ splits r k s
  | 0, ws, hl, hs, _ => by
    rw [List.length_eq_zero_iff] at hl
    subst hl
    simp only [List.sum_nil] at hs
    subst hs
    simp [splits]
  | k + 1, ws, hl, hs, hh => by
    cases ws with
    | nil => simp at hl
    | cons a t =>
      have a_r : a = r := by simpa using hh (by omega)
      subst a_r
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [List.sum_cons] at hs
      simp only [splits, show a ≤ s by omega, ite_true, List.mem_map]
      exact ⟨t, mem_comps t k (s - a) hl (by omega), rfl⟩

/-- A split respects the floors `fs` at radii `0 … k`. -/
def good (fs : List ℕ) (k : ℕ) (ws : List ℕ) : Bool :=
  (List.range (k + 1)).all (fun j => decide (fs.getD j 0 ≤ 1 + (ws.take j).sum))

/-- Every admissible split of a profile is dead. -/
def deadAll (q r : ℕ) (degrees fs : List ℕ) (k x c F : ℕ) : Bool :=
  (splits r k (x - 1 - c)).all (fun ws => !good fs k ws || Dead q r degrees (ws ++ [c]) (F - x))

/-- The raise test at radius `k + 2` from the floors `fs` (indexed by radius): each profile
passes the bank or has only dead splits. -/
def CanRaise' (q r k : ℕ) (fs : List ℕ) (F : ℕ) (bank : List Comparison) : Prop :=
  ∀ x ∈ Icc (fs.getD (k + 1) 0) F, ∀ c ∈ range (x - fs.getD k 0 + 1),
    (bank.any (fun b => decide (Pass x c F r b.degree (q * b.degree + 1) (b.left + b.right))) ||
      deadAll q r (bank.map Comparison.degree) fs k x c F) = true

instance {q r k fs F bank} : Decidable (CanRaise' q r k fs F bank) := by
  unfold CanRaise'
  infer_instance

/-! ### The advance -/

theorem widths_getD {D : CH.Digraph} {V : Finset ℕ} {u k i : ℕ} (h : i < k) :
    ((List.range k).map (fun j => (layer D V (j + 1) u).card)).getD i 0 =
      (layer D V (i + 1) u).card := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem advance' {q r k F : ℕ} {fs : List ℕ} {bank : List Comparison}
    (floors : ∀ i, Floor q r i (fs.getD i 0)) (time : k + 2 ≤ q)
    (narrow : F < fs.getD (k + 1) 0 + r)
    (sound : ∀ b ∈ bank, Valid q b ∧ b.degree ≤ r ∧ NoHost q b.degree)
    (check : CanRaise' q r k fs F bank) : Floor q r (k + 2) (F + 1) := by
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
  · -- the actual split of the inner layers
    set ws := (List.range k).map (fun j => (layer E V (j + 1) u).card) with hws
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
    refine dead_false freeE degE hu root (degrees := bank.map Comparison.degree) ?_ ?_ ?_ d
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

/-! ### The climb -/

def climb' (q r k : ℕ) (fs : List ℕ) (bank : List Comparison) (value fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => value
  | fuel + 1 => if CanRaise' q r k fs value bank then climb' q r k fs bank (value + 1) fuel else value

theorem climb'_sound {q r k fs bank} (floors : ∀ i, Floor q r i (fs.getD i 0))
    (time : k + 2 ≤ q) (sound : ∀ b ∈ bank, Valid q b ∧ b.degree ≤ r ∧ NoHost q b.degree)
    (fuel value : ℕ) (start : Floor q r (k + 2) value) (budget : value + fuel ≤ fs.getD (k + 1) 0 + r) :
    Floor q r (k + 2) (climb' q r k fs bank value fuel) := by
  induction fuel generalizing value with
  | zero => exact start
  | succ n ih =>
    simp only [climb']
    split
    next check => exact ih _ (advance' floors time (by omega) sound check) (by omega)
    next => exact start

/-- The floors at radii `0 … k + 1`, indexed by radius. -/
def layers' (q r : ℕ) (bank : List Comparison) : ℕ → List ℕ
  | 0 => [1, r + 1]
  | k + 1 =>
    let fs := layers' q r bank k
    fs ++ [climb' q r k fs bank (fs.getD (k + 1) 0) r]

theorem layers'_sound {q r bank} (hq : 1 ≤ q)
    (sound : ∀ b ∈ bank, Valid q b ∧ b.degree ≤ r ∧ NoHost q b.degree) (k : ℕ) (time : k + 1 ≤ q) :
    (layers' q r bank k).length = k + 2 ∧ ∀ i, Floor q r i ((layers' q r bank k).getD i 0) := by
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
    | i + 2 => simpa [layers'] using (floor_zero : Floor q r (i + 2) 0)
  | succ k ih =>
    obtain ⟨len, floors⟩ := ih (by omega)
    have top := climb'_sound (bank := bank) floors time sound r ((layers' q r bank k).getD (k + 1) 0)
      (fun D V free deg u hu => (floors (k + 1) D V free deg u hu).trans
        (card_le_card (ball_mono_radius (Nat.le_succ (k + 1))))) le_rfl
    refine ⟨by simp [layers', len], fun i => ?_⟩
    simp only [layers']
    rcases Nat.lt_or_ge i (k + 2) with h | h
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact floors i
    · rcases Nat.eq_or_lt_of_le h with rfl | h
      · rw [List.getD_append_right _ _ _ _ (by omega), len, Nat.sub_self]
        exact top
      · rw [List.getD_eq_default _ _ (by simp [len]; omega)]
        exact floor_zero

def middle' (q r : ℕ) (bank : List Comparison) : Comparison :=
  let fs := layers' q r bank (q / 2)
  ⟨r, fs.getD (q / 2) 0, if q - q / 2 = q / 2 then fs.getD (q / 2) 0 else fs.getD (q / 2 + 1) 0⟩

theorem middle'_valid {q r bank} (hq : 2 ≤ q)
    (sound : ∀ b ∈ bank, Valid q b ∧ b.degree ≤ r ∧ NoHost q b.degree) :
    Valid q (middle' q r bank) := by
  obtain ⟨-, fl⟩ := layers'_sound (by omega : 1 ≤ q) sound (q / 2) (by omega)
  refine ⟨fl (q / 2), ?_⟩
  change Floor q r (q - q / 2) (if q - q / 2 = q / 2 then _ else _)
  split
  next e => simpa only [e] using fl (q / 2)
  next e => simpa only [show q - q / 2 = q / 2 + 1 by omega] using fl (q / 2 + 1)

/-- The top-degree comparison from the new climb, over the old library of lower degrees. -/
def result' (q d : ℕ) := middle' q d (library q (d - 1))

/-- The floors of the new climb at radii `0 … q/2 + 1`. -/
def floors' (q d : ℕ) := layers' q d (library q (d - 1)) (q / 2)

theorem library_bank {q d} (hq : 2 ≤ q) (hd : 0 < d) (known : ∀ t, t < d → NoHost q t) :
    ∀ c ∈ library q (d - 1), Valid q c ∧ c.degree ≤ d ∧ NoHost q c.degree := by
  have prev := library_sound hq (d - 1) (fun t ht => known t (by omega))
  exact fun c hc => ⟨(prev c hc).1, by have := (prev c hc).2; omega,
    known _ (by have := (prev c hc).2; omega)⟩

theorem result'_valid {q d} (hq : 2 ≤ q) (hd : 0 < d) (known : ∀ t, t < d → NoHost q t) :
    Valid q (result' q d) :=
  middle'_valid hq (library_bank hq hd known)

def strictGain' (q d : ℕ) (b : Comparison) : Prop :=
  2 * (q / 2 / 2) = q / 2 ∧
    b.left + 2 ≤ 2 * (layers' q d (library q (d - 1)) (q / 2 / 2)).getD (q / 2 / 2) 0

instance {q d b} : Decidable (strictGain' q d b) := by unfold strictGain'; infer_instance

/-- The order bound from the new floors, with the Seymour equality test of `bound`. -/
def bound' (q d : ℕ) : ℕ :=
  let b := result' q d
  b.left + b.right + (if strictGain' q d b then 1 else 0) - 2

theorem bound_sound' {q d} (hq : 2 ≤ q) (hd : 0 < d) (known : ∀ t, t < d → NoHost q t)
    {D V} (free : QFree D V q) (ne : V.Nonempty) (deg : ∀ v ∈ V, d ≤ (outN D V v).card) :
    bound' q d < V.card := by
  let b := result' q d
  obtain ⟨left, right⟩ := result'_valid hq hd known
  change Floor q d (q / 2) b.left at left
  change Floor q d (q - q / 2) b.right at right
  change b.left + b.right + (if strictGain' q d b then 1 else 0) - 2 < V.card
  have pos := card_pos.mpr ne
  split
  next gain =>
    obtain ⟨eq, more⟩ := gain
    obtain ⟨-, bank⟩ := layers'_sound (by omega : 1 ≤ q) (library_bank hq hd known) (q / 2 / 2)
      (by omega)
    have size := SharedBankOrderTransfer.strict_order (k := q / 2 / 2) free ne
      (by omega : 2 * (q / 2 / 2) + (q - q / 2) ≤ q) (bank (q / 2 / 2) D V free deg)
      (eq.symm ▸ left D V free deg) (right D V free deg) more
    omega
  next =>
    have size := order_of_floors (by omega : q / 2 + (q - q / 2) ≤ q) left right D V free deg ne
    omega

end LeanCH.BR.ShapeClimb

/-! ### The order window, parallel to `RecursivePrefixBudget.Window` -/

namespace LeanCH.BR.ShapeClimb
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion CHRuleCatalog ProjectedQuotaTransfer

@[ch_numeric_guard] def Window (n r q limit : ℕ) : Prop :=
  let d := min r limit
  2≤q ∧ 0<d ∧ 0<bound' q d ∧ n+d≤bound' q d+r

instance {n r q limit} : Decidable (Window n r q limit) := by unfold Window; infer_instance

theorem excluded {p : Input} {limit} (bad : Bad p) (known : ∀t,t<limit → NoHost (cutoff p) t) :
    ¬Window p.n p.s (cutoff p) limit := by
  rintro ⟨cut,pos,live,paid⟩
  have certificate : GuardedFamilyRules.OrderBound (cutoff p) (min p.s limit) (bound' (cutoff p) (min p.s limit)) :=
    ⟨live, fun _ _ free ne deg => bound_sound' cut pos
      (fun t ht => known t (ht.trans_le (min_le_right ..))) free ne deg⟩
  exact GuardedFamilyRules.forbidden bad certificate ⟨le_rfl,min_le_left ..,paid⟩

theorem at_completed {p : Input} (bad : Bad p) :
    ¬Window p.n p.s (cutoff p) projectionFloor := excluded bad (available_lower_hosts bad)

attribute [aesop safe forward (immediate := [floors,time,narrow,sound,check]) (rule_sets := [CHGraphFamilies])] advance'
attribute [aesop safe forward (immediate := [bad,known]) (rule_sets := [CHGraphFamilies])] excluded
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] at_completed

#print axioms advance'
#print axioms layers'_sound
#print axioms bound_sound'
#print axioms excluded
#print axioms at_completed
end LeanCH.BR.ShapeClimb
