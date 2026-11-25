import checkpoints.shen_extension.ShapeClimbFat
import checkpoints.shen_extension.ShapeClimbX

/-!
# The reach climb at roots that avoid a pattern

A root `u` *avoids* a pattern `A : List ℕ → ℕ → Bool` (`Avoids`) when `A` never matches its
actual layer widths, in the slot convention of `ShapeClimbX`: `ws` the exact widths of the first
layers, `last` an upper bound on the width of the next layer. `AvoidFloor q r A i a` says that
every root that avoids `A`, in every `q`-free digraph of out-degree exactly `r`, has at least
`a` labels within radius `i`.

`advanceA` is `ShapeClimbFat.advanceFat` with the root restriction given by `A` and the extra
globally sound pattern `X` of `ShapeClimbX` (`SoundX q r X`) added to the checker: a profile of
the root is dead when `A` matches it (the root avoids `A`), when `X` matches it, or when `Dead3`
holds (the rows of the ball bounded by floors `fs` valid for every root). `climbA`, `layersA`
repeat the climb, each radius starting from the previous value; `layersAF` is the same list over
the pruned search and the reach table of `ShapeClimbFast`.

Instances:
* `thinA r`: second layer at most `r - 1`. A fat root avoids it (`fat_avoids_thin`), so
  `AvoidFloor q r (thinA r)` floors are fat floors (`fatFloor_of_thin`).
* `tightA r`: second layer `r - 1` and third layer at most `r - 1`. A root that is not of that
  kind avoids it (`avoids_tight`).
* `notTightA r`: second layer not `r - 1` or third layer not `r - 1`. A root with second and
  third layers of exactly `r - 1` labels avoids it (`avoids_notTight`).

Everything is generic in `q`, `r` and the patterns.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.ShapeClimbAvoid
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion RecursivePrefixBudget
open ShapeClimbRoot ShapeClimbDead ShapeClimb ShapeClimbDead2 ShapeClimbDead3 ReachCapacity
open ShapeClimbX (SoundX)
open DotTwoPassShellTransport (layer shell layer_subset)

/-- The root `u` avoids the pattern `A`: no prefix of its exact layer widths, followed by any
upper bound on the next width, matches `A`. -/
def Avoids (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) (A : List ℕ → ℕ → Bool) : Prop :=
  ∀ (ws : List ℕ) (last : ℕ), (∀ i < ws.length, (layer D V (i + 1) u).card = ws.getD i 0) →
    (layer D V (ws.length + 1) u).card ≤ last → A ws last = false

/-- A floor for the roots of out-regular digraphs that avoid `A`. -/
def AvoidFloor (q r : ℕ) (A : List ℕ → ℕ → Bool) (i a : ℕ) : Prop :=
  ∀ (D : CH.Digraph) (V : Finset ℕ), QFree D V q → (∀ v ∈ V, (outN D V v).card = r) →
    ∀ u ∈ V, Avoids D V u A → a ≤ (ball D V u i).card

theorem avoidFloor_zero {q r : ℕ} {A : List ℕ → ℕ → Bool} {i : ℕ} : AvoidFloor q r A i 0 :=
  fun _ _ _ _ _ _ _ => Nat.zero_le _

theorem avoidFloor_max {q r : ℕ} {A : List ℕ → ℕ → Bool} {i a b : ℕ} (fa : AvoidFloor q r A i a)
    (fb : AvoidFloor q r A i b) : AvoidFloor q r A i (max a b) :=
  fun D V free reg u hu av => max_le (fa D V free reg u hu av) (fb D V free reg u hu av)

def deadAllA (A X : List ℕ → ℕ → Bool) (q r : ℕ) (degrees fs g : List ℕ) (k x c F : ℕ) : Bool :=
  (splits r k (x - 1 - c)).all
    (fun ws => !good g k ws ||
      (A (ws ++ [c]) (F - x) || X (ws ++ [c]) (F - x) || Dead3 q r degrees fs (ws ++ [c]) (F - x)))

def CanRaiseA (A X : List ℕ → ℕ → Bool) (q r k : ℕ) (fs g : List ℕ) (F : ℕ)
    (bank : List Comparison) : Prop :=
  ∀ x ∈ Icc (g.getD (k + 1) 0) F, ∀ c ∈ range (x - g.getD k 0 + 1),
    (bank.any (fun b => decide (Pass x c F r b.degree (q * b.degree + 1) (b.left + b.right))) ||
      deadAllA A X q r (bank.map Comparison.degree) fs g k x c F) = true

instance {A X q r k fs g F bank} : Decidable (CanRaiseA A X q r k fs g F bank) := by
  unfold CanRaiseA
  infer_instance

theorem advanceA {A X : List ℕ → ℕ → Bool} {q r k F : ℕ} {fs g : List ℕ}
    {bank : List Comparison} (sx : SoundX q r X)
    (floors : ∀ i, Floor q r i (fs.getD i 0)) (avs : ∀ i, AvoidFloor q r A i (g.getD i 0))
    (time : k + 2 ≤ q) (narrow : F < g.getD (k + 1) 0 + r)
    (sound : ∀ b ∈ bank, Valid q b ∧ b.degree ≤ r ∧ NoHost q b.degree)
    (check : CanRaiseA A X q r k fs g F bank) : AvoidFloor q r A (k + 2) (F + 1) := by
  intro D V free reg u hu av
  have deg : ∀ v ∈ V, r ≤ (outN D V v).card := fun v hv => (reg v hv).ge
  have root := reg u hu
  by_contra! small
  have prev := avs k D V free reg u hu av
  have start := avs (k + 1) D V free reg u hu av
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
      exact avs j D V free reg u hu av
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
    have next : (layer D V ((ws ++ [(layer D V (k + 1) u).card]).length + 1) u).card ≤
        F - (ball D V u (k + 1)).card := by
      rw [List.length_append, len, List.length_singleton]
      show (layer D V (k + 2) u).card ≤ _
      omega
    have d := List.all_eq_true.mp dead ws mem
    rw [ok, Bool.not_true, Bool.false_or, av _ _ exact' next, Bool.false_or] at d
    rcases Bool.or_eq_true_iff.mp d with dx | d3
    · exact sx D V u _ _ free deg hu root exact' next dx
    · refine dead3_false free deg hu root (degrees := bank.map Comparison.degree) ?_ floors
        exact' next d3
      intro t ht
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
      exact (sound b hb).2.2

def climbA (A X : List ℕ → ℕ → Bool) (q r k : ℕ) (fs g : List ℕ) (bank : List Comparison)
    (value fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => value
  | fuel + 1 =>
    if CanRaiseA A X q r k fs g value bank then climbA A X q r k fs g bank (value + 1) fuel
    else value

theorem climbA_sound {A X q r k fs g bank} (sx : SoundX q r X)
    (floors : ∀ i, Floor q r i (fs.getD i 0)) (avs : ∀ i, AvoidFloor q r A i (g.getD i 0))
    (time : k + 2 ≤ q) (sound : ∀ b ∈ bank, Valid q b ∧ b.degree ≤ r ∧ NoHost q b.degree)
    (fuel value : ℕ) (start : AvoidFloor q r A (k + 2) value)
    (budget : value + fuel ≤ g.getD (k + 1) 0 + r) :
    AvoidFloor q r A (k + 2) (climbA A X q r k fs g bank value fuel) := by
  induction fuel generalizing value with
  | zero => exact start
  | succ n ih =>
    simp only [climbA]
    split
    next check => exact ih _ (advanceA sx floors avs time (by omega) sound check) (by omega)
    next => exact start

/-- The floors at radii `0 … k + 1` of the roots that avoid `A`, from the global floors `fs`. -/
def layersA (A X : List ℕ → ℕ → Bool) (q r : ℕ) (bank : List Comparison) (fs : List ℕ) :
    ℕ → List ℕ
  | 0 => [1, r + 1]
  | k + 1 =>
    let g := layersA A X q r bank fs k
    g ++ [climbA A X q r k fs g bank (g.getD (k + 1) 0) r]

theorem layersA_sound {A X q r bank fs} (sx : SoundX q r X) (hq : 1 ≤ q)
    (sound : ∀ b ∈ bank, Valid q b ∧ b.degree ≤ r ∧ NoHost q b.degree)
    (floors : ∀ i, Floor q r i (fs.getD i 0)) (k : ℕ) (time : k + 1 ≤ q) :
    (layersA A X q r bank fs k).length = k + 2 ∧
      ∀ i, AvoidFloor q r A i ((layersA A X q r bank fs k).getD i 0) := by
  induction k with
  | zero =>
    refine ⟨rfl, fun i => ?_⟩
    match i with
    | 0 => exact fun D V _ _ u hu _ => card_pos.mpr ⟨u, self_mem_ball hu⟩
    | 1 =>
      intro D V free reg u hu _
      change r + 1 ≤ (ball D V u 1).card
      rw [ReachLedger.ball_one free hq hu, reg u hu]
    | i + 2 => simpa [layersA] using (avoidFloor_zero : AvoidFloor q r A (i + 2) 0)
  | succ k ih =>
    obtain ⟨len, avs⟩ := ih (by omega)
    set g := layersA A X q r bank fs k with hg
    have start : AvoidFloor q r A (k + 2) (g.getD (k + 1) 0) :=
      fun D V free reg u hu av => (avs (k + 1) D V free reg u hu av).trans
        (card_le_card (ball_mono_radius (Nat.le_succ (k + 1))))
    have top : AvoidFloor q r A (k + 2) (climbA A X q r k fs g bank (g.getD (k + 1) 0) r) :=
      climbA_sound sx floors avs time sound _ _ start le_rfl
    refine ⟨by simp [layersA, ← hg, len], fun i => ?_⟩
    simp only [layersA, ← hg]
    rcases Nat.lt_or_ge i (k + 2) with h | h
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact avs i
    · rcases Nat.eq_or_lt_of_le h with rfl | h
      · rw [List.getD_append_right _ _ _ _ (by omega), len, Nat.sub_self]
        exact top
      · rw [List.getD_eq_default _ _ (by simp [len]; omega)]
        exact avoidFloor_zero

/-! ### The same list over the pruned search -/

open ShapeClimbFast

def deadAllAF (T : Tbl) (A X : List ℕ → ℕ → Bool) (q r : ℕ) (degrees fs g : List ℕ)
    (k x c F : ℕ) : Bool :=
  deadAllF r g (fun ws => A (ws ++ [c]) (F - x) || X (ws ++ [c]) (F - x) ||
      Dead3F T q r degrees fs (ws ++ [c]) (F - x))
    (fun _ => false) (peelCap q r degrees) k (x - 1 - c)

theorem deadAllAF_eq (A X : List ℕ → ℕ → Bool) (q r : ℕ) (degrees fs g : List ℕ)
    (RB EB k x c F : ℕ) :
    deadAllAF (mkT q r degrees fs RB EB) A X q r degrees fs g k x c F =
      deadAllA A X q r degrees fs g k x c F := by
  rw [deadAllAF, deadAllF_eq _ _ _ _ _
    (fun _ _ h => by simp at h)
    (fun pre a rest h => by
      rw [dead3_of_cap _ q r degrees fs c (F - x) pre a rest h, Bool.or_true])]
  unfold deadAllA
  refine all_congr' (fun ws _ => ?_)
  rw [dead3F_eq]

def CanRaiseAF (T : Tbl) (A X : List ℕ → ℕ → Bool) (q r k : ℕ) (fs g : List ℕ) (F : ℕ)
    (bank : List Comparison) : Prop :=
  ∀ x ∈ Icc (g.getD (k + 1) 0) F, ∀ c ∈ range (x - g.getD k 0 + 1),
    (bank.any (fun b => decide (Pass x c F r b.degree (q * b.degree + 1) (b.left + b.right))) ||
      deadAllAF T A X q r (bank.map Comparison.degree) fs g k x c F) = true

instance {T A X q r k fs g F bank} : Decidable (CanRaiseAF T A X q r k fs g F bank) := by
  unfold CanRaiseAF; infer_instance

theorem canRaiseAF_iff (A X : List ℕ → ℕ → Bool) (q r k : ℕ) (fs g : List ℕ) (F : ℕ)
    (bank : List Comparison) (RB EB : ℕ) :
    CanRaiseAF (mkT q r (bank.map Comparison.degree) fs RB EB) A X q r k fs g F bank ↔
      CanRaiseA A X q r k fs g F bank := by
  simp only [CanRaiseAF, CanRaiseA, deadAllAF_eq]

def climbAF (T : Tbl) (A X : List ℕ → ℕ → Bool) (q r k : ℕ) (fs g : List ℕ)
    (bank : List Comparison) (value fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => value
  | fuel + 1 =>
    if CanRaiseAF T A X q r k fs g value bank then climbAF T A X q r k fs g bank (value + 1) fuel
    else value

theorem climbAF_eq (A X : List ℕ → ℕ → Bool) (q r k : ℕ) (fs g : List ℕ)
    (bank : List Comparison) (RB EB : ℕ) :
    ∀ fuel value, climbAF (mkT q r (bank.map Comparison.degree) fs RB EB) A X q r k fs g bank
      value fuel = climbA A X q r k fs g bank value fuel := by
  intro fuel
  induction fuel with
  | zero => intro value; rfl
  | succ n ih =>
    intro value
    simp only [climbAF, climbA]
    by_cases h : CanRaiseA A X q r k fs g value bank
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ((canRaiseAF_iff ..).mpr h)),
        ite_eq_left_of_eq_true _ _ (eq_true h), ih]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h' => h ((canRaiseAF_iff ..).mp h'))),
        ite_eq_right_of_eq_false _ _ (eq_false h)]

def layersAF (A X : List ℕ → ℕ → Bool) (q r : ℕ) (bank : List Comparison) (fs : List ℕ) :
    ℕ → List ℕ
  | 0 => [1, r + 1]
  | k + 1 =>
    let g := layersAF A X q r bank fs k
    g ++ [climbAF (tableAt q r bank fs k) A X q r k fs g bank (g.getD (k + 1) 0) r]

theorem layersAF_eq (A X : List ℕ → ℕ → Bool) (q r : ℕ) (bank : List Comparison)
    (fs : List ℕ) : ∀ k, layersAF A X q r bank fs k = layersA A X q r bank fs k
  | 0 => rfl
  | k + 1 => by
    simp only [layersAF, layersA, tableAt, layersAF_eq A X q r bank fs k, climbAF_eq]

/-! ### Avoidance patterns -/

/-- The empty extra pattern, sound for every root. -/
def noX : List ℕ → ℕ → Bool := fun _ _ => false

theorem noX_sound (q r : ℕ) : SoundX q r noX := fun _ _ _ _ _ _ _ _ _ _ _ h => by
  simp [noX] at h

/-- The root's second layer has at most `r - 1` labels. -/
def thinA (r : ℕ) (ws : List ℕ) (last : ℕ) : Bool :=
  decide (2 ≤ ws.length ∧ ws.getD 1 0 + 1 ≤ r) || decide (ws.length = 1 ∧ last + 1 ≤ r)

/-- A fat root avoids `thinA r`. -/
theorem fat_avoids_thin {D : CH.Digraph} {V : Finset ℕ} {r u : ℕ}
    (fat : r ≤ (layer D V 2 u).card) : Avoids D V u (thinA r) := by
  intro ws last exact bound
  simp only [thinA, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  constructor
  · rintro ⟨len, w2⟩
    have l2 : (layer D V 2 u).card = ws.getD 1 0 := exact 1 (by omega)
    omega
  · rintro ⟨len, w2⟩
    rw [show ws.length + 1 = 2 by omega] at bound
    omega

/-- Floors of the roots that avoid `thinA r` are fat floors. -/
theorem fatFloor_of_thin {q r i a : ℕ} (h : AvoidFloor q r (thinA r) i a) :
    ShapeClimbFat.FatFloor q r i a :=
  fun D V free reg u hu fat => h D V free reg u hu (fat_avoids_thin fat)

/-- The root's second layer has `r - 1` labels and its third layer at most `r - 1`. -/
def tightA (r : ℕ) (ws : List ℕ) (last : ℕ) : Bool :=
  decide (2 ≤ ws.length ∧ ws.getD 1 0 + 1 = r ∧
    (if 3 ≤ ws.length then ws.getD 2 0 else last) + 1 ≤ r)

/-- A root that does not have (second layer `r - 1`, third layer at most `r - 1`) avoids
`tightA r`. -/
theorem avoids_tight {D : CH.Digraph} {V : Finset ℕ} {r u : ℕ}
    (h : ¬((layer D V 2 u).card + 1 = r ∧ (layer D V 3 u).card + 1 ≤ r)) :
    Avoids D V u (tightA r) := by
  intro ws last exact bound
  simp only [tightA, decide_eq_false_iff_not]
  rintro ⟨len, w2, w3⟩
  have l2 : (layer D V 2 u).card = ws.getD 1 0 := exact 1 (by omega)
  by_cases long : 3 ≤ ws.length
  · have l3 : (layer D V 3 u).card = ws.getD 2 0 := exact 2 (by omega)
    simp only [long, ↓reduceIte] at w3
    exact h ⟨by omega, by omega⟩
  · simp only [long, ↓reduceIte] at w3
    rw [show ws.length + 1 = 3 by omega] at bound
    exact h ⟨by omega, by omega⟩

/-- The profile contradicts (second layer `r - 1`, third layer `r - 1`). -/
def notTightA (r : ℕ) (ws : List ℕ) (last : ℕ) : Bool :=
  decide ((2 ≤ ws.length ∧ ws.getD 1 0 + 1 ≠ r) ∨ (3 ≤ ws.length ∧ ws.getD 2 0 + 1 ≠ r) ∨
    ((ws.length = 1 ∨ ws.length = 2) ∧ last + 2 ≤ r))

/-- A root with second and third layers of exactly `r - 1` labels avoids `notTightA r`. -/
theorem avoids_notTight {D : CH.Digraph} {V : Finset ℕ} {r u : ℕ}
    (h2 : (layer D V 2 u).card + 1 = r) (h3 : (layer D V 3 u).card + 1 = r) :
    Avoids D V u (notTightA r) := by
  intro ws last exact bound
  simp only [notTightA, decide_eq_false_iff_not]
  rintro (⟨len, w2⟩ | ⟨len, w3⟩ | ⟨len | len, w⟩)
  · have l2 : (layer D V 2 u).card = ws.getD 1 0 := exact 1 (by omega)
    omega
  · have l3 : (layer D V 3 u).card = ws.getD 2 0 := exact 2 (by omega)
    omega
  · rw [show ws.length + 1 = 2 by omega] at bound
    omega
  · rw [show ws.length + 1 = 3 by omega] at bound
    omega

/-- Floors of the roots that avoid `tightA r`, read at a root that is not tight. -/
theorem ball_of_tight {q r i a : ℕ} (h : AvoidFloor q r (tightA r) i a) {D : CH.Digraph}
    {V : Finset ℕ} (free : QFree D V q) (reg : ∀ v ∈ V, (outN D V v).card = r) {u : ℕ}
    (hu : u ∈ V) (nt : ¬((layer D V 2 u).card + 1 = r ∧ (layer D V 3 u).card + 1 ≤ r)) :
    a ≤ (ball D V u i).card :=
  h D V free reg u hu (avoids_tight nt)

/-- Floors of the roots that avoid `notTightA r`, read at a tight root. -/
theorem ball_of_notTight {q r i a : ℕ} (h : AvoidFloor q r (notTightA r) i a) {D : CH.Digraph}
    {V : Finset ℕ} (free : QFree D V q) (reg : ∀ v ∈ V, (outN D V v).card = r) {u : ℕ}
    (hu : u ∈ V) (h2 : (layer D V 2 u).card + 1 = r) (h3 : (layer D V 3 u).card + 1 = r) :
    a ≤ (ball D V u i).card :=
  h D V free reg u hu (avoids_notTight h2 h3)

#print axioms advanceA
#print axioms layersA_sound
#print axioms layersAF_eq
#print axioms fat_avoids_thin
#print axioms fatFloor_of_thin
#print axioms avoids_tight
#print axioms avoids_notTight
#print axioms ball_of_tight
#print axioms ball_of_notTight
end LeanCH.BR.ShapeClimbAvoid
