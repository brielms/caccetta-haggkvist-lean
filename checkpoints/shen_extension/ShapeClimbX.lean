import checkpoints.shen_extension.ShapeClimbFast
import checkpoints.shen_extension.ShapeClimbMono
import checkpoints.shen_extension.LoopCollar

/-!
# The reach climb with an extra dead pattern, and the collar dip

`SoundX q r X` says that no root of out-degree exactly `r` in a `q`-free digraph of minimum
out-degree `r` has layer widths matched by `X ws last` (`ws` the exact widths of the first
layers, `last` a bound on the next). The climb `layersX` is the seeded climb of
`ShapeClimbMono` with `X` added to the checker `Dead3`; `layersX_sound` is its soundness, and
`layersXF` the same list over the pruned search.

The instance is the collar dip. `collar_third`: a root with exactly `q + 1` heads, each of
out-degree at least `r ≤ q + 1`, whose second layer has at most `r - 1` labels, has at least
`r` labels in its third layer. (By `LoopCollar.collar` the heads point to the whole second
layer, so the second layer has no arc back to the heads or the root; it has at most `q` labels,
so it has a sink, and all `r` heads of the sink are new.) `collarDip q r` is that pattern for
`r = q + 1`.

Everything is generic in `q`, `r` and the pattern.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.ShapeClimbX
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion RecursivePrefixBudget
open ShapeClimbRoot ShapeClimbDead ShapeClimb ShapeClimbDead2 ShapeClimbDead3 ReachCapacity
open DotTwoPassShellTransport (layer shell layer_subset)

/-- An extra dead pattern on the layer widths of a root of out-degree exactly `r`. -/
def SoundX (q r : ℕ) (X : List ℕ → ℕ → Bool) : Prop :=
  ∀ (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) (ws : List ℕ) (last : ℕ), QFree D V q →
    (∀ v ∈ V, r ≤ (outN D V v).card) → u ∈ V → (outN D V u).card = r →
    (∀ i < ws.length, (layer D V (i + 1) u).card = ws.getD i 0) →
    (layer D V (ws.length + 1) u).card ≤ last → X ws last = true → False

def deadAllX (X : List ℕ → ℕ → Bool) (q r : ℕ) (degrees fs : List ℕ) (k x c F : ℕ) : Bool :=
  (splits r k (x - 1 - c)).all
    (fun ws => !good fs k ws ||
      (X (ws ++ [c]) (F - x) || Dead3 q r degrees fs (ws ++ [c]) (F - x)))

def CanRaiseX (X : List ℕ → ℕ → Bool) (q r k : ℕ) (fs : List ℕ) (F : ℕ)
    (bank : List Comparison) : Prop :=
  ∀ x ∈ Icc (fs.getD (k + 1) 0) F, ∀ c ∈ range (x - fs.getD k 0 + 1),
    (bank.any (fun b => decide (Pass x c F r b.degree (q * b.degree + 1) (b.left + b.right))) ||
      deadAllX X q r (bank.map Comparison.degree) fs k x c F) = true

instance {X q r k fs F bank} : Decidable (CanRaiseX X q r k fs F bank) := by
  unfold CanRaiseX
  infer_instance

theorem advanceX {X : List ℕ → ℕ → Bool} {q r k F : ℕ} {fs : List ℕ} {bank : List Comparison}
    (sx : SoundX q r X) (floors : ∀ i, Floor q r i (fs.getD i 0)) (time : k + 2 ≤ q)
    (narrow : F < fs.getD (k + 1) 0 + r)
    (sound : ∀ b ∈ bank, Valid q b ∧ b.degree ≤ r ∧ NoHost q b.degree)
    (check : CanRaiseX X q r k fs F bank) : Floor q r (k + 2) (F + 1) := by
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
    have exact' : ∀ i < (ws ++ [(layer E V (k + 1) u).card]).length,
        (layer E V (i + 1) u).card = (ws ++ [(layer E V (k + 1) u).card]).getD i 0 := by
      intro i hi
      rw [List.length_append, len, List.length_singleton] at hi
      rcases Nat.lt_or_ge i k with h | h
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact exact i (by omega)
      · obtain rfl : i = k := by omega
        rw [List.getD_append_right _ _ _ _ (by omega), len, Nat.sub_self]
        rfl
    have next : (layer E V ((ws ++ [(layer E V (k + 1) u).card]).length + 1) u).card ≤
        F - (ball E V u (k + 1)).card := by
      rw [List.length_append, len, List.length_singleton]
      show (layer E V (k + 2) u).card ≤ _
      omega
    have d := List.all_eq_true.mp dead ws mem
    rw [ok, Bool.not_true, Bool.false_or] at d
    rcases Bool.or_eq_true_iff.mp d with dx | d3
    · exact sx E V u _ _ freeE degE hu root exact' next dx
    · refine dead3_false freeE degE hu root (degrees := bank.map Comparison.degree) ?_ floors
        exact' next d3
      intro t ht
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
      exact (sound b hb).2.2

def climbX (X : List ℕ → ℕ → Bool) (q r k : ℕ) (fs : List ℕ) (bank : List Comparison)
    (value fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => value
  | fuel + 1 =>
    if CanRaiseX X q r k fs value bank then climbX X q r k fs bank (value + 1) fuel else value

theorem climbX_sound {X q r k fs bank} (sx : SoundX q r X)
    (floors : ∀ i, Floor q r i (fs.getD i 0))
    (time : k + 2 ≤ q) (sound : ∀ b ∈ bank, Valid q b ∧ b.degree ≤ r ∧ NoHost q b.degree)
    (fuel value : ℕ) (start : Floor q r (k + 2) value)
    (budget : value + fuel ≤ fs.getD (k + 1) 0 + r) :
    Floor q r (k + 2) (climbX X q r k fs bank value fuel) := by
  induction fuel generalizing value with
  | zero => exact start
  | succ n ih =>
    simp only [climbX]
    split
    next check => exact ih _ (advanceX sx floors time (by omega) sound check) (by omega)
    next => exact start

/-- The seeded climb with the extra pattern: floors at radii `0 … k + 1`. -/
def layersX (X : List ℕ → ℕ → Bool) (q r : ℕ) (bank : List Comparison) (seed : List ℕ) :
    ℕ → List ℕ
  | 0 => [1, r + 1]
  | k + 1 =>
    let fs := layersX X q r bank seed k
    let start := max (fs.getD (k + 1) 0) (seed.getD (k + 2) 0)
    fs ++ [climbX X q r k fs bank start (fs.getD (k + 1) 0 + r - start)]

theorem layersX_sound {X q r bank seed} (sx : SoundX q r X) (hq : 1 ≤ q)
    (sound : ∀ b ∈ bank, Valid q b ∧ b.degree ≤ r ∧ NoHost q b.degree)
    (seeds : ∀ i, Floor q r i (seed.getD i 0)) (k : ℕ) (time : k + 1 ≤ q) :
    (layersX X q r bank seed k).length = k + 2 ∧
      ∀ i, Floor q r i ((layersX X q r bank seed k).getD i 0) := by
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
    | i + 2 => simpa [layersX] using (floor_zero : Floor q r (i + 2) 0)
  | succ k ih =>
    obtain ⟨len, floors⟩ := ih (by omega)
    have start : Floor q r (k + 2)
        (max ((layersX X q r bank seed k).getD (k + 1) 0) (seed.getD (k + 2) 0)) :=
      ShapeClimbMono.floor_max
        (fun D V free deg u hu => (floors (k + 1) D V free deg u hu).trans
          (card_le_card (ball_mono_radius (Nat.le_succ (k + 1)))))
        (seeds (k + 2))
    have top : Floor q r (k + 2)
        (climbX X q r k (layersX X q r bank seed k) bank
          (max ((layersX X q r bank seed k).getD (k + 1) 0) (seed.getD (k + 2) 0))
          ((layersX X q r bank seed k).getD (k + 1) 0 + r -
            max ((layersX X q r bank seed k).getD (k + 1) 0) (seed.getD (k + 2) 0))) := by
      by_cases fit : max ((layersX X q r bank seed k).getD (k + 1) 0) (seed.getD (k + 2) 0) ≤
          (layersX X q r bank seed k).getD (k + 1) 0 + r
      · exact climbX_sound (bank := bank) sx floors time sound _ _ start (by omega)
      · rw [show (layersX X q r bank seed k).getD (k + 1) 0 + r -
            max ((layersX X q r bank seed k).getD (k + 1) 0) (seed.getD (k + 2) 0) = 0 by omega]
        exact start
    refine ⟨by simp [layersX, len], fun i => ?_⟩
    simp only [layersX]
    rcases Nat.lt_or_ge i (k + 2) with h | h
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact floors i
    · rcases Nat.eq_or_lt_of_le h with rfl | h
      · rw [List.getD_append_right _ _ _ _ (by omega), len, Nat.sub_self]
        exact top
      · rw [List.getD_eq_default _ _ (by simp [len]; omega)]
        exact floor_zero

/-! ### The same list over the pruned search -/

open ShapeClimbFast

def deadAllXF (T : Tbl) (X : List ℕ → ℕ → Bool) (q r : ℕ) (degrees fs : List ℕ)
    (k x c F : ℕ) : Bool :=
  deadAllF r fs (fun ws => X (ws ++ [c]) (F - x) || Dead3F T q r degrees fs (ws ++ [c]) (F - x))
    (fun _ => false) (peelCap q r degrees) k (x - 1 - c)

theorem deadAllXF_eq (X : List ℕ → ℕ → Bool) (q r : ℕ) (degrees fs : List ℕ)
    (RB EB k x c F : ℕ) :
    deadAllXF (mkT q r degrees fs RB EB) X q r degrees fs k x c F =
      deadAllX X q r degrees fs k x c F := by
  rw [deadAllXF, deadAllF_eq _ _ _ _ _
    (fun _ _ h => by simp at h)
    (fun pre a rest h => by
      rw [dead3_of_cap _ q r degrees fs c (F - x) pre a rest h, Bool.or_true])]
  unfold deadAllX
  refine all_congr' (fun ws _ => ?_)
  rw [dead3F_eq]

def CanRaiseXF (T : Tbl) (X : List ℕ → ℕ → Bool) (q r k : ℕ) (fs : List ℕ) (F : ℕ)
    (bank : List Comparison) : Prop :=
  ∀ x ∈ Icc (fs.getD (k + 1) 0) F, ∀ c ∈ range (x - fs.getD k 0 + 1),
    (bank.any (fun b => decide (Pass x c F r b.degree (q * b.degree + 1) (b.left + b.right))) ||
      deadAllXF T X q r (bank.map Comparison.degree) fs k x c F) = true

instance {T X q r k fs F bank} : Decidable (CanRaiseXF T X q r k fs F bank) := by
  unfold CanRaiseXF; infer_instance

theorem canRaiseXF_iff (X : List ℕ → ℕ → Bool) (q r k : ℕ) (fs : List ℕ) (F : ℕ)
    (bank : List Comparison) (RB EB : ℕ) :
    CanRaiseXF (mkT q r (bank.map Comparison.degree) fs RB EB) X q r k fs F bank ↔
      CanRaiseX X q r k fs F bank := by
  simp only [CanRaiseXF, CanRaiseX, deadAllXF_eq]

def climbXF (T : Tbl) (X : List ℕ → ℕ → Bool) (q r k : ℕ) (fs : List ℕ)
    (bank : List Comparison) (value fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => value
  | fuel + 1 =>
    if CanRaiseXF T X q r k fs value bank then climbXF T X q r k fs bank (value + 1) fuel
    else value

theorem climbXF_eq (X : List ℕ → ℕ → Bool) (q r k : ℕ) (fs : List ℕ) (bank : List Comparison)
    (RB EB : ℕ) :
    ∀ fuel value, climbXF (mkT q r (bank.map Comparison.degree) fs RB EB) X q r k fs bank value
      fuel = climbX X q r k fs bank value fuel := by
  intro fuel
  induction fuel with
  | zero => intro value; rfl
  | succ n ih =>
    intro value
    simp only [climbXF, climbX]
    by_cases h : CanRaiseX X q r k fs value bank
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ((canRaiseXF_iff ..).mpr h)),
        ite_eq_left_of_eq_true _ _ (eq_true h), ih]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h' => h ((canRaiseXF_iff ..).mp h'))),
        ite_eq_right_of_eq_false _ _ (eq_false h)]

def layersXF (X : List ℕ → ℕ → Bool) (q r : ℕ) (bank : List Comparison) (seed : List ℕ) :
    ℕ → List ℕ
  | 0 => [1, r + 1]
  | k + 1 =>
    let fs := layersXF X q r bank seed k
    let start := max (fs.getD (k + 1) 0) (seed.getD (k + 2) 0)
    fs ++ [climbXF (tableAt q r bank fs k) X q r k fs bank start (fs.getD (k + 1) 0 + r - start)]

theorem layersXF_eq (X : List ℕ → ℕ → Bool) (q r : ℕ) (bank : List Comparison)
    (seed : List ℕ) : ∀ k, layersXF X q r bank seed k = layersX X q r bank seed k
  | 0 => rfl
  | k + 1 => by
    simp only [layersXF, layersX, tableAt, layersXF_eq X q r bank seed k, climbXF_eq]

/-! ### The collar dip -/

/-- **The third layer after a collar.** A root with exactly `q + 1` heads, each row of
out-degree at least `r ≤ q + 1`, and at most `r - 1` labels in the second layer: the third
layer has at least `r` labels. -/
theorem collar_third {D : CH.Digraph} {V : Finset ℕ} {q r u : ℕ} (free : QFree D V q)
    (hq : 3 ≤ q) (hr : 2 ≤ r) (rq : r ≤ q + 1) (hu : u ∈ V)
    (heads : (outN D V u).card = q + 1) (deg : ∀ v ∈ V, r ≤ (outN D V v).card)
    (thin : (layer D V 2 u).card + 1 ≤ r) : r ≤ (layer D V 3 u).card := by
  classical
  obtain ⟨-, width, all⟩ := LoopCollar.collar free (by omega) hu heads
    (fun x hx => deg x (outN_subset hx)) thin
  have ysub : layer D V 2 u ⊆ V := fun w hw => ball_subset (mem_layer.mp hw).1
  have yne : (layer D V 2 u).Nonempty := card_pos.mp (by omega)
  obtain ⟨t, tY, sink⟩ := exists_sink (free.mono_set ysub) yne (by omega)
  have tV := ysub tY
  obtain ⟨x0, hx0⟩ : (outN D V u).Nonempty := card_pos.mp (by omega)
  have x0V := (mem_outN.mp hx0).1
  have ux0 := (mem_outN.mp hx0).2
  have x0t := (mem_outN.mp ((all x0 hx0).2 tY)).2
  have tb : t ∈ ball D V u 2 := (mem_layer.mp tY).1
  have into : outN D V t ⊆ layer D V 3 u := by
    intro w hw
    obtain ⟨wV, tw⟩ := mem_outN.mp hw
    refine mem_layer.mpr ⟨ball_step tb wV tw, ?_⟩
    show w ∉ ball D V u 2
    intro near
    by_cases one : w ∈ ball D V u 1
    · rcases (mem_ball_one hu).mp one with rfl | wX
      · exact free w 3 (by omega) hq (.step x0V ux0 (.step tV x0t (.step hu tw (.refl w))))
      · exact digonfree free (by omega) tV wV tw (mem_outN.mp ((all w wX).2 tY)).2
    · exact sink w (mem_layer.mpr ⟨near, one⟩) tw
  exact (deg t tV).trans (card_le_card into)

/-- The collar dip: `r = q + 1`, a second layer of at most `r - 1` labels and a third layer of
at most `r - 1` labels. -/
def collarDip (q r : ℕ) (ws : List ℕ) (last : ℕ) : Bool :=
  decide (q + 1 = r ∧ 3 ≤ q ∧ 2 ≤ ws.length ∧ ws.getD 1 0 + 1 ≤ r ∧
    (if 3 ≤ ws.length then ws.getD 2 0 else last) + 1 ≤ r)

theorem collarDip_sound (q r : ℕ) : SoundX q r (collarDip q r) := by
  intro D V u ws last free deg hu root exact bound h
  obtain ⟨qr, hq, len, w2, w3⟩ := of_decide_eq_true h
  have l2 : (layer D V 2 u).card = ws.getD 1 0 := exact 1 (by omega)
  have third := collar_third free hq (by omega) (by omega) hu (by omega) deg (by omega)
  by_cases long : 3 ≤ ws.length
  · have l3 : (layer D V 3 u).card = ws.getD 2 0 := exact 2 (by omega)
    simp only [long, ↓reduceIte] at w3
    omega
  · simp only [long, ↓reduceIte] at w3
    have e : ws.length + 1 = 3 := by omega
    rw [e] at bound
    omega

#print axioms advanceX
#print axioms layersX_sound
#print axioms layersXF_eq
#print axioms collar_third
#print axioms collarDip_sound
end LeanCH.BR.ShapeClimbX
