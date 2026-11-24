import checkpoints.shen_extension.ShapeClimbRoot
import checkpoints.shen_extension.TightLayerShapes
import checkpoints.shen_extension.TightWideCases
import checkpoints.shen_extension.Wide2Acyclic
import checkpoints.shen_extension.LayerExcess
import checkpoints.shen_extension.EqualLayerTransit
import checkpoints.shen_extension.TightPeel

/-!
# A decidable checker for dead layer profiles

`Dead q r degrees ws last` reads the widths `ws = [|L 1|, …, |L m|]` of the layers of a
ball around a root of out-degree exactly `r`, followed by an upper bound `last` for
`|L (m + 1)|`. Slot `i` is the exact width `ws[i]` for `i < m` and the bound `last` at
`i = m`. The checker is true when a prefix of the slots matches one of the compiled
layer-shape exclusions, the equal-layer capacity law, an inner peel by a lower degree
without hosts, an empty layer before a nonempty one, or a wrong first width.
`dead_false` is its soundness. All thresholds are free in `q` and `r`.
-/

namespace LeanCH.BR.ShapeClimbDead
open Finset BRq2 BRq3 BypassRepair ShapeClimbRoot
open DotTwoPassShellTransport (layer shell layer_subset)

/-- Slot `i`: the exact width for `i < |ws|`, the bound `last` from `i = |ws|` on. -/
def slot (ws : List ℕ) (last i : ℕ) : ℕ := ws.getD i last

/-- Widths `r`, `r + 1`, `≤ r - 1` (`wide_layer_false`). -/
def Wide (q r : ℕ) (ws : List ℕ) (last : ℕ) : Prop :=
  2 ≤ ws.length ∧ slot ws last 0 = r ∧ slot ws last 1 = r + 1 ∧ slot ws last 2 + 1 ≤ r ∧
    3 ≤ r ∧ r + 1 ≤ q

/-- Widths `r`, `r`, `r + 1`, `≤ r - 1` (`full_front_tight_false`). -/
def FrontTight (q r : ℕ) (ws : List ℕ) (last : ℕ) : Prop :=
  3 ≤ ws.length ∧ slot ws last 0 = r ∧ slot ws last 1 = r ∧ slot ws last 2 = r + 1 ∧
    slot ws last 3 + 1 ≤ r ∧ 3 ≤ r ∧ r + 1 ≤ q

/-- Widths `r`, `r`, `r`, `r + 1`, `≤ r - 3` (`full_front3_false`). -/
def Front3 (q r : ℕ) (ws : List ℕ) (last : ℕ) : Prop :=
  4 ≤ ws.length ∧ slot ws last 0 = r ∧ slot ws last 1 = r ∧ slot ws last 2 = r ∧
    slot ws last 3 = r + 1 ∧ slot ws last 4 + 3 ≤ r ∧ 3 ≤ r ∧ r + 1 ≤ q ∧ 5 ≤ q

/-- Widths `r`, `r + 1`, `r`, `≤ r - 1` at `q = r + 1` (`tight_wide_layers_false`). -/
def TightWide (q r : ℕ) (ws : List ℕ) (last : ℕ) : Prop :=
  3 ≤ ws.length ∧ slot ws last 0 = r ∧ slot ws last 1 = r + 1 ∧ slot ws last 2 = r ∧
    slot ws last 3 + 1 ≤ r ∧ 5 ≤ r ∧ q = r + 1

/-- Widths `r`, `r + 2`, `r - 1`, `≤ r - 1` at `q = r + 1` (`wide2_layers_false`). -/
def Wide2 (q r : ℕ) (ws : List ℕ) (last : ℕ) : Prop :=
  3 ≤ ws.length ∧ slot ws last 0 = r ∧ slot ws last 1 = r + 2 ∧ slot ws last 2 + 1 = r ∧
    slot ws last 3 + 1 ≤ r ∧ 7 ≤ r ∧ q = r + 1

/-- `h ≥ 1` layers of width `r`, then a narrower slot (`end_capacity`). -/
def Equal (q r : ℕ) (ws : List ℕ) (last : ℕ) : Prop :=
  ∃ h ∈ range (ws.length + 1), 0 < h ∧ (∀ i ∈ range h, slot ws last i = r) ∧
    slot ws last h < r ∧ 0 < r ∧ r < q ∧ r / 2 + h ≤ q ∧ h + 1 ≤ q

/-- The punctured `(j + 1)`-ball keeps `t` heads per row and is too small for degree `t`
(`punctured_peel`). -/
def Peel (q r : ℕ) (degrees ws : List ℕ) (last : ℕ) : Prop :=
  ∃ j ∈ range ws.length, ∃ t ∈ degrees, 1 ≤ t ∧ t + slot ws last (j + 1) ≤ r ∧
    0 < (ws.take (j + 1)).sum ∧ (ws.take (j + 1)).sum ≤ q * t ∧ j + 2 ≤ q

/-- An empty layer followed by a nonempty one. -/
def Gap (ws : List ℕ) : Prop :=
  ∃ i ∈ range ws.length, i + 1 < ws.length ∧ ws.getD i 0 = 0 ∧ 0 < ws.getD (i + 1) 0

/-- The first layer is the out-neighbourhood of the root, of width exactly `r`. -/
def First (q r : ℕ) (ws : List ℕ) (last : ℕ) : Prop :=
  1 ≤ q ∧ (slot ws last 0 < r ∨ (0 < ws.length ∧ slot ws last 0 ≠ r))

/-- Widths `r`, `r + a`, then a slot `z` with `t = r - z`, where layers one and two hold exactly
`q · t + 1` labels and degree `t` has no host (`TightPeel.parent_cover`,
`TightPeel.cover_sink_false`). -/
def TightPeelP (q r : ℕ) (degrees ws : List ℕ) (last : ℕ) : Prop :=
  2 ≤ ws.length ∧ slot ws last 0 = r ∧ r ≤ slot ws last 1 ∧
    r - slot ws last 2 ∈ degrees ∧ 1 ≤ r - slot ws last 2 ∧ r - slot ws last 2 + 1 ≤ r ∧
    2 * r + (slot ws last 1 - r) = q * (r - slot ws last 2) + 1 ∧
    slot ws last 1 - r + 2 ≤ q ∧ 3 ≤ q ∧ r ≤ q

def DeadP (q r : ℕ) (degrees ws : List ℕ) (last : ℕ) : Prop :=
  Wide q r ws last ∨ FrontTight q r ws last ∨ Front3 q r ws last ∨ TightWide q r ws last ∨
    Wide2 q r ws last ∨ Equal q r ws last ∨ Peel q r degrees ws last ∨ Gap ws ∨
    First q r ws last ∨ TightPeelP q r degrees ws last

section
variable (q r : ℕ) (degrees ws : List ℕ) (last : ℕ)
instance : Decidable (Wide q r ws last) := by unfold Wide; infer_instance
instance : Decidable (FrontTight q r ws last) := by unfold FrontTight; infer_instance
instance : Decidable (Front3 q r ws last) := by unfold Front3; infer_instance
instance : Decidable (TightWide q r ws last) := by unfold TightWide; infer_instance
instance : Decidable (Wide2 q r ws last) := by unfold Wide2; infer_instance
instance : Decidable (Equal q r ws last) := by unfold Equal; infer_instance
instance : Decidable (Peel q r degrees ws last) := by unfold Peel; infer_instance
instance : Decidable (Gap ws) := by unfold Gap; infer_instance
instance : Decidable (First q r ws last) := by unfold First; infer_instance
instance : Decidable (TightPeelP q r degrees ws last) := by unfold TightPeelP; infer_instance
instance : Decidable (DeadP q r degrees ws last) := by unfold DeadP; infer_instance
end

def Dead (q r : ℕ) (degrees ws : List ℕ) (last : ℕ) : Bool := decide (DeadP q r degrees ws last)

/-! ### Slots and sums -/

theorem take_sum_getD (ws : List ℕ) (n : ℕ) :
    (ws.take n).sum = ∑ i ∈ range n, ws.getD i 0 := by
  induction ws generalizing n with
  | nil => simp
  | cons a t ih =>
    cases n with
    | zero => simp
    | succ m =>
      rw [List.take_succ_cons, List.sum_cons, ih, sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      omega

section sound
variable {D : CH.Digraph} {V : Finset ℕ} {q r u : ℕ} {ws : List ℕ} {last : ℕ}

theorem slot_eq (exact : ∀ i < ws.length, (layer D V (i + 1) u).card = ws.getD i 0)
    {i : ℕ} (h : i < ws.length) : (layer D V (i + 1) u).card = slot ws last i := by
  rw [exact i h, slot, List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ h]

theorem slot_le (exact : ∀ i < ws.length, (layer D V (i + 1) u).card = ws.getD i 0)
    (bound : (layer D V (ws.length + 1) u).card ≤ last)
    {i : ℕ} (h : i ≤ ws.length) : (layer D V (i + 1) u).card ≤ slot ws last i := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact (slot_eq exact h).le
  · rw [slot, List.getD_eq_default _ _ le_rfl]; exact bound

set_option hygiene false in
/-- Close a heads-containment goal `outN D V x ⊆ L 1 ∪ … ∪ L (i + 1)`. -/
local macro "heads_tac" : tactic => `(tactic| (
  intro x hx y hy
  obtain ⟨j, h1, h2, hj⟩ := head_mem free hu (by omega) (by omega) hx hy
  interval_cases j <;> simp only [mem_union, hj, true_or, or_true]))

theorem wide_dead (free : QFree D V q) (deg : ∀ v ∈ V, r ≤ (outN D V v).card) (hu : u ∈ V)
    (exact : ∀ i < ws.length, (layer D V (i + 1) u).card = ws.getD i 0)
    (bound : (layer D V (ws.length + 1) u).card ≤ last) (p : Wide q r ws last) : False := by
  obtain ⟨len, s0, s1, s2, three, time⟩ := p
  have c0 : (layer D V 1 u).card = slot ws last 0 :=
    slot_eq exact (by omega)
  have c1 : (layer D V 2 u).card = slot ws last 1 :=
    slot_eq exact (by omega)
  have c2 : (layer D V 3 u).card ≤ slot ws last 2 :=
    slot_le exact bound (by omega)
  exact WideLayerReturn.wide_layer_false (X := layer D V 1 u) (Y := layer D V 2 u)
    (Z := layer D V 3 u) free layer_subset layer_subset
    (by omega) (by omega) (by omega) three time
    (fun x hx => deg x (layer_subset hx)) (fun x hx => deg x (layer_subset hx))
    (by heads_tac) (by heads_tac)

theorem front_tight_dead (free : QFree D V q) (deg : ∀ v ∈ V, r ≤ (outN D V v).card)
    (hu : u ∈ V) (exact : ∀ i < ws.length, (layer D V (i + 1) u).card = ws.getD i 0)
    (bound : (layer D V (ws.length + 1) u).card ≤ last) (p : FrontTight q r ws last) : False := by
  obtain ⟨len, s0, s1, s2, s3, three, time⟩ := p
  have c0 : (layer D V 1 u).card = slot ws last 0 :=
    slot_eq exact (by omega)
  have c1 : (layer D V 2 u).card = slot ws last 1 :=
    slot_eq exact (by omega)
  have c2 : (layer D V 3 u).card = slot ws last 2 :=
    slot_eq exact (by omega)
  have c3 : (layer D V 4 u).card ≤ slot ws last 3 :=
    slot_le exact bound (by omega)
  exact WideLayerReturn.full_front_tight_false (W := layer D V 1 u) (X := layer D V 2 u)
    (Y := layer D V 3 u) (Z := layer D V 4 u) free layer_subset
    layer_subset layer_subset (by omega) (by omega) (by omega) (by omega) three time
    (fun x hx => deg x (layer_subset hx)) (fun x hx => deg x (layer_subset hx))
    (fun x hx => deg x (layer_subset hx))
    (by heads_tac) (by heads_tac) (by heads_tac)
    (fun y hy => parent_mem hu (i := 2) (by omega) hy)

theorem front3_dead (free : QFree D V q) (deg : ∀ v ∈ V, r ≤ (outN D V v).card)
    (hu : u ∈ V) (exact : ∀ i < ws.length, (layer D V (i + 1) u).card = ws.getD i 0)
    (bound : (layer D V (ws.length + 1) u).card ≤ last) (p : Front3 q r ws last) : False := by
  obtain ⟨len, s0, s1, s2, s3, s4, three, time, five⟩ := p
  have c0 : (layer D V 1 u).card = slot ws last 0 :=
    slot_eq exact (by omega)
  have c1 : (layer D V 2 u).card = slot ws last 1 :=
    slot_eq exact (by omega)
  have c2 : (layer D V 3 u).card = slot ws last 2 :=
    slot_eq exact (by omega)
  have c3 : (layer D V 4 u).card = slot ws last 3 :=
    slot_eq exact (by omega)
  have c4 : (layer D V 5 u).card ≤ slot ws last 4 :=
    slot_le exact bound (by omega)
  exact TightLayerShapes.full_front3_false (U := layer D V 1 u) (W := layer D V 2 u)
    (X := layer D V 3 u) (Y := layer D V 4 u) (Z := layer D V 5 u) free layer_subset
    layer_subset layer_subset layer_subset (by omega) (by omega) (by omega) (by omega)
    (by omega) three time
    (fun x hx => deg x (layer_subset hx)) (fun x hx => deg x (layer_subset hx))
    (fun x hx => deg x (layer_subset hx)) (fun x hx => deg x (layer_subset hx))
    (by heads_tac) (by heads_tac) (by heads_tac) (by heads_tac)
    (fun y hy => parent_mem hu (i := 2) (by omega) hy)
    (fun y hy => parent_mem hu (i := 3) (by omega) hy)

theorem tight_wide_dead (free : QFree D V q) (deg : ∀ v ∈ V, r ≤ (outN D V v).card)
    (hu : u ∈ V) (exact : ∀ i < ws.length, (layer D V (i + 1) u).card = ws.getD i 0)
    (bound : (layer D V (ws.length + 1) u).card ≤ last) (p : TightWide q r ws last) : False := by
  obtain ⟨len, s0, s1, s2, s3, five, hq⟩ := p
  have c0 : (layer D V 1 u).card = slot ws last 0 :=
    slot_eq exact (by omega)
  have c1 : (layer D V 2 u).card = slot ws last 1 :=
    slot_eq exact (by omega)
  have c2 : (layer D V 3 u).card = slot ws last 2 :=
    slot_eq exact (by omega)
  have c3 : (layer D V 4 u).card ≤ slot ws last 3 :=
    slot_le exact bound (by omega)
  exact TightWideCases.tight_wide_layers_false (X := layer D V 1 u) (Y := layer D V 2 u)
    (Z := layer D V 3 u) (W := layer D V 4 u) free layer_subset
    layer_subset layer_subset (by omega) (by omega) (by omega) (by omega) five hq
    (fun x hx => deg x (layer_subset hx)) (fun x hx => deg x (layer_subset hx))
    (fun x hx => deg x (layer_subset hx))
    (by heads_tac) (by heads_tac) (by heads_tac)

theorem wide2_dead (free : QFree D V q) (deg : ∀ v ∈ V, r ≤ (outN D V v).card)
    (hu : u ∈ V) (exact : ∀ i < ws.length, (layer D V (i + 1) u).card = ws.getD i 0)
    (bound : (layer D V (ws.length + 1) u).card ≤ last) (p : Wide2 q r ws last) : False := by
  obtain ⟨len, s0, s1, s2, s3, seven, hq⟩ := p
  have c0 : (layer D V 1 u).card = slot ws last 0 :=
    slot_eq exact (by omega)
  have c1 : (layer D V 2 u).card = slot ws last 1 :=
    slot_eq exact (by omega)
  have c2 : (layer D V 3 u).card = slot ws last 2 :=
    slot_eq exact (by omega)
  have c3 : (layer D V 4 u).card ≤ slot ws last 3 :=
    slot_le exact bound (by omega)
  exact Wide2Acyclic.wide2_layers_false (X := layer D V 1 u) (Y := layer D V 2 u)
    (Z := layer D V 3 u) (W := layer D V 4 u) free layer_subset
    layer_subset layer_subset (by omega) (by omega) (by omega) (by omega) seven hq
    (fun x hx => deg x (layer_subset hx)) (fun x hx => deg x (layer_subset hx))
    (fun x hx => deg x (layer_subset hx))
    (by heads_tac) (by heads_tac) (by heads_tac)

theorem equal_dead (free : QFree D V q) (deg : ∀ v ∈ V, r ≤ (outN D V v).card)
    (hu : u ∈ V) (exact : ∀ i < ws.length, (layer D V (i + 1) u).card = ws.getD i 0)
    (bound : (layer D V (ws.length + 1) u).card ≤ last) (p : Equal q r ws last) : False := by
  obtain ⟨h, hh, pos, run, shortH, hr, hq, height, time⟩ := p
  rw [mem_range] at hh
  have cap := EqualLayerTransit.end_capacity (fun i => layer D V (i + 1) u) free hr hq height pos
    (fun _ => layer_subset)
    (fun i hi => by rw [slot_eq (last := last) exact (by omega)]; exact run i (mem_range.mpr hi))
    (fun i _ => layer_disjoint (by omega))
    (fun i _ v hv => deg v (layer_subset hv))
    (fun i hi v hv x hx => by
      obtain ⟨j, h1, h2, hj⟩ := head_mem free hu (i := i + 1) (by omega) (by omega) hv hx
      exact ⟨j - 1, by omega, by rwa [Nat.sub_add_cancel h1]⟩)
  have := slot_le exact bound (i := h) (by omega)
  omega

theorem ball_card_take (hu : u ∈ V)
    (exact : ∀ i < ws.length, (layer D V (i + 1) u).card = ws.getD i 0)
    {n : ℕ} (hn : n ≤ ws.length) : (ball D V u n).card = 1 + (ws.take n).sum := by
  rw [card_ball_sum hu, take_sum_getD]
  congr 1
  exact sum_congr rfl (fun i hi => exact i (by rw [mem_range] at hi; omega))

theorem peel_dead (free : QFree D V q) (deg : ∀ v ∈ V, r ≤ (outN D V v).card)
    (hu : u ∈ V) {degrees : List ℕ} (lower : ∀ t ∈ degrees, NoHost q t)
    (exact : ∀ i < ws.length, (layer D V (i + 1) u).card = ws.getD i 0)
    (bound : (layer D V (ws.length + 1) u).card ≤ last) (p : Peel q r degrees ws last) :
    False := by
  obtain ⟨j, hj, t, ht, one, loss, live, small, time⟩ := p
  rw [mem_range] at hj
  have size := ball_card_take hu exact (n := j + 1) (by omega)
  have er := card_erase_add_one (self_mem_ball (D := D) (k := j + 1) hu)
  have next := slot_le exact bound (i := j + 1) (by omega)
  have big := LayerExcess.punctured_peel (k := j + 1) free hu (by omega) deg (lower t ht)
    (by
      have e : ball D V u (j + 1 + 1) \ ball D V u (j + 1) = layer D V (j + 1 + 1) u := by
        simp only [layer, Nat.add_sub_cancel]
      rw [e]; omega)
    (card_pos.mp (by omega))
  omega

theorem gap_dead (hu : u ∈ V)
    (exact : ∀ i < ws.length, (layer D V (i + 1) u).card = ws.getD i 0) (p : Gap ws) : False := by
  obtain ⟨i, -, hi, zero, pos⟩ := p
  have e0 := exact i (by omega)
  have e1 := exact (i + 1) (by omega)
  rw [zero, card_eq_zero] at e0
  rw [layer_empty_next hu e0, card_empty] at e1
  omega

theorem first_dead (free : QFree D V q) (hu : u ∈ V) (root : (outN D V u).card = r)
    (exact : ∀ i < ws.length, (layer D V (i + 1) u).card = ws.getD i 0)
    (bound : (layer D V (ws.length + 1) u).card ≤ last) (p : First q r ws last) : False := by
  obtain ⟨hq, lt | ⟨len, ne⟩⟩ := p
  · have := slot_le exact bound (i := 0) (by omega)
    rw [layer_one_card free hq hu root] at this
    omega
  · have := slot_eq (last := last) exact (i := 0) len
    rw [layer_one_card free hq hu root] at this
    omega

theorem tight_peel_dead (free : QFree D V q) (deg : ∀ v ∈ V, r ≤ (outN D V v).card)
    (hu : u ∈ V) {degrees : List ℕ} (lower : ∀ t ∈ degrees, NoHost q t)
    (exact : ∀ i < ws.length, (layer D V (i + 1) u).card = ws.getD i 0)
    (bound : (layer D V (ws.length + 1) u).card ≤ last) (p : TightPeelP q r degrees ws last) :
    False := by
  obtain ⟨len, s0, s1, tdeg, t1, t2, sz, time, q3, rq⟩ := p
  have c0 : (layer D V 1 u).card = slot ws last 0 := slot_eq exact (by omega)
  have c1 : (layer D V 2 u).card = slot ws last 1 := slot_eq exact (by omega)
  have c2 : (layer D V 3 u).card ≤ slot ws last 2 := slot_le exact bound (by omega)
  have cU : (layer D V 1 u ∪ layer D V 2 u).card = slot ws last 0 + slot ws last 1 := by
    rw [card_union_of_disjoint (layer_disjoint (by omega)), c0, c1]
  have headsX : ∀ x ∈ layer D V 1 u, outN D V x ⊆ layer D V 1 u ∪ layer D V 2 u := by
    heads_tac
  have rowsA : ∀ x ∈ layer D V 1 u,
      r - slot ws last 2 + 1 ≤ (outN D (layer D V 1 u ∪ layer D V 2 u) x).card := by
    intro x hx
    have sub : outN D V x ⊆ outN D (layer D V 1 u ∪ layer D V 2 u) x := fun w hw =>
      mem_outN.mpr ⟨headsX x hx hw, (mem_outN.mp hw).2⟩
    have := card_le_card sub
    have := deg x (layer_subset hx)
    omega
  have rowsY : ∀ y ∈ layer D V 2 u,
      r - slot ws last 2 ≤ (outN D (layer D V 1 u ∪ layer D V 2 u) y).card := by
    intro y hy
    have sub : outN D V y ⊆ outN D (layer D V 1 u ∪ layer D V 2 u) y ∪ layer D V 3 u := by
      intro w hw
      obtain ⟨j, h1, h2, hj⟩ := head_mem free hu (i := 2) (by omega) (by omega) hy hw
      interval_cases j
      · exact mem_union_left _ (mem_outN.mpr ⟨mem_union_left _ hj, (mem_outN.mp hw).2⟩)
      · exact mem_union_left _ (mem_outN.mpr ⟨mem_union_right _ hj, (mem_outN.mp hw).2⟩)
      · exact mem_union_right _ hj
    have := (card_le_card sub).trans (card_union_le _ _)
    have := deg y (layer_subset hy)
    omega
  have cover := TightPeel.parent_cover free (union_subset layer_subset layer_subset)
    (lower _ tdeg) t1 (by omega) (by omega) rowsA rowsY
  exact TightPeel.cover_sink_false (a := slot ws last 1 - r) free layer_subset layer_subset
    (card_pos.mp (by omega)) (by omega) (fun x hx => deg x (layer_subset hx)) headsX
    (by omega) time cover

/-- **Soundness of the checker.** At a root of out-degree exactly `r` whose layers have the
widths `ws` and a next layer of at most `last` labels, a dead profile is impossible. -/
theorem dead_false (free : QFree D V q) (deg : ∀ v ∈ V, r ≤ (outN D V v).card) (hu : u ∈ V)
    (root : (outN D V u).card = r) {degrees : List ℕ} (lower : ∀ t ∈ degrees, NoHost q t)
    (exact : ∀ i < ws.length, (layer D V (i + 1) u).card = ws.getD i 0)
    (bound : (layer D V (ws.length + 1) u).card ≤ last)
    (dead : Dead q r degrees ws last = true) : False := by
  rcases of_decide_eq_true dead with p | p | p | p | p | p | p | p | p | p
  · exact wide_dead free deg hu exact bound p
  · exact front_tight_dead free deg hu exact bound p
  · exact front3_dead free deg hu exact bound p
  · exact tight_wide_dead free deg hu exact bound p
  · exact wide2_dead free deg hu exact bound p
  · exact equal_dead free deg hu exact bound p
  · exact peel_dead free deg hu lower exact bound p
  · exact gap_dead hu exact p
  · exact first_dead free hu root exact bound p
  · exact tight_peel_dead free deg hu lower exact bound p

end sound

#print axioms dead_false
end LeanCH.BR.ShapeClimbDead
