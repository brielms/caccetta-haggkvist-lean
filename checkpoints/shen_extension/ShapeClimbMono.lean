import checkpoints.shen_extension.ShapeClimbTight
import checkpoints.shen_extension.BypassDegreeDescent

/-!
# The reach climb seeded from the cutoff one below

A digraph with no closed walk of length at most `q` has none of length at most `q - 1`, so
every ball floor proved at cutoff `q - 1` holds at cutoff `q` (`floor_of_lower`). The reach
climb `ShapeClimbDead3.layers3` does not see this: at some cutoffs its floors are lower than
its own floors one cutoff below. `layersS` is the same climb started, at each radius, from the
larger of the previous floor and a supplied floor `seed`; `floorsM` seeds the climb at cutoff
`q` with the unseeded climb at cutoff `q - 1`.

The closed lower degrees are needed at both cutoffs. `lower_hosts_every` supplies them at
every cutoff: a host of degree below the completed prefix is, after relabelling, a
counterexample to the conjecture at that degree.

`boundM` is the order bound from the seeded floors at the two middle radii, with the strict
gain of `ShapeClimbAt3.boundAt3` and the tight-pair gain of `ShapeClimbTight.boundAt3T`.
`boundMF` is the same number over the pruned evaluation of `ShapeClimbFast`.
Everything is generic in `q`, `r` and `c`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.ShapeClimbMono
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion CHRuleCatalog ProjectedQuotaTransfer
open RecursivePrefixBudget ShapeClimbDead3
open ShapeClimbAt (library_bankAt)

/-! ### Lower degrees at every cutoff -/

theorem arcless_no_cycle (n b : ℕ) : ¬CH.HasDirectedCycleAtMost (fun _ _ => false) n b := by
  rintro ⟨vs, cyc, -⟩
  match vs, cyc with
  | [], h => exact h
  | _ :: [], h => exact h.1 rfl
  | _ :: _ :: _, h => exact Bool.false_ne_true h.2.2.2.1.1

/-- No host of a degree below the completed prefix, at any cutoff. -/
theorem lower_hosts_every (q t : ℕ) (low : t < projectionFloor) : NoHost q t := by
  intro E U live size free deg
  have cardPos := card_pos.mpr live
  rcases Nat.eq_zero_or_pos t with rfl | pos
  · omega
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · omega
  let p : Input := ⟨q, 1, fun _ _ => false⟩
  have cp : cutoff p = q := by simp [cutoff, CH.ceilDiv, p]
  obtain ⟨c, -, child, cs, -⟩ := BypassDegreeDescent.host_child p pos (by omega) live
    (by rw [cp]; exact size) (by rw [cp]; exact free) deg
  have bad : Bad c := ⟨child.order, child.degree_pos, child.loopless, child.degree,
    fun hit => arcless_no_cycle _ _ (child.pullback hit)⟩
  have floor : projectionFloor ≤ c.s := replay_completed_floor bad
  omega

/-! ### Floors pass to larger cutoffs -/

theorem floor_of_lower {q q' r i a : ℕ} (h : q' ≤ q) (fl : Floor q' r i a) : Floor q r i a :=
  fun F U free deg x hx => fl F U (free.mono_bound h) deg x hx

theorem floor_max {q r i a b : ℕ} (fa : Floor q r i a) (fb : Floor q r i b) :
    Floor q r i (max a b) :=
  fun F U free deg x hx => max_le (fa F U free deg x hx) (fb F U free deg x hx)

/-! ### The seeded climb -/

/-- The reach climb started at each radius from the larger of the previous floor and `seed`. -/
def layersS (q r : ℕ) (bank : List Comparison) (seed : List ℕ) : ℕ → List ℕ
  | 0 => [1, r + 1]
  | k + 1 =>
    let fs := layersS q r bank seed k
    let start := max (fs.getD (k + 1) 0) (seed.getD (k + 2) 0)
    fs ++ [climb3 q r k fs bank start (fs.getD (k + 1) 0 + r - start)]

theorem layersS_sound {q r bank seed} (hq : 1 ≤ q)
    (sound : ∀ b ∈ bank, Valid q b ∧ b.degree ≤ r ∧ NoHost q b.degree)
    (seeds : ∀ i, Floor q r i (seed.getD i 0)) (k : ℕ) (time : k + 1 ≤ q) :
    (layersS q r bank seed k).length = k + 2 ∧
      ∀ i, Floor q r i ((layersS q r bank seed k).getD i 0) := by
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
    | i + 2 => simpa [layersS] using (floor_zero : Floor q r (i + 2) 0)
  | succ k ih =>
    obtain ⟨len, floors⟩ := ih (by omega)
    have start : Floor q r (k + 2)
        (max ((layersS q r bank seed k).getD (k + 1) 0) (seed.getD (k + 2) 0)) :=
      floor_max
        (fun D V free deg u hu => (floors (k + 1) D V free deg u hu).trans
          (card_le_card (ball_mono_radius (Nat.le_succ (k + 1)))))
        (seeds (k + 2))
    have top : Floor q r (k + 2)
        (climb3 q r k (layersS q r bank seed k) bank
          (max ((layersS q r bank seed k).getD (k + 1) 0) (seed.getD (k + 2) 0))
          ((layersS q r bank seed k).getD (k + 1) 0 + r -
            max ((layersS q r bank seed k).getD (k + 1) 0) (seed.getD (k + 2) 0))) := by
      by_cases fit : max ((layersS q r bank seed k).getD (k + 1) 0) (seed.getD (k + 2) 0) ≤
          (layersS q r bank seed k).getD (k + 1) 0 + r
      · exact climb3_sound (bank := bank) floors time sound _ _ start (by omega)
      · rw [show (layersS q r bank seed k).getD (k + 1) 0 + r -
            max ((layersS q r bank seed k).getD (k + 1) 0) (seed.getD (k + 2) 0) = 0 by omega]
        exact start
    refine ⟨by simp [layersS, len], fun i => ?_⟩
    simp only [layersS]
    rcases Nat.lt_or_ge i (k + 2) with h | h
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact floors i
    · rcases Nat.eq_or_lt_of_le h with rfl | h
      · rw [List.getD_append_right _ _ _ _ (by omega), len, Nat.sub_self]
        exact top
      · rw [List.getD_eq_default _ _ (by simp [len]; omega)]
        exact floor_zero

/-- The floors of the unseeded climb at cutoff `q - 1`, when its radii `0 … K + 1` are in time. -/
def seedAt (q r c K : ℕ) : List ℕ :=
  if 3 ≤ q ∧ K + 2 ≤ q then layers3 (q - 1) r (library (q - 1) c) K else []

theorem seedAt_sound {q r c K} (cr : c < r) (known : ∀ q' t, t ≤ c → NoHost q' t) :
    ∀ i, Floor q r i ((seedAt q r c K).getD i 0) := by
  intro i
  unfold seedAt
  split
  next h =>
    obtain ⟨-, fl⟩ := layers3_sound (q := q - 1) (by omega)
      (library_bankAt (by omega) cr (known (q - 1))) K (by omega)
    exact floor_of_lower (Nat.sub_le q 1) (fl i)
  next => simpa using (floor_zero : Floor q r i 0)

/-- Floors at radii `0 … q/2 + 1` at cutoff `q`, seeded from cutoff `q - 1`. -/
def floorsM (q r c : ℕ) : List ℕ :=
  layersS q r (library q c) (seedAt q r c (q / 2)) (q / 2)

theorem floorsM_sound {q r c} (hq : 2 ≤ q) (cr : c < r) (known : ∀ q' t, t ≤ c → NoHost q' t) :
    ∀ i, Floor q r i ((floorsM q r c).getD i 0) :=
  (layersS_sound (by omega) (library_bankAt hq cr (known q)) (seedAt_sound cr known) (q / 2)
    (by omega)).2

/-! ### The order bound -/

/-- The order bound from a list of floors indexed by radius: two-ball count at the middle radii,
plus one for the strict gain at the quarter radius, or else for the tight pair at odd `q`. -/
def boundOf (q r : ℕ) (fs : List ℕ) : ℕ :=
  let left := fs.getD (q / 2) 0
  let right := fs.getD (q - q / 2) 0
  left + right +
      (if 2 * (q / 2 / 2) = q / 2 ∧ left + 2 ≤ 2 * fs.getD (q / 2 / 2) 0 then 1 else 0) - 2 +
    (if ¬(2 * (q / 2 / 2) = q / 2 ∧ left + 2 ≤ 2 * fs.getD (q / 2 / 2) 0) ∧
        (q % 2 = 1 ∧ right + 1 ≤ left + r) ∧ 2 ≤ left + right then 1 else 0)

theorem boundOf_sound {q r fs} (hq : 2 ≤ q) (floors : ∀ i, Floor q r i (fs.getD i 0))
    {D V} (free : QFree D V q) (ne : V.Nonempty) (deg : ∀ v ∈ V, r ≤ (outN D V v).card) :
    boundOf q r fs < V.card := by
  have left := floors (q / 2)
  have right := floors (q - q / 2)
  have pos := card_pos.mpr ne
  unfold boundOf
  by_cases strict : 2 * (q / 2 / 2) = q / 2 ∧ fs.getD (q / 2) 0 + 2 ≤ 2 * fs.getD (q / 2 / 2) 0
  · obtain ⟨eq, more⟩ := strict
    have size := SharedBankOrderTransfer.strict_order (k := q / 2 / 2) free ne
      (by omega : 2 * (q / 2 / 2) + (q - q / 2) ≤ q) (floors (q / 2 / 2) D V free deg)
      (eq.symm ▸ left D V free deg) (right D V free deg) more
    simp only [eq, more, and_self, ↓reduceIte, not_true_eq_false, false_and]
    omega
  · have size := order_of_floors (by omega : q / 2 + (q - q / 2) ≤ q) left right D V free deg ne
    simp only [strict, ↓reduceIte, not_false_eq_true, true_and]
    split
    next h =>
      obtain ⟨⟨odd, gain⟩, two⟩ := h
      by_contra small
      exact TightPair.tight_pair_false free (by omega : 2 * (q / 2) ≤ q) ne (left D V free deg)
        (right D V free deg) (c := r + 1)
        (fun v hv => by
          have one : q - 2 * (q / 2) = 1 := by omega
          rw [one, ReachLedger.ball_one free (by omega) hv]
          have := deg v hv
          omega)
        (by omega) (by omega)
    next => omega

/-- The order bound of the seeded climb at degree `r` with the bank of degrees `≤ c`. -/
def boundM (q r c : ℕ) : ℕ := boundOf q r (floorsM q r c)

theorem boundM_sound {q r c} (hq : 2 ≤ q) (cr : c < r) (known : ∀ q' t, t ≤ c → NoHost q' t)
    {D V} (free : QFree D V q) (ne : V.Nonempty) (deg : ∀ v ∈ V, r ≤ (outN D V v).card) :
    boundM q r c < V.card :=
  boundOf_sound hq (floorsM_sound hq cr known) free ne deg

/-! ### The same number over the pruned evaluation -/

open ShapeClimbFast in
def layersSF (q r : ℕ) (bank : List Comparison) (seed : List ℕ) : ℕ → List ℕ
  | 0 => [1, r + 1]
  | k + 1 =>
    let fs := layersSF q r bank seed k
    let start := max (fs.getD (k + 1) 0) (seed.getD (k + 2) 0)
    fs ++ [climb3F (tableAt q r bank fs k) q r k fs bank start (fs.getD (k + 1) 0 + r - start)]

theorem layersSF_eq (q r : ℕ) (bank : List Comparison) (seed : List ℕ) :
    ∀ k, layersSF q r bank seed k = layersS q r bank seed k
  | 0 => rfl
  | k + 1 => by
    simp only [layersSF, layersS, ShapeClimbFast.tableAt, layersSF_eq q r bank seed k,
      ShapeClimbFast.climb3F_eq]

def seedAtF (q r c K : ℕ) : List ℕ :=
  if 3 ≤ q ∧ K + 2 ≤ q then ShapeClimbFast.layers3F (q - 1) r (library (q - 1) c) K else []

def boundMF (q r c : ℕ) : ℕ :=
  boundOf q r (layersSF q r (library q c) (seedAtF q r c (q / 2)) (q / 2))

theorem boundMF_eq (q r c : ℕ) : boundMF q r c = boundM q r c := by
  simp only [boundMF, boundM, floorsM, seedAtF, seedAt, layersSF_eq, ShapeClimbFast.layers3F_eq]

/-! ### Guarded bound and window -/

/-- The seeded bound, used only at degrees at most `span` above the closed prefix `limit`. -/
def guardedBoundM (q r limit span : ℕ) : ℕ :=
  if r ≤ limit + span then boundM q r (min (r - 1) (limit - 1)) else 0

def guardedBoundMF (q r limit span : ℕ) : ℕ :=
  if r ≤ limit + span then boundMF q r (min (r - 1) (limit - 1)) else 0

theorem guardedBoundMF_eq (q r limit span : ℕ) :
    guardedBoundMF q r limit span = guardedBoundM q r limit span := by
  simp only [guardedBoundMF, guardedBoundM, boundMF_eq]

theorem excludedGM {p : Input} {limit span} (bad : Bad p)
    (known : ∀ q' t, t < limit → NoHost q' t) :
    ¬ShapeClimbAt3.WindowGWith (guardedBoundM (cutoff p) p.s limit span) p.n p.s (cutoff p)
      limit := by
  rintro ⟨cut, pos, lim, npos, paid⟩
  unfold guardedBoundM at paid
  split at paid
  · have certificate : GuardedFamilyRules.OrderBound (cutoff p) p.s
        (boundM (cutoff p) p.s (min (p.s - 1) (limit - 1))) :=
      ⟨lt_of_lt_of_le bad.order paid, fun _ _ free ne deg => boundM_sound cut
        (lt_of_le_of_lt (min_le_left ..) (by omega))
        (fun q' t ht => known q' t (by have := ht.trans (min_le_right ..); omega)) free ne deg⟩
    exact GuardedFamilyRules.forbidden bad certificate ⟨le_rfl, le_rfl, by omega⟩
  · omega

theorem at_completedGM {p : Input} (bad : Bad p) (span : ℕ) :
    ¬ShapeClimbAt3.WindowGWith (guardedBoundM (cutoff p) p.s projectionFloor span) p.n p.s
      (cutoff p) projectionFloor :=
  excludedGM bad (fun q' t low => lower_hosts_every q' t low)

#print axioms lower_hosts_every
#print axioms layersS_sound
#print axioms boundM_sound
#print axioms boundMF_eq
#print axioms guardedBoundMF_eq
#print axioms at_completedGM
end LeanCH.BR.ShapeClimbMono
