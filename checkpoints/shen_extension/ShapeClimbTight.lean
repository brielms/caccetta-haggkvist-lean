import checkpoints.shen_extension.ShapeClimbFast
import checkpoints.shen_extension.TightPair

/-!
# The reach climb with the tight-pair gain

`ShapeClimbAt3.boundAt3 q r c` compares the floors `left`, `right` of the reach climb at the two
middle radii `q/2` and `q - q/2` by the two-ball count: a host has at least `left + right - 1`
labels. For odd `q` the third radius `q - 2 (q/2)` is `1`, where the out-degree gives the floor
`r + 1`. `TightPair.tight_pair_false` then excludes the order `left + right - 1` itself as soon
as `right + 1 ≤ left + r`, that is, as soon as the floor grows by less than `r` across the
middle. `boundAt3T` adds that unit when the existing strict gain is absent.

`boundAt3TF` is the same number over the pruned evaluation of `ShapeClimbFast`.
Everything is generic in `q`, `r` and `c`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.ShapeClimbTight
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion CHRuleCatalog ProjectedQuotaTransfer
open RecursivePrefixBudget ShapeClimbDead3

/-- The floor of the reach climb at radius `q/2`. -/
def leftAt (q r c : ℕ) : ℕ := (ShapeClimbAt3.resultAt3 q r c).left

/-- The floor of the reach climb at radius `q - q/2`. -/
def rightAt (q r c : ℕ) : ℕ := (ShapeClimbAt3.resultAt3 q r c).right

/-- The tight-pair gain: `q` odd and the floor grows by less than `r` across the middle. -/
def Tight (q r c : ℕ) : Prop := q % 2 = 1 ∧ rightAt q r c + 1 ≤ leftAt q r c + r

instance {q r c} : Decidable (Tight q r c) := by unfold Tight; infer_instance

/-- The order bound of the reach climb with the tight-pair gain. -/
def boundAt3T (q r c : ℕ) : ℕ :=
  ShapeClimbAt3.boundAt3 q r c +
    (if ¬ShapeClimbAt3.strictGainAt3 q r c (ShapeClimbAt3.resultAt3 q r c) ∧ Tight q r c ∧
        2 ≤ leftAt q r c + rightAt q r c then 1 else 0)

theorem boundAt3T_sound {q r c} (hq : 2 ≤ q) (hr : 0 < r) (cr : c < r)
    (known : ∀ t, t ≤ c → NoHost q t)
    {D V} (free : QFree D V q) (ne : V.Nonempty) (deg : ∀ v ∈ V, r ≤ (outN D V v).card) :
    boundAt3T q r c < V.card := by
  have base := ShapeClimbAt3.boundAt3_sound hq hr cr known free ne deg
  unfold boundAt3T
  split
  next h =>
    obtain ⟨ns, ⟨odd, gain⟩, two⟩ := h
    obtain ⟨left, right⟩ := ShapeClimbAt3.resultAt3_valid hq cr known
    change Floor q r (q / 2) (leftAt q r c) at left
    change Floor q r (q - q / 2) (rightAt q r c) at right
    have e : ShapeClimbAt3.boundAt3 q r c = leftAt q r c + rightAt q r c - 2 := by
      show (ShapeClimbAt3.resultAt3 q r c).left + (ShapeClimbAt3.resultAt3 q r c).right +
        (if ShapeClimbAt3.strictGainAt3 q r c (ShapeClimbAt3.resultAt3 q r c) then 1 else 0) - 2 = _
      simp only [ns, ↓reduceIte]
      rfl
    rw [e]
    by_contra small
    have small' : V.card + 1 ≤ leftAt q r c + rightAt q r c := by omega
    exact TightPair.tight_pair_false free (by omega : 2*(q/2) ≤ q) ne (left D V free deg)
      (right D V free deg) (c := r + 1)
      (fun v hv => by
        have one : q - 2*(q/2) = 1 := by omega
        rw [one, ReachLedger.ball_one free (by omega) hv]
        have := deg v hv
        omega)
      small' (by omega)
  next => simpa using base

/-! ### The same number over the pruned evaluation -/

/-- `boundAt3T`, with the floors computed once by `ShapeClimbFast.layers3F`. -/
def boundAt3TF (q r c : ℕ) : ℕ :=
  let fs := ShapeClimbFast.layers3F q r (library q c) (q / 2)
  let left := fs.getD (q / 2) 0
  let right := if q - q / 2 = q / 2 then fs.getD (q / 2) 0 else fs.getD (q / 2 + 1) 0
  left + right +
      (if 2 * (q / 2 / 2) = q / 2 ∧ left + 2 ≤ 2 * fs.getD (q / 2 / 2) 0 then 1 else 0) - 2 +
    (if ¬(2 * (q / 2 / 2) = q / 2 ∧ left + 2 ≤ 2 * fs.getD (q / 2 / 2) 0) ∧
        (q % 2 = 1 ∧ right + 1 ≤ left + r) ∧ 2 ≤ left + right then 1 else 0)

theorem boundAt3TF_eq (q r c : ℕ) : boundAt3TF q r c = boundAt3T q r c := by
  simp only [boundAt3TF, boundAt3T, Tight, leftAt, rightAt, ShapeClimbAt3.boundAt3,
    ShapeClimbAt3.resultAt3, ShapeClimbAt3.middle3, ShapeClimbAt3.strictGainAt3,
    ShapeClimbFast.layers3F_eq,
    ShapeClimbFast.layers3_getD_le q r (library q c) (Nat.div_le_self (q / 2) 2)
      (by omega : q / 2 / 2 < q / 2 / 2 + 2)]
  congr

/-! ### Guarded bound and window -/

/-- The tight bound, used only at degrees at most `span` above the closed prefix `limit`. -/
def guardedBoundAt3T (q r limit span : ℕ) : ℕ :=
  if r ≤ limit + span then boundAt3T q r (min (r - 1) (limit - 1)) else 0

def guardedBoundAt3TF (q r limit span : ℕ) : ℕ :=
  if r ≤ limit + span then boundAt3TF q r (min (r - 1) (limit - 1)) else 0

theorem guardedBoundAt3TF_eq (q r limit span : ℕ) :
    guardedBoundAt3TF q r limit span = guardedBoundAt3T q r limit span := by
  simp only [guardedBoundAt3TF, guardedBoundAt3T, boundAt3TF_eq]

theorem excludedGT {p : Input} {limit span} (bad : Bad p)
    (known : ∀ t, t < limit → NoHost (cutoff p) t) :
    ¬ShapeClimbAt3.WindowGWith (guardedBoundAt3T (cutoff p) p.s limit span) p.n p.s (cutoff p)
      limit := by
  rintro ⟨cut, pos, lim, npos, paid⟩
  unfold guardedBoundAt3T at paid
  split at paid
  · have certificate : GuardedFamilyRules.OrderBound (cutoff p) p.s
        (boundAt3T (cutoff p) p.s (min (p.s - 1) (limit - 1))) :=
      ⟨lt_of_lt_of_le bad.order paid, fun _ _ free ne deg => boundAt3T_sound cut pos
        (lt_of_le_of_lt (min_le_left ..) (by omega))
        (fun t ht => known t (by have := ht.trans (min_le_right ..); omega)) free ne deg⟩
    exact GuardedFamilyRules.forbidden bad certificate ⟨le_rfl, le_rfl, by omega⟩
  · omega

theorem at_completedGT {p : Input} (bad : Bad p) (span : ℕ) :
    ¬ShapeClimbAt3.WindowGWith (guardedBoundAt3T (cutoff p) p.s projectionFloor span) p.n p.s
      (cutoff p) projectionFloor :=
  excludedGT bad (available_lower_hosts bad)

#print axioms boundAt3T_sound
#print axioms boundAt3TF_eq
#print axioms guardedBoundAt3TF_eq
#print axioms at_completedGT
end LeanCH.BR.ShapeClimbTight
