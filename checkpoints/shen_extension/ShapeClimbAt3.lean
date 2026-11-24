import checkpoints.shen_extension.ShapeClimbAt
import checkpoints.shen_extension.ShapeClimbDead3

/-!
# The reach-capacity climb at the true degree

The same degree-`r` window as `ShapeClimbAt`, over the floors `layers3` of the climb with
the reach-capacity checker, and the bank `library q c` of the closed lower degrees
`t ≤ c < r`. `layers3 q r bank k` lists floors at radii `0 … k + 1`, indexed by radius,
exactly as `layers'`. Everything is generic in `q`, `r` and `c`.
-/

namespace LeanCH.BR.ShapeClimbAt3
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion RecursivePrefixBudget ShapeClimbDead3
open ShapeClimbAt (library_bankAt)

def middle3 (q r : ℕ) (bank : List Comparison) : Comparison :=
  let fs := layers3 q r bank (q / 2)
  ⟨r, fs.getD (q / 2) 0, if q - q / 2 = q / 2 then fs.getD (q / 2) 0 else fs.getD (q / 2 + 1) 0⟩

theorem middle3_valid {q r bank} (hq : 2 ≤ q)
    (sound : ∀ b ∈ bank, Valid q b ∧ b.degree ≤ r ∧ NoHost q b.degree) :
    Valid q (middle3 q r bank) := by
  obtain ⟨-, fl⟩ := layers3_sound (by omega : 1 ≤ q) sound (q / 2) (by omega)
  refine ⟨fl (q / 2), ?_⟩
  change Floor q r (q - q / 2) (if q - q / 2 = q / 2 then _ else _)
  split
  next e => simpa only [e] using fl (q / 2)
  next e => simpa only [show q - q / 2 = q / 2 + 1 by omega] using fl (q / 2 + 1)

/-- The top comparison of the reach-capacity climb at degree `r` over the bank of degrees `≤ c`. -/
def resultAt3 (q r c : ℕ) : Comparison := middle3 q r (library q c)

def strictGainAt3 (q r c : ℕ) (b : Comparison) : Prop :=
  2 * (q / 2 / 2) = q / 2 ∧
    b.left + 2 ≤ 2 * (layers3 q r (library q c) (q / 2 / 2)).getD (q / 2 / 2) 0

instance {q r c b} : Decidable (strictGainAt3 q r c b) := by unfold strictGainAt3; infer_instance

/-- The order bound at degree `r` from the reach-capacity floors and the bank of degrees `≤ c`. -/
def boundAt3 (q r c : ℕ) : ℕ :=
  let b := resultAt3 q r c
  b.left + b.right + (if strictGainAt3 q r c b then 1 else 0) - 2

theorem resultAt3_valid {q r c} (hq : 2 ≤ q) (cr : c < r) (known : ∀ t, t ≤ c → NoHost q t) :
    Valid q (resultAt3 q r c) :=
  middle3_valid hq (library_bankAt hq cr known)

theorem boundAt3_sound {q r c} (hq : 2 ≤ q) (hr : 0 < r) (cr : c < r)
    (known : ∀ t, t ≤ c → NoHost q t)
    {D V} (free : QFree D V q) (ne : V.Nonempty) (deg : ∀ v ∈ V, r ≤ (outN D V v).card) :
    boundAt3 q r c < V.card := by
  have _ := hr
  let b := resultAt3 q r c
  obtain ⟨left, right⟩ := resultAt3_valid hq cr known
  change Floor q r (q / 2) b.left at left
  change Floor q r (q - q / 2) b.right at right
  change b.left + b.right + (if strictGainAt3 q r c b then 1 else 0) - 2 < V.card
  have pos := card_pos.mpr ne
  split
  next gain =>
    obtain ⟨eq, more⟩ := gain
    obtain ⟨-, bank⟩ := layers3_sound (by omega : 1 ≤ q) (library_bankAt hq cr known) (q / 2 / 2)
      (by omega)
    have size := SharedBankOrderTransfer.strict_order (k := q / 2 / 2) free ne
      (by omega : 2 * (q / 2 / 2) + (q - q / 2) ≤ q) (bank (q / 2 / 2) D V free deg)
      (eq.symm ▸ left D V free deg) (right D V free deg) more
    omega
  next =>
    have size := order_of_floors (by omega : q / 2 + (q - q / 2) ≤ q) left right D V free deg ne
    omega

end LeanCH.BR.ShapeClimbAt3

/-! ### The order window at the true degree -/

namespace LeanCH.BR.ShapeClimbAt3
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion CHRuleCatalog ProjectedQuotaTransfer
open RecursivePrefixBudget

/-- The window with the bound supplied, so a caller computes `boundAt3` once per `(q, r)`. -/
@[ch_numeric_guard] def WindowWith3 (b n r q limit : ℕ) : Prop :=
  2 ≤ q ∧ 0 < r ∧ 0 < limit ∧ n ≤ b

instance {b n r q limit} : Decidable (WindowWith3 b n r q limit) := by
  unfold WindowWith3; infer_instance

@[ch_numeric_guard] def Window3 (n r q limit : ℕ) : Prop :=
  2 ≤ q ∧ 0 < r ∧ 0 < limit ∧ n ≤ boundAt3 q r (min (r - 1) (limit - 1))

instance {n r q limit} : Decidable (Window3 n r q limit) := by unfold Window3; infer_instance

theorem window3_iff {n r q limit} :
    Window3 n r q limit ↔ WindowWith3 (boundAt3 q r (min (r - 1) (limit - 1))) n r q limit :=
  Iff.rfl

theorem excluded3 {p : Input} {limit} (bad : Bad p) (known : ∀ t, t < limit → NoHost (cutoff p) t) :
    ¬Window3 p.n p.s (cutoff p) limit := by
  rintro ⟨cut, pos, lim, paid⟩
  have certificate : GuardedFamilyRules.OrderBound (cutoff p) p.s
      (boundAt3 (cutoff p) p.s (min (p.s - 1) (limit - 1))) :=
    ⟨lt_of_lt_of_le bad.order paid, fun _ _ free ne deg => boundAt3_sound cut pos
      (lt_of_le_of_lt (min_le_left ..) (by omega))
      (fun t ht => known t (by have := ht.trans (min_le_right ..); omega)) free ne deg⟩
  exact GuardedFamilyRules.forbidden bad certificate ⟨le_rfl, le_rfl, by omega⟩

theorem at_completed3 {p : Input} (bad : Bad p) :
    ¬Window3 p.n p.s (cutoff p) projectionFloor := excluded3 bad (available_lower_hosts bad)

/-- The bound, used only at degrees at most `span` above the closed prefix `limit`. -/
def guardedBoundAt3 (q r limit span : ℕ) : ℕ :=
  if r ≤ limit + span then boundAt3 q r (min (r - 1) (limit - 1)) else 0

/-- The guarded window with the bound supplied, so a caller computes it once per `(q, r)`. -/
@[ch_numeric_guard] def WindowGWith (b n r q limit : ℕ) : Prop :=
  2 ≤ q ∧ 0 < r ∧ 0 < limit ∧ 0 < n ∧ n ≤ b

instance {b n r q limit} : Decidable (WindowGWith b n r q limit) := by
  unfold WindowGWith; infer_instance

@[ch_numeric_guard] def WindowG3 (n r q limit span : ℕ) : Prop :=
  2 ≤ q ∧ 0 < r ∧ 0 < limit ∧ 0 < n ∧ n ≤ guardedBoundAt3 q r limit span

instance {n r q limit span} : Decidable (WindowG3 n r q limit span) := by
  unfold WindowG3; infer_instance

theorem windowG3_iff {n r q limit span} :
    WindowG3 n r q limit span ↔ WindowGWith (guardedBoundAt3 q r limit span) n r q limit :=
  Iff.rfl

theorem excludedG {p : Input} {limit span} (bad : Bad p)
    (known : ∀ t, t < limit → NoHost (cutoff p) t) :
    ¬WindowG3 p.n p.s (cutoff p) limit span := by
  rintro ⟨cut, pos, lim, npos, paid⟩
  unfold guardedBoundAt3 at paid
  split at paid
  · exact excluded3 bad known ⟨cut, pos, lim, paid⟩
  · omega

theorem at_completedG {p : Input} (bad : Bad p) (span : ℕ) :
    ¬WindowG3 p.n p.s (cutoff p) projectionFloor span :=
  excludedG bad (available_lower_hosts bad)

attribute [aesop safe forward (immediate := [bad,known]) (rule_sets := [CHGraphFamilies])] excluded3
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] at_completed3
attribute [aesop safe forward (immediate := [bad,known]) (rule_sets := [CHGraphFamilies])] excludedG
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] at_completedG

#print axioms boundAt3_sound
#print axioms excluded3
#print axioms at_completed3
#print axioms excludedG
#print axioms at_completedG
end LeanCH.BR.ShapeClimbAt3
