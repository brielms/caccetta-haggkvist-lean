import checkpoints.shen_extension.ShapeClimb

/-!
# The shape climb at the true degree

`ShapeClimb.bound' q d` runs the layer-shape climb at degree `d` over the bank
`library q (d - 1)`, and its window calls it at `d = min r limit`. Here the same climb runs
at the true degree `r` over the bank `library q c` of the closed lower degrees `t ≤ c < r`.
Everything is generic in `q`, `r` and `c`.
-/

namespace LeanCH.BR.ShapeClimbAt
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion RecursivePrefixBudget ShapeClimb

/-- The top comparison of the climb at degree `r` over the bank of degrees `≤ c`. -/
def resultAt (q r c : ℕ) : Comparison := middle' q r (library q c)

def strictGainAt (q r c : ℕ) (b : Comparison) : Prop :=
  2 * (q / 2 / 2) = q / 2 ∧
    b.left + 2 ≤ 2 * (layers' q r (library q c) (q / 2 / 2)).getD (q / 2 / 2) 0

instance {q r c b} : Decidable (strictGainAt q r c b) := by unfold strictGainAt; infer_instance

/-- The order bound at degree `r` from the bank of degrees `≤ c`. -/
def boundAt (q r c : ℕ) : ℕ :=
  let b := resultAt q r c
  b.left + b.right + (if strictGainAt q r c b then 1 else 0) - 2

theorem library_bankAt {q r c} (hq : 2 ≤ q) (cr : c < r) (known : ∀ t, t ≤ c → NoHost q t) :
    ∀ b ∈ library q c, Valid q b ∧ b.degree ≤ r ∧ NoHost q b.degree := by
  have prev := library_sound hq c (fun t ht => known t ht.le)
  exact fun b hb => ⟨(prev b hb).1, (prev b hb).2.trans cr.le, known _ (prev b hb).2⟩

theorem resultAt_valid {q r c} (hq : 2 ≤ q) (cr : c < r) (known : ∀ t, t ≤ c → NoHost q t) :
    Valid q (resultAt q r c) :=
  middle'_valid hq (library_bankAt hq cr known)

theorem boundAt_sound {q r c} (hq : 2 ≤ q) (hr : 0 < r) (cr : c < r)
    (known : ∀ t, t ≤ c → NoHost q t)
    {D V} (free : QFree D V q) (ne : V.Nonempty) (deg : ∀ v ∈ V, r ≤ (outN D V v).card) :
    boundAt q r c < V.card := by
  have _ := hr
  let b := resultAt q r c
  obtain ⟨left, right⟩ := resultAt_valid hq cr known
  change Floor q r (q / 2) b.left at left
  change Floor q r (q - q / 2) b.right at right
  change b.left + b.right + (if strictGainAt q r c b then 1 else 0) - 2 < V.card
  have pos := card_pos.mpr ne
  split
  next gain =>
    obtain ⟨eq, more⟩ := gain
    obtain ⟨-, bank⟩ := layers'_sound (by omega : 1 ≤ q) (library_bankAt hq cr known) (q / 2 / 2)
      (by omega)
    have size := SharedBankOrderTransfer.strict_order (k := q / 2 / 2) free ne
      (by omega : 2 * (q / 2 / 2) + (q - q / 2) ≤ q) (bank (q / 2 / 2) D V free deg)
      (eq.symm ▸ left D V free deg) (right D V free deg) more
    omega
  next =>
    have size := order_of_floors (by omega : q / 2 + (q - q / 2) ≤ q) left right D V free deg ne
    omega

end LeanCH.BR.ShapeClimbAt

/-! ### The order window at the true degree -/

namespace LeanCH.BR.ShapeClimbAt
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion CHRuleCatalog ProjectedQuotaTransfer
open RecursivePrefixBudget

/-- The window with the bound supplied, so a caller computes `boundAt` once per `(q, r)`. -/
@[ch_numeric_guard] def WindowWith (b n r q limit : ℕ) : Prop :=
  2 ≤ q ∧ 0 < r ∧ 0 < limit ∧ n ≤ b

instance {b n r q limit} : Decidable (WindowWith b n r q limit) := by
  unfold WindowWith; infer_instance

@[ch_numeric_guard] def Window (n r q limit : ℕ) : Prop :=
  2 ≤ q ∧ 0 < r ∧ 0 < limit ∧ n ≤ boundAt q r (min (r - 1) (limit - 1))

instance {n r q limit} : Decidable (Window n r q limit) := by unfold Window; infer_instance

theorem window_iff {n r q limit} :
    Window n r q limit ↔ WindowWith (boundAt q r (min (r - 1) (limit - 1))) n r q limit :=
  Iff.rfl

theorem excluded {p : Input} {limit} (bad : Bad p) (known : ∀ t, t < limit → NoHost (cutoff p) t) :
    ¬Window p.n p.s (cutoff p) limit := by
  rintro ⟨cut, pos, lim, paid⟩
  have certificate : GuardedFamilyRules.OrderBound (cutoff p) p.s
      (boundAt (cutoff p) p.s (min (p.s - 1) (limit - 1))) :=
    ⟨lt_of_lt_of_le bad.order paid, fun _ _ free ne deg => boundAt_sound cut pos
      (lt_of_le_of_lt (min_le_left ..) (by omega))
      (fun t ht => known t (by have := ht.trans (min_le_right ..); omega)) free ne deg⟩
  exact GuardedFamilyRules.forbidden bad certificate ⟨le_rfl, le_rfl, by omega⟩

theorem at_completed {p : Input} (bad : Bad p) :
    ¬Window p.n p.s (cutoff p) projectionFloor := excluded bad (available_lower_hosts bad)

/-- The bound, used only at degrees at most `span` above the closed prefix `limit`. -/
def guardedBoundAt (q r limit span : ℕ) : ℕ :=
  if r ≤ limit + span then boundAt q r (min (r - 1) (limit - 1)) else 0

/-- The guarded window with the bound supplied, so a caller computes it once per `(q, r)`. -/
@[ch_numeric_guard] def WindowGWith (b n r q limit : ℕ) : Prop :=
  2 ≤ q ∧ 0 < r ∧ 0 < limit ∧ 0 < n ∧ n ≤ b

instance {b n r q limit} : Decidable (WindowGWith b n r q limit) := by
  unfold WindowGWith; infer_instance

@[ch_numeric_guard] def WindowG (n r q limit span : ℕ) : Prop :=
  2 ≤ q ∧ 0 < r ∧ 0 < limit ∧ 0 < n ∧ n ≤ guardedBoundAt q r limit span

instance {n r q limit span} : Decidable (WindowG n r q limit span) := by
  unfold WindowG; infer_instance

theorem windowG_iff {n r q limit span} :
    WindowG n r q limit span ↔ WindowGWith (guardedBoundAt q r limit span) n r q limit :=
  Iff.rfl

theorem excludedG {p : Input} {limit span} (bad : Bad p)
    (known : ∀ t, t < limit → NoHost (cutoff p) t) :
    ¬WindowG p.n p.s (cutoff p) limit span := by
  rintro ⟨cut, pos, lim, npos, paid⟩
  unfold guardedBoundAt at paid
  split at paid
  · exact excluded bad known ⟨cut, pos, lim, paid⟩
  · omega

theorem at_completedG {p : Input} (bad : Bad p) (span : ℕ) :
    ¬WindowG p.n p.s (cutoff p) projectionFloor span :=
  excludedG bad (available_lower_hosts bad)

attribute [aesop safe forward (immediate := [bad,known]) (rule_sets := [CHGraphFamilies])] excluded
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] at_completed
attribute [aesop safe forward (immediate := [bad,known]) (rule_sets := [CHGraphFamilies])] excludedG
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] at_completedG

#print axioms boundAt_sound
#print axioms excluded
#print axioms at_completed
#print axioms excludedG
#print axioms at_completedG
end LeanCH.BR.ShapeClimbAt
