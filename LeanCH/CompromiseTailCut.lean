module

public import LeanCH.CompromiseCertificateCharge
public import LeanCH.CompromiseSubset

set_option linter.style.header false

/-! Retaining an arbitrary proper set of heads at one tail. Collective
second-path losses are included exactly. Goodness of the whole cut graph
is explicit; single-arc minimality alone does not supply that hypothesis. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseFair CH.CompromiseCritical CH.CompromiseSubset
open CH.CompromiseDeletion
open CH.CompromisePerturbation CH.CompromiseRowRepair CH.CompromiseColumnCoupling
open CH.CompromiseCertificateCharge
open CH.CompromiseInverse CH.CompromiseArcMinimal
public section

namespace CH.CompromiseTailCut

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def retain (i : V) (B : Finset V) (v u : V) : Prop :=
  adj v u ∧ (v ≠ i ∨ u ∈ B)

instance (i : V) (B : Finset V) : DecidableRel (retain adj i B) := fun v u => by
  unfold retain
  infer_instance

@[expose] def WeightedSubgraphMinimal : Prop :=
  ∀ (sub : V → V → Prop) [DecidableRel sub],
    (∀ v u, sub v u → adj v u) → (∃ v u, adj v u ∧ ¬ sub v u) →
      ∀ w : V → ℝ, (∀ v, 0 ≤ w v) → ∃ v, 0 ≤ surplus sub w v

theorem single_arc_minimal (minimal : WeightedSubgraphMinimal adj) : WeightedArcMinimal adj := by
  intro i j edge
  apply minimal (CH.ArcMinimal.eraseArc adj i j) (fun _ _ h => h.1)
  exact ⟨i, j, edge, by simp [CH.ArcMinimal.eraseArc]⟩

theorem cut_good (minimal : WeightedSubgraphMinimal adj) (i : V) (B : Finset V)
    (subset : B ⊆ outN adj i) (proper : B ≠ outN adj i) :
    ∀ w : V → ℝ, (∀ v, 0 ≤ w v) → ∃ v, 0 ≤ surplus (retain adj i B) w v := by
  have notSubset : ¬ outN adj i ⊆ B := fun h => proper (Subset.antisymm subset h)
  obtain ⟨u, hu, outside⟩ := not_subset.mp notSubset
  apply minimal (retain adj i B) (fun _ _ h => h.1)
  refine ⟨i, u, (mem_outN adj i u).mp hu, ?_⟩
  simp only [retain, ne_eq, not_true_eq_false, false_or]
  exact fun h => outside h.2

theorem out_retained (i : V) (B : Finset V) (subset : B ⊆ outN adj i) :
    outN (retain adj i B) i = B := by
  ext u
  simp only [mem_outN, retain, ne_eq, not_true_eq_false, false_or]
  exact ⟨fun h => h.2, fun h => ⟨(mem_outN adj i u).mp (subset h), h⟩⟩

theorem in_retained (noLoop : ∀ v, ¬ adj v v) (i : V) (B : Finset V) :
    inN (retain adj i B) i = inN adj i := by
  ext v
  simp only [mem_inN, retain]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, Or.inl (fun he => noLoop i (by simpa only [he] using h))⟩

theorem second_retained (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (i : V) (B : Finset V) (subset : B ⊆ outN adj i) :
    second (retain adj i B) i = boundary adj B := by
  have noLoop (v : V) : ¬ adj v v := fun h => noDigon v v h h
  ext u
  constructor
  · intro h
    obtain ⟨_, notEdge, a, hia, hau⟩ := (mem_second _ i u).mp h
    have aB : a ∈ B := hia.2.resolve_left (by simp)
    refine mem_sdiff.mpr ⟨(mem_reach adj B u).mpr ⟨a, aB, hau.1⟩, ?_⟩
    intro uB
    exact notEdge ⟨(mem_outN adj i u).mp (subset uB), Or.inr uB⟩
  · intro h
    obtain ⟨reach, outside⟩ := mem_sdiff.mp h
    obtain ⟨a, aB, hau⟩ := (mem_reach adj B u).mp reach
    have hia : adj i a := (mem_outN adj i a).mp (subset aB)
    apply (mem_second _ i u).mpr
    refine ⟨?_, ?_, a, ⟨hia, Or.inr aB⟩, ⟨hau, Or.inl ?_⟩⟩
    · intro he
      exact noDigon i a hia (by simpa only [he] using hau)
    · intro he
      exact outside (he.2.resolve_left (by simp))
    · intro he
      exact noLoop i (by simpa only [he] using hia)

theorem tail_surplus (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (i : V) (B : Finset V) (subset : B ⊆ outN adj i) (w : V → ℝ) :
    surplus (retain adj i B) w i = mass w (boundary adj B) + inWeight adj w i - 2 * mass w B := by
  have noLoop (v : V) : ¬ adj v v := fun h => noDigon v v h h
  simp only [surplus, secondWeight, outWeight, inWeight, second_retained adj noDigon i B subset,
    in_retained adj noLoop, out_retained adj i B subset]

@[expose] def removedHeads (i : V) (B : Finset V) : Finset V := outN adj i \ B
@[expose] def lostEndpoints (i : V) (B : Finset V) : Finset V :=
  second adj i \ second (retain adj i B) i
@[expose] def gainedEndpoints (i : V) (B : Finset V) : Finset V :=
  second (retain adj i B) i \ second adj i

/-- An old endpoint disappears exactly when every middle is removed.
There can be several such middles, even if no single arc loses it. -/
theorem mem_lost_endpoints (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (i : V) (B : Finset V) (subset : B ⊆ outN adj i) (u : V) :
    u ∈ lostEndpoints adj i B ↔ u ∈ second adj i ∧
      ∀ a, adj i a → adj a u → a ∉ B := by
  simp only [lostEndpoints, mem_sdiff, second_retained adj noDigon i B subset]
  constructor
  · rintro ⟨old, lost⟩
    refine ⟨old, ?_⟩
    intro a _ hau aB
    apply lost
    refine mem_sdiff.mpr ⟨(mem_reach adj B u).mpr ⟨a, aB, hau⟩, ?_⟩
    intro uB
    exact ((mem_second adj i u).mp old).2.1 ((mem_outN adj i u).mp (subset uB))
  · rintro ⟨old, removed⟩
    refine ⟨old, ?_⟩
    intro reached
    obtain ⟨a, aB, hau⟩ := (mem_reach adj B u).mp (mem_sdiff.mp reached).1
    exact removed a ((mem_outN adj i a).mp (subset aB)) hau aB

theorem gained_subset_removed (i : V) (B : Finset V) :
    gainedEndpoints adj i B ⊆ removedHeads adj i B := by
  intro u hu
  obtain ⟨new, old⟩ := mem_sdiff.mp hu
  obtain ⟨hne, noEdge, a, hia, hau⟩ := (mem_second _ i u).mp new
  have original : adj i u := by
    by_contra noOriginal
    exact old ((mem_second adj i u).mpr ⟨hne, noOriginal, a, hia.1, hau.1⟩)
  refine mem_sdiff.mpr ⟨(mem_outN adj i u).mpr original, ?_⟩
  exact fun uB => noEdge ⟨original, Or.inr uB⟩

theorem exact_gain (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (i : V) (B : Finset V) (subset : B ⊆ outN adj i) (w : V → ℝ) :
    surplus (retain adj i B) w i - surplus adj w i =
      2 * mass w (removedHeads adj i B) + mass w (gainedEndpoints adj i B) -
        mass w (lostEndpoints adj i B) := by
  have noLoop (v : V) : ¬ adj v v := fun h => noDigon v v h h
  have heads := sum_sdiff (f := w) subset
  change mass w (removedHeads adj i B) + mass w B = outWeight adj w i at heads
  have seconds : mass w (gainedEndpoints adj i B) - mass w (lostEndpoints adj i B) =
      secondWeight (retain adj i B) w i - secondWeight adj w i := by
    exact sum_sdiff_sub_sum_sdiff
  have incoming : inWeight (retain adj i B) w i = inWeight adj w i := by
    simp only [inWeight, in_retained adj noLoop]
  have outgoing : outWeight (retain adj i B) w i = mass w B := by
    simp only [outWeight, out_retained adj i B subset]
  dsimp [surplus]
  rw [incoming, outgoing]
  linarith

theorem off_tail_le (i : V) (B : Finset V) (v u : V) (vi : v ≠ i) :
    coefficient (retain adj i B) v u ≤ coefficient adj v u := by
  have outSame : retain adj i B v u ↔ adj v u := by simp [retain, vi]
  have secondSubset : u ∈ second (retain adj i B) v → u ∈ second adj v := by
    intro h
    obtain ⟨hne, noEdge, a, hva, hau⟩ := (mem_second _ v u).mp h
    exact (mem_second adj v u).mpr
      ⟨hne, fun he => noEdge (outSame.mpr he), a, hva.1, hau.1⟩
  have hs : (if u ∈ second (retain adj i B) v then (1 : ℝ) else 0) ≤
      if u ∈ second adj v then 1 else 0 := by
    by_cases h : u ∈ second (retain adj i B) v
    · simp only [h, secondSubset h, ite_true, le_refl]
    · simp only [h, ite_false]
      split_ifs <;> norm_num
  have hi : (if retain adj i B u v then (1 : ℝ) else 0) ≤ if adj u v then 1 else 0 := by
    by_cases h : retain adj i B u v
    · simp only [h, h.1, ite_true, le_refl]
    · simp only [h, ite_false]
      split_ifs <;> norm_num
  simp only [coefficient, CH.CompromisePacking.capacity, outSame]
  linarith

@[expose] def changeRow (i : V) (B : Finset V) (u : V) : ℝ :=
  coefficient (retain adj i B) i u - coefficient adj i u

theorem coefficient_bound (i : V) (B : Finset V) (v u : V) :
    coefficient (retain adj i B) v u ≤ shiftRow (coefficient adj) i (changeRow adj i B) v u := by
  by_cases vi : v = i
  · subst v
    simp only [shiftRow, changeRow, ite_true]
    linarith
  · simpa only [shiftRow, ite_eq_right vi, add_zero] using off_tail_le adj i B v u vi

theorem change_pairing (i : V) (B : Finset V) (w : V → ℝ) :
    pairing (changeRow adj i B) w = surplus (retain adj i B) w i - surplus adj w i := by
  simp only [pairing, changeRow, sub_mul, sum_sub_distrib]
  exact congrArg₂ (fun x y : ℝ => x - y) (row_coefficient (retain adj i B) w i)
    (row_coefficient adj w i)

/-- The same cut certificate pays the common deficit and all losses
outside the changed tail. The loss term is retained before weakening. -/
theorem deficit_budget (i : V) (B : Finset V) (w p : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hp : p ∈ simplex)
    (fair : ∀ u, 0 ≤ col (coefficient (retain adj i B)) p u)
    (kappa : ℝ) (rows : ∀ v, surplus adj w v ≤ -kappa) :
    kappa + payoff (loss (coefficient adj) (coefficient (retain adj i B))
      i (changeRow adj i B)) w p ≤
        p i * (surplus (retain adj i B) w i - surplus adj w i) := by
  have old : payoff (coefficient adj) w p ≤ -kappa := by
    calc
      _ = ∑ v, p v * surplus adj w v := by simp [payoff, row_coefficient]
      _ ≤ ∑ v, p v * (-kappa) := sum_le_sum (fun v _ =>
        mul_le_mul_of_nonneg_left (rows v) (hp.1 v))
      _ = -kappa := by simp [← sum_mul, hp.2]
  have now : 0 ≤ payoff (coefficient (retain adj i B)) w p := by
    rw [payoff_transpose]
    exact sum_nonneg (fun u _ => mul_nonneg (hw u) (fair u))
  have identity := payoff_loss (coefficient adj) (coefficient (retain adj i B))
    i (changeRow adj i B) w p
  rw [payoff_shift, change_pairing] at identity
  linarith

/-- A nonempty retained set forces a gain of at least three deficits,
including losses of endpoints with several deleted middle vertices. -/
theorem three_deficit_cut (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (i : V) (B : Finset V) (subset : B ⊆ outN adj i) (nonempty : B.Nonempty)
    (good : ∀ w : V → ℝ, (∀ v, 0 ≤ w v) → ∃ v, 0 ≤ surplus (retain adj i B) w v)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa) :
    3 * kappa ≤ surplus (retain adj i B) w i - surplus adj w i := by
  let : Nonempty V := ⟨i⟩
  have noBad : ¬ ∃ y ∈ simplex, ∀ v, row (coefficient (retain adj i B)) y v < 0 := by
    rintro ⟨y, hy, bad⟩
    obtain ⟨v, hv⟩ := good y hy.1
    have hh := bad v
    rw [row_coefficient] at hh
    linarith
  obtain ⟨p, hp, fair⟩ := (fair_iff_no_bad _).mpr noBad
  obtain ⟨u, hu⟩ := nonempty
  have retained : retain adj i B i u := ⟨(mem_outN adj i u).mp (subset hu), Or.inr hu⟩
  have nd : ∀ v z, retain adj i B v z → ¬ retain adj i B z v :=
    fun v z h hh => noDigon v z h.1 hh.1
  have nt : ∀ v z a, retain adj i B v z → retain adj i B z a → ¬ retain adj i B a v :=
    fun v z a h hh hhh => noTri v z a h.1 hh.1 hhh.1
  have tail := fair_tail_bound _ nd nt p hp fair i u retained
  have budget := deficit_budget adj i B w p hw hp fair kappa rows
  have lossNonneg := payoff_nonnegative _
    (loss_nonnegative _ _ i _ (coefficient_bound adj i B)) w p hw hp.1
  have gainPositive : 0 < surplus (retain adj i B) w i - surplus adj w i := by
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos (hp.1 i) (le_of_not_gt hn)
    linarith
  nlinarith [hp.1 u]

/-- At an equalized counterweight this is a proper-subset expansion
condition with a two-deficit margin, not a new full-graph theorem. -/
theorem retained_boundary_charge (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (minimal : WeightedSubgraphMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v = -kappa)
    (i : V) (B : Finset V) (subset : B ⊆ outN adj i)
    (nonempty : B.Nonempty) (proper : B ≠ outN adj i) :
    2 * mass w B + 2 * kappa ≤ mass w (boundary adj B) + inWeight adj w i := by
  have bound := three_deficit_cut adj noDigon noTri i B subset nonempty
    (cut_good adj minimal i B subset proper) w hw kappa kp (fun v => (rows v).le)
  rw [tail_surplus adj noDigon i B subset, rows i] at bound
  linarith

/-- All original inverse columns are constrained by the same fair
certificate of the entire cut, not by separate single-arc witnesses. -/
theorem all_column_charge (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (deleted : DeletedFair adj) (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v)
    (bad0 : ∀ v, surplus adj w0 v < 0)
    (i : V) (B : Finset V) (subset : B ⊆ outN adj i)
    (good : ∀ w : V → ℝ, (∀ v, 0 ≤ w v) → ∃ v, 0 ≤ surplus (retain adj i B) w v)
    (k : V) :
    (if k = i then (1 : ℝ) else 0) + mass (fun u => Q adj u k) (lostEndpoints adj i B) ≤
      2 * mass (fun u => Q adj u k) (removedHeads adj i B) +
        mass (fun u => Q adj u k) (gainedEndpoints adj i B) := by
  let : Nonempty V := ⟨i⟩
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w0 hw0 bad0
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  have noBad : ¬ ∃ y ∈ simplex, ∀ v, row (coefficient (retain adj i B)) y v < 0 := by
    rintro ⟨y, hy, bad⟩
    obtain ⟨v, hv⟩ := good y hy.1
    have hh := bad v
    rw [row_coefficient] at hh
    linarith
  obtain ⟨p, hp, fair⟩ := (fair_iff_no_bad _).mpr noBad
  have pi := certificate_tail_positive (CH.CompromiseInverse.matrix adj) unit qn
    (coefficient (retain adj i B)) i (changeRow adj i B) p hp
    (coefficient_bound adj i B) fair
  have coupling := transport (CH.CompromiseInverse.matrix adj) unit qn
    (coefficient (retain adj i B)) i (changeRow adj i B) p fair k
  change p k + payoff (loss (coefficient adj) (coefficient (retain adj i B))
    i (changeRow adj i B)) (fun u => Q adj u k) p ≤
      p i * pairing (changeRow adj i B) (fun u => Q adj u k) at coupling
  have lossNonneg := payoff_nonnegative _
    (loss_nonnegative _ _ i _ (coefficient_bound adj i B))
    (fun u => Q adj u k) p (fun u => qn u k) hp.1
  rw [change_pairing, exact_gain adj noDigon i B subset] at coupling
  by_cases ki : k = i
  · subst k
    simp only [ite_true]
    nlinarith
  · simp only [ite_eq_right ki]
    nlinarith [hp.1 k]

/-- Collective path losses charge the whole inverse block on the
removed heads, with the gained-head contribution kept separately. -/
theorem collective_loss_block_sharp (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v) (bad0 : ∀ v, surplus adj w0 v < 0)
    (i : V) (B : Finset V) (subset : B ⊆ outN adj i)
    (good : ∀ w : V → ℝ, (∀ v, 0 ≤ w v) → ∃ v, 0 ≤ surplus (retain adj i B) w v) :
    ((lostEndpoints adj i B).card : ℝ) ≤
      6 * (∑ k ∈ removedHeads adj i B, mass (fun u => Q adj u k) (removedHeads adj i B)) +
        3 * ∑ k ∈ removedHeads adj i B, mass (fun u => Q adj u k) (gainedEndpoints adj i B) := by
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _
    (graph_inverse_nonpos adj deleted w0 hw0 bad0).2
  have columnBound (k : V) : mass (fun u => Q adj u k) (lostEndpoints adj i B) ≤
      2 * mass (fun u => Q adj u k) (removedHeads adj i B) +
        mass (fun u => Q adj u k) (gainedEndpoints adj i B) := by
    have bound := all_column_charge adj noDigon deleted w0 hw0 bad0 i B subset good k
    split_ifs at bound <;> linarith
  have endpointBound (u : V) (hu : u ∈ lostEndpoints adj i B) :
      1 ≤ 3 * mass (fun k => Q adj u k) (removedHeads adj i B) := by
    obtain ⟨old, excluded⟩ := (mem_lost_endpoints adj noDigon i B subset u).mp hu
    obtain ⟨_, _, a, hia, hau⟩ := (mem_second adj i u).mp old
    have aC : a ∈ removedHeads adj i B :=
      mem_sdiff.mpr ⟨(mem_outN adj i a).mpr hia, excluded a hia hau⟩
    have charge := arc_lower adj deleted minimal w0 hw0 bad0 a u hau
    have term := single_le_sum (fun k (_ : k ∈ removedHeads adj i B) => qn u k) aC
    change Q adj u a ≤ mass (fun k => Q adj u k) (removedHeads adj i B) at term
    linarith
  have lower := sum_le_sum endpointBound
  have upper := sum_le_sum (s := removedHeads adj i B) (fun k _ => columnBound k)
  simp only [sum_const, nsmul_eq_mul, mul_one, sum_add_distrib, ← mul_sum] at lower upper
  have commute : (∑ u ∈ lostEndpoints adj i B, mass (fun k => Q adj u k) (removedHeads adj i B)) =
      ∑ k ∈ removedHeads adj i B, mass (fun u => Q adj u k) (lostEndpoints adj i B) := by
    exact sum_comm
  rw [commute] at lower
  linarith

theorem collective_loss_block_bound (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (deleted : DeletedFair adj) (minimal : WeightedSubgraphMinimal adj)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v) (bad0 : ∀ v, surplus adj w0 v < 0)
    (i : V) (B : Finset V) (subset : B ⊆ outN adj i) (proper : B ≠ outN adj i) :
    ((lostEndpoints adj i B).card : ℝ) ≤
      9 * ∑ k ∈ removedHeads adj i B, mass (fun u => Q adj u k) (removedHeads adj i B) := by
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _
    (graph_inverse_nonpos adj deleted w0 hw0 bad0).2
  have bound := collective_loss_block_sharp adj noDigon deleted (single_arc_minimal adj minimal)
    w0 hw0 bad0 i B subset (cut_good adj minimal i B subset proper)
  have gains := sum_le_sum (s := removedHeads adj i B) (fun k _ =>
    weight_mono (fun u => Q adj u k) (fun u => qn u k) _ _ (gained_subset_removed adj i B))
  linarith

/-- Deleting every outgoing arc makes the tail a sink, so this block
bound needs only the earlier single-arc minimality assumption. -/
theorem full_tail_block_bound (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v) (bad0 : ∀ v, surplus adj w0 v < 0) (i : V) :
    ((second adj i).card : ℝ) ≤ 6 * ∑ k ∈ outN adj i, mass (fun u => Q adj u k) (outN adj i) := by
  have emptySecond : second (retain adj i ∅) i = ∅ := by
    rw [second_retained adj noDigon i ∅ (empty_subset _)]
    simp [boundary, reach]
  have good (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) :
      ∃ v, 0 ≤ surplus (retain adj i ∅) w v := by
    refine ⟨i, ?_⟩
    rw [tail_surplus adj noDigon i ∅ (empty_subset _)]
    simpa [boundary, reach, mass, inWeight] using weight_nonneg w hw (inN adj i)
  have bound := collective_loss_block_sharp adj noDigon deleted minimal w0 hw0 bad0
    i ∅ (empty_subset _) good
  simpa only [removedHeads, sdiff_empty, lostEndpoints, gainedEndpoints, emptySecond,
    empty_sdiff, mass, sum_empty, sum_const_zero, mul_zero, add_zero] using bound

theorem zero_block_losses_empty (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (deleted : DeletedFair adj) (minimal : WeightedSubgraphMinimal adj)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v) (bad0 : ∀ v, surplus adj w0 v < 0)
    (i : V) (B : Finset V) (subset : B ⊆ outN adj i) (proper : B ≠ outN adj i)
    (zero : ∀ j ∈ removedHeads adj i B, ∀ k ∈ removedHeads adj i B, Q adj j k = 0) :
    lostEndpoints adj i B = ∅ := by
  have bound := collective_loss_block_bound adj noDigon deleted minimal
    w0 hw0 bad0 i B subset proper
  have block : (∑ k ∈ removedHeads adj i B,
      mass (fun u => Q adj u k) (removedHeads adj i B)) = 0 := by
    apply sum_eq_zero
    intro k hk
    exact sum_eq_zero (fun j hj => zero j hj k hk)
  rw [block, mul_zero] at bound
  have count : (lostEndpoints adj i B).card ≤ 0 := by exact_mod_cast bound
  exact card_eq_zero.mp (by omega)

end CH.CompromiseTailCut

#print axioms CH.CompromiseTailCut.second_retained
#print axioms CH.CompromiseTailCut.mem_lost_endpoints
#print axioms CH.CompromiseTailCut.exact_gain
#print axioms CH.CompromiseTailCut.deficit_budget
#print axioms CH.CompromiseTailCut.three_deficit_cut
#print axioms CH.CompromiseTailCut.retained_boundary_charge
#print axioms CH.CompromiseTailCut.all_column_charge
#print axioms CH.CompromiseTailCut.collective_loss_block_sharp
#print axioms CH.CompromiseTailCut.collective_loss_block_bound
#print axioms CH.CompromiseTailCut.full_tail_block_bound
#print axioms CH.CompromiseTailCut.zero_block_losses_empty
