module

public import LeanCH.CompromiseNoBypass

set_option linter.style.header false

/-! Low-weight vertices have tightly constrained incoming subgraphs.
The bounds use weighted minimality and a common positive surplus deficit;
they do not assert that these remaining patterns are impossible. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseDeletion CH.CompromiseCritical CH.CompromiseInverse
open CH.CompromisePerturbation CH.CompromiseArcMinimal CH.CompromiseLostArc
open CH.CompromiseSharedPaths CH.CompromiseCertificateCharge CH.CompromiseUnitMinimal
open CH.CompromiseMinimumWeight CH.CompromiseNoBypass
public section

namespace CH.CompromiseSmallIncoming

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

theorem four_of_no_sink (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v) (j : V)
    (ne : (inN adj j).Nonempty) (empty : noBypassParents adj j = ∅) :
    4 ≤ (inN adj j).card := by
  have revOut : outN (fun a b => adj b a) j = inN adj j := by ext; simp
  have nd : ∀ v u, adj u v → ¬ adj v u := fun v u => noDigon u v
  have nt : ∀ v u z, adj u v → adj z u → ¬ adj v z :=
    fun v u z huv hzu hvz => noTri z u v hzu huv hvz
  have hh := four_of_internal (fun a b => adj b a) nd nt j
    (by simpa [revOut] using ne) (by
      intro i hi
      rw [revOut] at hi
      have hs : j ∈ second (CH.ArcMinimal.eraseArc adj i j) i := by
        by_contra hn
        have hm : i ∈ noBypassParents adj j := mem_filter.mpr ⟨hi, hn⟩
        rw [empty] at hm
        simp at hm
      obtain ⟨_, _, a, hia, haj⟩ := (mem_second _ i j).mp hs
      exact ⟨a, by simpa [revOut] using (mem_inN adj j a).mpr haj.1, hia.1⟩)
  simpa [revOut] using hh

/-- The established atom floor makes every predecessor of a vertex
with mass below 2*kappa branch, even away from the minimum weight. -/
theorem low_weight_branches (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa) (floor : ∀ v, 3 * kappa ≤ 2 * w v)
    (ip : ∀ v, (inN adj v).Nonempty) (j : V) (small : w j < 2 * kappa)
    (i : V) (edge : adj i j) : ∃ u, adj i u ∧ u ≠ j := by
  by_contra hn
  push Not at hn
  have singleton : outN adj i = {j} := by
    ext u
    simp only [mem_outN, mem_singleton]
    exact ⟨hn u, fun h => h ▸ edge⟩
  have outj : (outN adj j).Nonempty := by
    by_contra hh
    have he : outN adj j = ∅ := not_nonempty_iff_eq_empty.mp hh
    have zero : outWeight adj w j = 0 := by simp [outWeight, mass, he]
    have hs := weight_nonneg w hw (second adj j)
    have hi := weight_nonneg w hw (inN adj j)
    have hb := rows j
    dsimp [surplus, secondWeight, inWeight] at hb
    rw [zero] at hb
    linarith
  obtain ⟨a, ha⟩ := outj
  have hja : adj j a := (mem_outN adj j a).mp ha
  have secondA : a ∈ second adj i := by
    apply (mem_second adj i a).mpr
    refine ⟨?_, ?_, j, edge, hja⟩
    · intro he
      subst a
      exact noDigon i j edge hja
    · intro hia
      have he := hn a hia
      subst a
      exact noDigon j j hja hja
  obtain ⟨b, hb⟩ := ip i
  have so : w a ≤ secondWeight adj w i := single_le_sum (fun v _ => hw v) secondA
  have si : w b ≤ inWeight adj w i := single_le_sum (fun v _ => hw v) hb
  have oo : outWeight adj w i = w j := by simp [outWeight, mass, singleton]
  have hh := rows i
  dsimp [surplus] at hh
  rw [oo] at hh
  linarith [floor a, floor b]

/-- Below 2*kappa there are at most four predecessors. Three predecessors
force exactly one internal sink; four force no internal sink. -/
theorem below_two_structure [Nonempty V]
    (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa) (j : V) (small : w j < 2 * kappa) :
    1 ≤ (inN adj j).card ∧ (inN adj j).card ≤ 4 ∧
      ((inN adj j).card = 3 → (noBypassParents adj j).card = 1) ∧
      ((inN adj j).card = 4 → noBypassParents adj j = ∅) := by
  have bad : ∀ v, surplus adj w v < 0 := fun v => lt_of_le_of_lt (rows v) (by linarith)
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w hw bad
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  have ip (v : V) : (inN adj v).Nonempty := card_pos.mp (in_positive adj unit qn v)
  have floor := minimum_weight_bound adj noDigon noTri deleted minimal w hw kappa kp rows
  have branch := low_weight_branches adj noDigon w hw kappa kp rows floor ip j small
  obtain ⟨i, hi⟩ := ip j
  have edge := (mem_inN adj j i).mp hi
  obtain ⟨u, other, hne⟩ := branch i edge
  have count := branch_row_bound adj noDigon noTri deleted minimal w hw bad i j u edge other hne
  have budget := inverse_weighted_row_bound adj unit qn w kappa rows j
  have degree : ((inN adj j).card : ℝ) < 5 := by nlinarith
  have degNat : (inN adj j).card < 5 := by exact_mod_cast degree
  have one : 1 ≤ (inN adj j).card := card_pos.mpr (ip j)
  refine ⟨one, by omega, ?_, ?_⟩
  · intro hd
    have nz : (noBypassParents adj j).Nonempty := by
      by_contra hn
      have hh := four_of_no_sink adj noDigon noTri j (ip j) (not_nonempty_iff_eq_empty.mp hn)
      omega
    have hc := no_bypass_row_bound adj noDigon noTri deleted minimal w hw bad j nz branch
    rw [hd] at hc
    have hr : ((noBypassParents adj j).card : ℝ) < 2 := by norm_num at hc; nlinarith
    have hn : (noBypassParents adj j).card < 2 := by exact_mod_cast hr
    have hp := card_pos.mpr nz
    omega
  · intro hd
    apply not_nonempty_iff_eq_empty.mp
    intro nz
    have hc := no_bypass_row_bound adj noDigon noTri deleted minimal w hw bad j nz branch
    have hp : (1 : ℝ) ≤ (noBypassParents adj j).card := by exact_mod_cast card_pos.mpr nz
    rw [hd] at hc
    norm_num at hc
    nlinarith

/-- Below 5*kappa/3, the only possible incoming cardinalities are one,
or two with precisely one sink. -/
theorem below_five_thirds_counts [Nonempty V]
    (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa) (j : V) (small : 3 * w j < 5 * kappa) :
    (inN adj j).card = 1 ∨
      ((inN adj j).card = 2 ∧ (noBypassParents adj j).card = 1) := by
  have bad : ∀ v, surplus adj w v < 0 := fun v => lt_of_le_of_lt (rows v) (by linarith)
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w hw bad
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  have ip (v : V) : (inN adj v).Nonempty := card_pos.mp (in_positive adj unit qn v)
  have floor := minimum_weight_bound adj noDigon noTri deleted minimal w hw kappa kp rows
  have branch := low_weight_branches adj noDigon w hw kappa kp rows floor ip j (by linarith)
  have budget := inverse_weighted_row_bound adj unit qn w kappa rows j
  have nz : (noBypassParents adj j).Nonempty := by
    by_contra hn
    have four := four_of_no_sink adj noDigon noTri j (ip j) (not_nonempty_iff_eq_empty.mp hn)
    obtain ⟨i, hi⟩ := ip j
    have edge := (mem_inN adj j i).mp hi
    obtain ⟨u, other, hne⟩ := branch i edge
    have count := branch_row_bound adj noDigon noTri deleted minimal w hw bad i j u edge other hne
    have fr : (4 : ℝ) ≤ (inN adj j).card := by exact_mod_cast four
    nlinarith
  have hc := no_bypass_row_bound adj noDigon noTri deleted minimal w hw bad j nz branch
  have hr : 2 * ((inN adj j).card : ℝ) + ((noBypassParents adj j).card : ℝ) < 6 := by
    nlinarith
  have hn : 2 * (inN adj j).card + (noBypassParents adj j).card < 6 := by exact_mod_cast hr
  have hp := card_pos.mpr nz
  have hi := card_pos.mpr (ip j)
  omega

theorem pair_with_one_sink (noLoop : ∀ v, ¬ adj v v) (j : V)
    (two : (inN adj j).card = 2) (one : (noBypassParents adj j).card = 1) :
    ∃ a b, a ≠ b ∧ inN adj j = {a, b} ∧ adj a b := by
  have hex : ∃ a ∈ inN adj j, ∃ b ∈ inN adj j, adj a b := by
    by_contra hn
    push Not at hn
    have he : noBypassParents adj j = inN adj j := by
      apply subset_antisymm (no_bypass_subset adj j)
      intro a ha
      exact (no_bypass_iff adj noLoop j a).mpr ⟨(mem_inN adj j a).mp ha, hn a ha⟩
    rw [he] at one
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := hex
  have hne : a ≠ b := by intro h; subst b; exact noLoop a hab
  have sub : ({a, b} : Finset V) ⊆ inN adj j := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have eq : ({a, b} : Finset V) = inN adj j := eq_of_subset_of_card_le sub (by simp [two, hne])
  exact ⟨a, b, hne, eq.symm, hab⟩

theorem below_five_thirds_shape [Nonempty V]
    (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa) (j : V) (small : 3 * w j < 5 * kappa) :
    (∃ a, inN adj j = {a}) ∨ (∃ a b, a ≠ b ∧ inN adj j = {a, b} ∧ adj a b) := by
  rcases below_five_thirds_counts adj noDigon noTri deleted minimal w hw kappa kp rows
    j small with h | h
  · exact Or.inl (card_eq_one.mp h)
  · exact Or.inr (pair_with_one_sink adj (fun v hh => noDigon v v hh hh) j h.1 h.2)

/-- The four-predecessor, sink-free boundary is an actual directed
four-cycle. Triangle-freeness forbids both diagonals of that cycle. -/
theorem four_incoming_cycle (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v) (j : V)
    (four : (inN adj j).card = 4) (empty : noBypassParents adj j = ∅) :
    ∃ a b c d, inN adj j = {a, b, c, d} ∧ ({a, b, c, d} : Finset V).card = 4 ∧
      adj a b ∧ adj b c ∧ adj c d ∧ adj d a := by
  have noLoop (v : V) : ¬ adj v v := fun h => noDigon v v h h
  have step (x : V) (hx : x ∈ inN adj j) : ∃ y ∈ inN adj j, adj x y := by
    by_contra hn
    push Not at hn
    have hz := (no_bypass_iff adj noLoop j x).mpr ⟨(mem_inN adj j x).mp hx, hn⟩
    rw [empty] at hz
    simp at hz
  obtain ⟨a, ha⟩ := card_pos.mp (show 0 < (inN adj j).card by omega)
  obtain ⟨b, hb, hab⟩ := step a ha
  obtain ⟨c, hc, hbc⟩ := step b hb
  obtain ⟨d, hd, hcd⟩ := step c hc
  have ab : a ≠ b := by intro h; subst b; exact noLoop a hab
  have bc : b ≠ c := by intro h; subst c; exact noLoop b hbc
  have ac : a ≠ c := by intro h; subst c; exact noDigon a b hab hbc
  have cd : c ≠ d := by intro h; subst d; exact noLoop c hcd
  have bd : b ≠ d := by intro h; subst d; exact noDigon b c hbc hcd
  have ad : a ≠ d := by intro h; subst d; exact noTri a b c hab hbc hcd
  have sub : ({a, b, c, d} : Finset V) ⊆ inN adj j := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have card : ({a, b, c, d} : Finset V).card = 4 := by simp [ab, ac, ad, bc, bd, cd]
  have eq : inN adj j = {a, b, c, d} :=
    (eq_of_subset_of_card_le sub (by omega)).symm
  obtain ⟨e, he, hde⟩ := step d hd
  rw [eq] at he
  simp only [mem_insert, mem_singleton] at he
  have hda : adj d a := by
    rcases he with he | he | he | he
    · simpa [he] using hde
    · subst e
      exact (noTri b c d hbc hcd hde).elim
    · subst e
      exact (noDigon c d hcd hde).elim
    · subst e
      exact (noLoop d hde).elim
  exact ⟨a, b, c, d, eq, card, hab, hbc, hcd, hda⟩

/-- A low-weight head has no private lost endpoint on a no-bypass arc,
and at most one on an arc with a bypass. -/
theorem low_head_lost_bound [Nonempty V]
    (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa) (j : V) (small : w j < 2 * kappa)
    (i : V) (edge : adj i j) :
    (lostSecond adj i j).card ≤
      if j ∈ second (CH.ArcMinimal.eraseArc adj i j) i then 1 else 0 := by
  have bad : ∀ v, surplus adj w v < 0 := fun v => lt_of_le_of_lt (rows v) (by linarith)
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w hw bad
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  have ip (v : V) : (inN adj v).Nonempty := card_pos.mp (in_positive adj unit qn v)
  have floor := minimum_weight_bound adj noDigon noTri deleted minimal w hw kappa kp rows
  obtain ⟨u, other, hne⟩ := low_weight_branches adj noDigon w hw kappa kp rows floor ip
    j small i edge
  have gain := three_deficit_charge adj noDigon noTri minimal w hw kappa kp rows
    i j u edge other hne
  have lower := sum_le_sum (s := lostSecond adj i j) (fun v _ => floor v)
  simp only [sum_const, nsmul_eq_mul, ← mul_sum] at lower
  change ((lostSecond adj i j).card : ℝ) * (3 * kappa) ≤
    2 * mass w (lostSecond adj i j) at lower
  by_cases h : j ∈ second (CH.ArcMinimal.eraseArc adj i j) i
  · simp only [ite_eq_left h]
    simp only [newHead, ite_eq_left h] at gain
    have hr : ((lostSecond adj i j).card : ℝ) < 2 := by nlinarith
    have hn : (lostSecond adj i j).card < 2 := by exact_mod_cast hr
    omega
  · simp only [ite_eq_right h]
    simp only [newHead, ite_eq_right h] at gain
    have hr : ((lostSecond adj i j).card : ℝ) < 1 := by nlinarith
    have hn : (lostSecond adj i j).card < 1 := by exact_mod_cast hr
    omega

end CH.CompromiseSmallIncoming

#print axioms CH.CompromiseSmallIncoming.low_weight_branches
#print axioms CH.CompromiseSmallIncoming.below_two_structure
#print axioms CH.CompromiseSmallIncoming.below_five_thirds_shape
#print axioms CH.CompromiseSmallIncoming.four_incoming_cycle
#print axioms CH.CompromiseSmallIncoming.low_head_lost_bound
