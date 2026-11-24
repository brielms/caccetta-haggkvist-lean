module

public import LeanCH.CompromiseCertificateCharge
public import LeanCH.CompromiseSharedPaths

set_option linter.style.header false

/-! A weighted arc-minimal, vertex-deletion-minimal compromise obstruction
cannot already be bad at every vertex for the unit weighting. The two
notions of minimality must not be conflated with unit-weight minimality. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseDeletion CH.CompromiseCritical CH.CompromiseInverse
open CH.CompromisePerturbation CH.CompromiseArcMinimal CH.CompromiseLostArc
open CH.CompromiseSharedPaths CH.CompromiseCertificateCharge
public section

namespace CH.CompromiseUnitMinimal

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

theorem unit_surplus (v : V) :
    surplus adj (fun _ => 1) v = ((second adj v).card : ℝ) +
      ((inN adj v).card : ℝ) - 2 * ((outN adj v).card : ℝ) := by
  simp [surplus, secondWeight, inWeight, outWeight, mass]

theorem out_positive (rows : ∀ v, surplus adj (fun _ => 1) v ≤ -1) (v : V) :
    0 < (outN adj v).card := by
  have h := rows v
  rw [unit_surplus] at h
  by_contra hn
  have hz : (outN adj v).card = 0 := by omega
  rw [hz] at h
  have hs : (0 : ℝ) ≤ (second adj v).card := Nat.cast_nonneg _
  have hi : (0 : ℝ) ≤ (inN adj v).card := Nat.cast_nonneg _
  norm_num at h
  linarith

theorem in_positive (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u) (v : V) : 0 < (inN adj v).card := by
  by_contra hn
  have he : inN adj v = ∅ := card_eq_zero.mp (by omega)
  have na (u : V) : ¬ adj u v := by
    intro h
    have hh := (mem_inN adj v u).mpr h
    rw [he] at hh
    simp at hh
  have hc (u : V) : 0 ≤ coefficient adj u v := by
    simp only [coefficient, CH.CompromisePacking.capacity, ite_eq_right (na u), sub_zero]
    split_ifs <;> norm_num
  have hi := inverse_row (CH.CompromiseInverse.matrix adj) unit v v
  change col (coefficient adj) (fun u => Q adj v u) v = _ at hi
  simp only [ite_true] at hi
  have hn : 0 ≤ col (coefficient adj) (fun u => Q adj v u) v :=
    sum_nonneg (fun u _ => mul_nonneg (qn v u) (hc u))
  linarith

theorem out_at_least_two (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (rows : ∀ v, surplus adj (fun _ => 1) v ≤ -1)
    (ip : ∀ v, 0 < (inN adj v).card) (v : V) : 2 ≤ (outN adj v).card := by
  have op := out_positive adj rows
  by_contra hn
  have one : (outN adj v).card = 1 := by have := op v; omega
  obtain ⟨a, ha⟩ := card_eq_one.mp one
  have hva : adj v a := (mem_outN adj v a).mp (by rw [ha]; simp)
  obtain ⟨b, hb⟩ := card_pos.mp (op a)
  have hab : adj a b := (mem_outN adj a b).mp hb
  have hs : b ∈ second adj v := by
    apply (mem_second adj v b).mpr
    refine ⟨?_, ?_, a, hva, hab⟩
    · intro he
      subst b
      exact noDigon v a hva hab
    · intro hvb
      have he : b = a := by
        have hh := (mem_outN adj v b).mpr hvb
        simpa [ha] using hh
      subst b
      exact noDigon a a hab hab
  have sc : 0 < (second adj v).card := card_pos.mpr ⟨b, hs⟩
  have ic := ip v
  have sr : (1 : ℝ) ≤ (second adj v).card := by exact_mod_cast sc
  have ir : (1 : ℝ) ≤ (inN adj v).card := by exact_mod_cast ic
  have h := rows v
  rw [unit_surplus, one] at h
  norm_num at h
  linarith

theorem all_heads_internal (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (minimal : WeightedArcMinimal adj)
    (rows : ∀ v, surplus adj (fun _ => 1) v ≤ -1)
    (op : ∀ v, 2 ≤ (outN adj v).card) (i j : V) (edge : adj i j) :
    ∃ a ∈ outN adj i, adj a j := by
  have hj : j ∈ outN adj i := (mem_outN adj i j).mpr edge
  have ne : ((outN adj i).erase j).Nonempty := by
    apply card_pos.mp
    rw [card_erase_of_mem hj]
    have := op i
    omega
  obtain ⟨u, hu⟩ := ne
  obtain ⟨hne, hu⟩ := mem_erase.mp hu
  have gain := three_deficit_charge adj noDigon noTri minimal (fun _ => 1)
    (fun _ => by norm_num) 1 (by norm_num) rows i j u edge ((mem_outN adj i u).mp hu) hne
  have hs : j ∈ second (CH.ArcMinimal.eraseArc adj i j) i := by
    by_contra hn
    have ln : 0 ≤ mass (fun _ : V => (1 : ℝ)) (lostSecond adj i j) :=
      weight_nonneg _ (fun _ => by norm_num) _
    simp only [newHead, ite_eq_right hn] at gain
    linarith
  have noLoop (v : V) : ¬ adj v v := fun h => noDigon v v h h
  have hh := (new_head_iff adj noLoop i j edge).mp hs
  exact (mem_filter.mp hh).2

omit [DecidableEq V] in
theorem four_of_internal (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (i : V) (ne : (outN adj i).Nonempty)
    (heads : ∀ j ∈ outN adj i, ∃ a ∈ outN adj i, adj a j) :
    4 ≤ (outN adj i).card := by
  classical
  obtain ⟨a, ha⟩ := ne
  obtain ⟨b, hb, hba⟩ := heads a ha
  obtain ⟨c, hc, hcb⟩ := heads b hb
  obtain ⟨d, hd, hdc⟩ := heads c hc
  have ba : b ≠ a := by intro h; subst b; exact noDigon a a hba hba
  have cb : c ≠ b := by intro h; subst c; exact noDigon b b hcb hcb
  have ca : c ≠ a := by intro h; subst c; exact noDigon b a hba hcb
  have dc : d ≠ c := by intro h; subst d; exact noDigon c c hdc hdc
  have db : d ≠ b := by intro h; subst d; exact noDigon c b hcb hdc
  have da : d ≠ a := by intro h; subst d; exact noTri a c b hdc hcb hba
  have sub : ({a, b, c, d} : Finset V) ⊆ outN adj i := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have count : ({a, b, c, d} : Finset V).card = 4 := by
    simp [Ne.symm ba, Ne.symm cb, Ne.symm ca, Ne.symm dc, Ne.symm db, Ne.symm da]
  simpa [count] using card_le_card sub

theorem inverse_row_mass_le_one (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u)
    (rows : ∀ v, surplus adj (fun _ => 1) v ≤ -1) (v : V) :
    (∑ u, Q adj v u) ≤ 1 := by
  have he : payoff (CH.CompromiseInverse.matrix adj) (fun _ => 1) (fun u => Q adj v u) = -1 := by
    erw [payoff_transpose]
    simp only [Q, inverse_row (CH.CompromiseInverse.matrix adj) unit, one_mul]
    simp
  have h : payoff (CH.CompromiseInverse.matrix adj) (fun _ => 1) (fun u => Q adj v u) ≤
      -(∑ u, Q adj v u) := by
    change (∑ u, Q adj v u * row (coefficient adj) (fun _ => 1) u) ≤ _
    simp only [row_coefficient]
    calc
      _ ≤ ∑ u, Q adj v u * (-1) := sum_le_sum (fun u _ =>
        mul_le_mul_of_nonneg_left (rows u) (qn v u))
      _ = _ := by simp
  linarith

theorem indegree_at_most_three (qn : ∀ v u, 0 ≤ Q adj v u)
    (charge : ∀ i j, adj i j → 1 ≤ 3 * Q adj j i)
    (massBound : ∀ v, (∑ u, Q adj v u) ≤ 1) (v : V) : (inN adj v).card ≤ 3 := by
  have h := sum_le_sum (s := inN adj v)
    (fun u hu => charge u v ((mem_inN adj v u).mp hu))
  simp only [sum_const, nsmul_eq_mul, mul_one, ← mul_sum] at h
  have hs : (∑ u ∈ inN adj v, Q adj v u) ≤ ∑ u, Q adj v u :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun u _ _ => qn v u)
  have hr : ((inN adj v).card : ℝ) ≤ 3 := by linarith [massBound v]
  exact_mod_cast hr

/-- A unit counterweight cannot coexist with these two weighted
minimality inputs. This does not prove K* for arbitrary weighted graphs. -/
theorem no_unit_counterexample [Nonempty V]
    (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (rows : ∀ v, surplus adj (fun _ => 1) v ≤ -1) : False := by
  have nn : ∀ v : V, 0 ≤ (1 : ℝ) := fun _ => by norm_num
  have bad : ∀ v, surplus adj (fun _ => 1) v < 0 := fun v => lt_of_le_of_lt (rows v) (by norm_num)
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted (fun _ => 1) nn bad
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  have op := out_at_least_two adj noDigon rows (in_positive adj unit qn)
  have four (v : V) : 4 ≤ (outN adj v).card :=
    four_of_internal adj noDigon noTri v (card_pos.mp (by have := op v; omega))
      (fun j hj => all_heads_internal adj noDigon noTri minimal rows op v j
        ((mem_outN adj v j).mp hj))
  have three := indegree_at_most_three adj qn (arc_lower adj deleted minimal (fun _ => 1) nn bad)
    (inverse_row_mass_le_one adj unit qn rows)
  have lo := sum_le_sum (s := (univ : Finset V)) (fun v _ => four v)
  have hi := sum_le_sum (s := (univ : Finset V)) (fun v _ => three v)
  have eq := double_count adj univ univ
  simp only [inter_univ] at eq
  simp only [sum_const, card_univ, smul_eq_mul] at lo hi
  have pos := Fintype.card_pos (α := V)
  omega

/-- In particular these weighted minimality assumptions already force
a unit-weight compromise vertex, even though general K* stays open. -/
theorem compromise_unit [Nonempty V]
    (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj) :
    ∃ v, 2 * (outN adj v).card ≤ (second adj v).card + (inN adj v).card := by
  by_contra hn
  push Not at hn
  apply no_unit_counterexample adj noDigon noTri deleted minimal
  intro v
  have hi : (second adj v).card + (inN adj v).card + 1 ≤ 2 * (outN adj v).card := by
    have := hn v
    omega
  have hr : ((second adj v).card : ℝ) + ((inN adj v).card : ℝ) + 1 ≤
      2 * ((outN adj v).card : ℝ) := by exact_mod_cast hi
  rw [unit_surplus]
  linarith

end CH.CompromiseUnitMinimal

#print axioms CH.CompromiseUnitMinimal.all_heads_internal
#print axioms CH.CompromiseUnitMinimal.inverse_row_mass_le_one
#print axioms CH.CompromiseUnitMinimal.no_unit_counterexample
#print axioms CH.CompromiseUnitMinimal.compromise_unit
