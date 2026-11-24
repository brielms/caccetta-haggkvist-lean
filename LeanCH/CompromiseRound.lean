module

public import LeanCH.CompromiseWeighted

set_option linter.style.header false

/-!
Weighted geometric compromise for oriented graphs whose out-neighbourhoods
are intervals immediately following their tails in a cyclic order.
Incoming neighbourhoods need not be intervals. No CH or Seymour assumption
is used, and zero vertex weights are allowed.
-/

open Finset CH.CompromiseSeven CH.CompromiseWeighted
public section

namespace CH.CompromiseRound

section Capture

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (adj : V → V → Prop) [DecidableRel adj]

omit [DecidableEq V] in
/-- The report's two-average hypothesis gives simultaneous bounds at a minimum
of the majorant; no stationary distribution or positivity is needed. -/
theorem simultaneous_of_two_averages (o i s ψ : V → ℝ)
    (A B : V → V → ℝ)
    (hA : ∀ x, (∀ y, 0 ≤ A x y) ∧ ∑ y, A x y = 1)
    (hB : ∀ x, (∀ y, 0 ≤ B x y) ∧ ∑ y, B x y = 1)
    (majorant : ∀ x, o x ≤ ψ x)
    (captureA : ∀ x, (∑ y, A x y * ψ y) ≤ s x)
    (captureB : ∀ x, (∑ y, B x y * ψ y) ≤ i x) :
    ∃ v, o v ≤ i v ∧ o v ≤ s v := by
  obtain ⟨v, _, hmin⟩ := exists_min_image univ ψ univ_nonempty
  have average (K : V → V → ℝ)
      (hK : ∀ x, (∀ y, 0 ≤ K x y) ∧ ∑ y, K x y = 1) :
      ψ v ≤ ∑ y, K v y * ψ y := by
    calc
      ψ v = ∑ y, K v y * ψ v := by rw [← sum_mul, (hK v).2, one_mul]
      _ ≤ _ := sum_le_sum (fun y _ =>
        mul_le_mul_of_nonneg_left (hmin y (mem_univ y)) ((hK v).1 y))
  exact ⟨v, (majorant v).trans ((average B hB).trans (captureB v)),
    (majorant v).trans ((average A hA).trans (captureA v))⟩

/-- Two whole-neighbourhood captures give both inequalities at one vertex. -/
theorem simultaneous_of_two_captures (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (captures : ∀ v, 0 < outWeight adj w v →
      (∃ a, outN adj a ⊆ second adj v) ∧ (∃ b, outN adj b ⊆ inN adj v)) :
    ∃ v, outWeight adj w v ≤ inWeight adj w v ∧
      outWeight adj w v ≤ secondWeight adj w v := by
  obtain ⟨v, _, hmin⟩ := exists_min_image univ (outWeight adj w) univ_nonempty
  refine ⟨v, ?_⟩
  have ho : 0 ≤ outWeight adj w v := weight_nonneg w hw _
  have hi : 0 ≤ inWeight adj w v := weight_nonneg w hw _
  have hs : 0 ≤ secondWeight adj w v := weight_nonneg w hw _
  by_cases hp : 0 < outWeight adj w v
  · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := captures v hp
    have hsa := weight_mono w hw _ _ ha
    have hib := weight_mono w hw _ _ hb
    have hma := hmin a (mem_univ a)
    have hmb := hmin b (mem_univ b)
    change outWeight adj w a ≤ secondWeight adj w v at hsa
    change outWeight adj w b ≤ inWeight adj w v at hib
    have hoi : outWeight adj w v ≤ inWeight adj w v := hmb.trans hib
    have hos : outWeight adj w v ≤ secondWeight adj w v := hma.trans hsa
    exact ⟨hoi, hos⟩
  · have hz : outWeight adj w v = 0 := by linarith
    rw [hz]
    exact ⟨hi, hs⟩

theorem geometric_of_two_captures (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (captures : ∀ v, 0 < outWeight adj w v →
      (∃ a, outN adj a ⊆ second adj v) ∧ (∃ b, outN adj b ⊆ inN adj v)) :
    ∃ v, (outWeight adj w v) ^ 2 ≤ inWeight adj w v * secondWeight adj w v := by
  obtain ⟨v, hi, hs⟩ := simultaneous_of_two_captures adj w hw captures
  refine ⟨v, ?_⟩
  have ho : 0 ≤ outWeight adj w v := weight_nonneg w hw _
  have hin : 0 ≤ inWeight adj w v := weight_nonneg w hw _
  nlinarith [mul_le_mul hi hs ho hin]

end Capture

variable {n : ℕ}

/-- Clockwise distance in the fixed cyclic order on `Fin n`. -/
@[expose] def distance (u v : Fin n) : ℕ :=
  if u.val ≤ v.val then v.val - u.val else n + v.val - u.val

@[simp] theorem distance_self (u : Fin n) : distance u u = 0 := by
  simp [distance]

theorem distance_pos (u v : Fin n) : 0 < distance u v ↔ u ≠ v := by
  have hu := u.isLt
  have hv := v.isLt
  have he : u = v ↔ u.val = v.val := Fin.ext_iff
  unfold distance
  split_ifs <;> omega

theorem distance_lt (u v : Fin n) : distance u v < n := by
  have hu := u.isLt
  have hv := v.isLt
  unfold distance
  split_ifs <;> omega

theorem distance_pair (u v : Fin n) (hne : u ≠ v) :
    distance u v + distance v u = n := by
  have hu := u.isLt
  have hv := v.isLt
  have he : u.val ≠ v.val := fun h => hne (Fin.ext h)
  unfold distance
  split_ifs <;> omega

theorem distance_triangle (u v z : Fin n) :
    distance u v + distance v z = distance u z ∨
      distance u v + distance v z = n + distance u z := by
  have hu := u.isLt
  have hv := v.isLt
  have hz := z.isLt
  unfold distance
  split_ifs <;> omega

variable (adj : Fin n → Fin n → Prop) [DecidableRel adj]

/-- Every out-neighbourhood is a consecutive initial clockwise interval. -/
@[expose] def OutInterval : Prop := ∀ x y z,
  0 < distance x y → distance x y ≤ distance x z → adj x z → adj x y

theorem second_capture (interval : OutInterval adj)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (v : Fin n) (hn : (outN adj v).Nonempty) :
    ∃ a, adj v a ∧ outN adj a ⊆ second adj v := by
  obtain ⟨a, ha, hmax⟩ := exists_max_image (outN adj v) (distance v) hn
  have hva : adj v a := by simpa using ha
  have hne : v ≠ a := by
    intro he
    subst a
    exact noDigon v v hva hva
  refine ⟨a, hva, ?_⟩
  intro z hz
  have haz : adj a z := by simpa using hz
  have hza : a ≠ z := by
    intro he
    subst z
    exact noDigon a a haz haz
  refine (mem_second adj v z).mpr ⟨?_, ?_, a, hva, haz⟩
  · intro he
    subst z
    exact noDigon v a hva haz
  · intro hvz
    have hm := hmax z (by simpa using hvz)
    have hpaz := (distance_pos a z).mpr hza
    have hpair := distance_pair v a hne
    have htri := distance_triangle v a z
    have hap : 0 < distance a v := (distance_pos a v).mpr hne.symm
    have hle : distance a v ≤ distance a z := by omega
    exact noDigon v a hva (interval a v z hap hle haz)

/-- The closest non-in-neighbour before `v` captures the incoming interval.
Its existence follows from any out-neighbour of `v` and the no-digon property. -/
theorem incoming_capture (interval : OutInterval adj)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (v : Fin n) (hn : (outN adj v).Nonempty) :
    ∃ b, outN adj b ⊆ inN adj v := by
  let S := univ.filter (fun b => b ≠ v ∧ ¬ adj b v)
  have hS : S.Nonempty := by
    obtain ⟨a, ha⟩ := hn
    have hva : adj v a := by simpa using ha
    refine ⟨a, ?_⟩
    simp only [S, mem_filter, mem_univ, true_and]
    refine ⟨?_, noDigon v a hva⟩
    intro he
    subst a
    exact noDigon v v hva hva
  obtain ⟨b, hb, hmin⟩ := exists_min_image S (fun b => distance b v) hS
  have hb' : b ≠ v ∧ ¬ adj b v := by simpa [S] using hb
  refine ⟨b, ?_⟩
  intro z hz
  have hbz : adj b z := by simpa using hz
  have hp : 0 < distance b v := (distance_pos b v).mpr hb'.1
  have hlt : distance b z < distance b v := by
    by_contra h
    exact hb'.2 (interval b v z hp (by omega) hbz)
  have hzne : z ≠ v := by
    intro he
    subst z
    exact hb'.2 hbz
  have hbzne : b ≠ z := by
    intro he
    subst z
    exact noDigon b b hbz hbz
  have hbp := (distance_pos b z).mpr hbzne
  have htri := distance_triangle b z v
  have hbound := distance_lt z v
  have hclose : distance z v < distance b v := by omega
  have hzv : adj z v := by
    by_contra h
    have hzS : z ∈ S := by simp [S, hzne, h]
    have hm := hmin z hzS
    omega
  simpa using hzv

/-- The same vertex satisfies both weighted inequalities for this class. -/
theorem simultaneous_outInterval [NeZero n] (w : Fin n → ℝ) (hw : ∀ v, 0 ≤ w v)
    (interval : OutInterval adj) (noDigon : ∀ u v, adj u v → ¬ adj v u) :
    ∃ v, outWeight adj w v ≤ inWeight adj w v ∧
      outWeight adj w v ≤ secondWeight adj w v := by
  apply simultaneous_of_two_captures adj w hw
  intro v hp
  have hn : (outN adj v).Nonempty := by
    by_contra h
    have he := not_nonempty_iff_eq_empty.mp h
    simp [outWeight, mass, he] at hp
  obtain ⟨a, _, ha⟩ := second_capture adj interval noDigon v hn
  exact ⟨⟨a, ha⟩, incoming_capture adj interval noDigon v hn⟩

/-- Weighted geometric compromise for a circular out-interval orientation. -/
theorem geometric_outInterval [NeZero n] (w : Fin n → ℝ) (hw : ∀ v, 0 ≤ w v)
    (interval : OutInterval adj) (noDigon : ∀ u v, adj u v → ¬ adj v u) :
    ∃ v, (outWeight adj w v) ^ 2 ≤ inWeight adj w v * secondWeight adj w v := by
  obtain ⟨v, hi, hs⟩ := simultaneous_outInterval adj w hw interval noDigon
  refine ⟨v, ?_⟩
  have ho : 0 ≤ outWeight adj w v := weight_nonneg w hw _
  have hin : 0 ≤ inWeight adj w v := weight_nonneg w hw _
  nlinarith [mul_le_mul hi hs ho hin]

theorem compromise_outInterval [NeZero n] (w : Fin n → ℝ) (hw : ∀ v, 0 ≤ w v)
    (interval : OutInterval adj) (noDigon : ∀ u v, adj u v → ¬ adj v u) :
    ∃ v, 2 * outWeight adj w v ≤ inWeight adj w v + secondWeight adj w v := by
  obtain ⟨v, hi, hs⟩ := simultaneous_outInterval adj w hw interval noDigon
  refine ⟨v, ?_⟩
  linarith

/-- CH3 for the out-interval class, with arbitrary minimum out-degree. -/
theorem order_bound_outInterval [NeZero n] (R : ℕ)
    (interval : OutInterval adj) (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v z, adj u v → adj v z → ¬ adj z u)
    (minimum : ∀ v, R ≤ (outN adj v).card) : 3 * R + 1 ≤ n := by
  obtain ⟨v, hv⟩ := compromise_outInterval adj (fun _ => 1) (by intro; norm_num)
    interval noDigon
  have unit_mass (S : Finset (Fin n)) : mass (fun _ => (1 : ℝ)) S = S.card := by
    simp [mass]
  simp only [outWeight, inWeight, secondWeight, unit_mass] at hv
  have hv' : 2 * (outN adj v).card ≤ (inN adj v).card + (second adj v).card := by
    exact_mod_cast hv
  have loopless (u : Fin n) : ¬ adj u u := fun h => noDigon u u h h
  have hoi : Disjoint (outN adj v) (inN adj v) := by
    apply disjoint_left.mpr
    intro a ha hb
    exact noDigon v a (by simpa using ha) (by simpa using hb)
  have hos : Disjoint (outN adj v) (second adj v) := by
    apply disjoint_left.mpr
    intro a ha hs
    exact ((mem_second adj v a).mp hs).2.1 (by simpa using ha)
  have his : Disjoint (inN adj v) (second adj v) := by
    apply disjoint_left.mpr
    intro a ha hs
    obtain ⟨_, _, b, hvb, hba⟩ := (mem_second adj v a).mp hs
    exact noTri v b a hvb hba (by simpa using ha)
  have hvnot : v ∉ outN adj v ∪ inN adj v ∪ second adj v := by
    simp [loopless]
  have hc := card_le_card (subset_univ
    (insert v (outN adj v ∪ inN adj v ∪ second adj v)))
  rw [card_insert_of_notMem hvnot,
    card_union_of_disjoint (disjoint_union_left.mpr ⟨hos, his⟩),
    card_union_of_disjoint hoi, card_univ, Fintype.card_fin] at hc
  have hm := minimum v
  omega

end CH.CompromiseRound

#print axioms CH.CompromiseRound.simultaneous_of_two_captures
#print axioms CH.CompromiseRound.simultaneous_of_two_averages
#print axioms CH.CompromiseRound.geometric_of_two_captures
#print axioms CH.CompromiseRound.second_capture
#print axioms CH.CompromiseRound.incoming_capture
#print axioms CH.CompromiseRound.simultaneous_outInterval
#print axioms CH.CompromiseRound.geometric_outInterval
#print axioms CH.CompromiseRound.compromise_outInterval
#print axioms CH.CompromiseRound.order_bound_outInterval
