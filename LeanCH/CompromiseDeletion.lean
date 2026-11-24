module

public import LeanCH.CompromiseSubset
public import LeanCH.CompromiseFair

set_option linter.style.header false

/-! Exact vertex-deletion accounting. The good induced vertex is an explicit
hypothesis; no order-minimality, CH, or compromise conjecture is assumed
silently. Retained second neighbours lost through deleted middles are kept. -/

open Finset CH.CompromiseSeven CH.CompromiseWeighted CH.CompromiseSubset
open CH.CompromiseFair
public section

namespace CH.CompromiseDeletion

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def surplus (w : V → ℝ) (v : V) : ℝ :=
  secondWeight adj w v + inWeight adj w v - 2 * outWeight adj w v

@[expose] def localSurplus (w : V → ℝ) (S : Finset V) (v : V) : ℝ :=
  mass w (localSecond adj S v) + mass w (inN adj v ∩ S) -
    2 * mass w (outN adj v ∩ S)

@[expose] def lost (S : Finset V) (v : V) : Finset V :=
  (second adj v ∩ S) \ localSecond adj S v

theorem localSecond_subset (S : Finset V) (v : V) :
    localSecond adj S v ⊆ second adj v ∩ S := by
  intro z hz
  obtain ⟨hzS, hne, hnon, a, _, hva, haz⟩ := mem_filter.mp hz
  exact mem_inter.mpr ⟨(mem_second adj v z).mpr ⟨hne, hnon, a, hva, haz⟩, hzS⟩

/-- A lost retained endpoint has a path through the deleted set, and no
two-step path with a retained middle. -/
theorem mem_lost (S : Finset V) (v z : V) :
    z ∈ lost adj S v ↔ z ∈ S ∧ z ≠ v ∧ ¬ adj v z ∧
      (∃ a, a ∉ S ∧ adj v a ∧ adj a z) ∧
      (∀ a ∈ S, ¬ (adj v a ∧ adj a z)) := by
  simp only [lost, mem_sdiff, mem_inter, mem_second, localSecond, mem_filter]
  constructor
  · rintro ⟨⟨⟨hne, hnon, a, hva, haz⟩, hzS⟩, hnot⟩
    have hn (b : V) (hb : b ∈ S) : ¬ (adj v b ∧ adj b z) := by
      rintro ⟨hvb, hbz⟩
      exact hnot ⟨hzS, hne, hnon, b, hb, hvb, hbz⟩
    exact ⟨hzS, hne, hnon, ⟨a, fun ha => hn a ha ⟨hva, haz⟩, hva, haz⟩, hn⟩
  · rintro ⟨hzS, hne, hnon, ⟨a, _, hva, haz⟩, hn⟩
    refine ⟨⟨⟨hne, hnon, a, hva, haz⟩, hzS⟩, ?_⟩
    rintro ⟨_, _, _, b, hb, hvb, hbz⟩
    exact hn b hb ⟨hvb, hbz⟩

theorem second_mass_split (w : V → ℝ) (S : Finset V) (v : V) :
    mass w (localSecond adj S v) + mass w (lost adj S v) +
      mass w (second adj v \ S) = secondWeight adj w v := by
  have h1 := sum_sdiff (f := w) (localSecond_subset adj S v)
  have h2 := sum_inter_add_sum_sdiff (second adj v) S w
  change mass w (lost adj S v) + mass w (localSecond adj S v) =
    mass w (second adj v ∩ S) at h1
  change mass w (second adj v ∩ S) + mass w (second adj v \ S) =
    secondWeight adj w v at h2
  linarith

theorem second_card_split (S : Finset V) (v : V) :
    (localSecond adj S v).card + (lost adj S v).card +
      (second adj v \ S).card = (second adj v).card := by
  have h1 := card_sdiff_add_card_eq_card (localSecond_subset adj S v)
  have h2 := card_sdiff_add_card_inter (second adj v) S
  change (lost adj S v).card + (localSecond adj S v).card =
    (second adj v ∩ S).card at h1
  omega

/-- The exact identity includes both the incoming boundary and lost retained
second neighbours. It holds for arbitrary real weights. -/
theorem deletion_identity (w : V → ℝ) (S : Finset V) (v : V) :
    surplus adj w v + 2 * mass w (outN adj v \ S) =
      localSurplus adj w S v + mass w (inN adj v \ S) +
        mass w (second adj v \ S) + mass w (lost adj S v) := by
  have ho := sum_inter_add_sum_sdiff (outN adj v) S w
  have hi := sum_inter_add_sum_sdiff (inN adj v) S w
  have hs := second_mass_split adj w S v
  change mass w (outN adj v ∩ S) + mass w (outN adj v \ S) = outWeight adj w v at ho
  change mass w (inN adj v ∩ S) + mass w (inN adj v \ S) = inWeight adj w v at hi
  dsimp [surplus, localSurplus]
  linarith

theorem deletion_strict (w : V → ℝ) (S : Finset V) (v : V)
    (bad : surplus adj w v < 0) :
    localSurplus adj w S v + mass w (inN adj v \ S) +
      mass w (second adj v \ S) + mass w (lost adj S v) <
        2 * mass w (outN adj v \ S) := by
  have h := deletion_identity adj w S v
  linarith

/-- The report's set inequality, strengthened by the lost-endpoint term. -/
theorem unit_deletion_bound (S : Finset V) (v : V)
    (bad : (second adj v).card + (inN adj v).card < 2 * (outN adj v).card)
    (good : 2 * (outN adj v ∩ S).card ≤
      (localSecond adj S v).card + (inN adj v ∩ S).card) :
    1 + (inN adj v \ S).card + (second adj v \ S).card +
      (lost adj S v).card ≤ 2 * (outN adj v \ S).card := by
  have ho := card_sdiff_add_card_inter (outN adj v) S
  have hi := card_sdiff_add_card_inter (inN adj v) S
  have hs := second_card_split adj S v
  omega

@[expose] def deficit (v : V) : ℕ :=
  2 * (outN adj v).card - ((second adj v).card + (inN adj v).card)

/-- Deleting one vertex supplies an incoming witness with deficit one or two;
the deficit and lost retained endpoints together cost at most two. -/
theorem singleton_witness
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (bad : ∀ v, (second adj v).card + (inN adj v).card < 2 * (outN adj v).card)
    (x : V)
    (inducedGood : ∃ a ∈ univ.erase x,
      2 * (outN adj a ∩ univ.erase x).card ≤
        (localSecond adj (univ.erase x) a).card + (inN adj a ∩ univ.erase x).card) :
    ∃ a, a ≠ x ∧ adj a x ∧ 1 ≤ deficit adj a ∧
      deficit adj a + (lost adj (univ.erase x) a).card ≤ 2 := by
  obtain ⟨a, ha, hg⟩ := inducedGood
  have hax : a ≠ x := (mem_erase.mp ha).1
  have hb := unit_deletion_bound adj (univ.erase x) a (bad a) hg
  have hx : adj a x := by
    by_contra h
    have he : outN adj a \ univ.erase x = ∅ := by
      ext z
      simp only [mem_sdiff, mem_outN, mem_erase, mem_univ, and_true, not_ne_iff,
        notMem_empty, iff_false]
      rintro ⟨hz, hzx⟩
      subst z
      exact h hz
    rw [he, card_empty] at hb
    omega
  have ho : outN adj a \ univ.erase x = {x} := by
    ext z
    simp only [mem_sdiff, mem_outN, mem_erase, mem_univ, and_true, not_ne_iff,
      mem_singleton]
    constructor
    · exact fun h => h.2
    · intro he
      subst z
      exact ⟨hx, rfl⟩
  have hi : inN adj a \ univ.erase x = ∅ := by
    ext z
    simp only [mem_sdiff, mem_inN, mem_erase, mem_univ, and_true, not_ne_iff,
      notMem_empty, iff_false]
    rintro ⟨hz, hzx⟩
    subst z
    exact noDigon a x hx hz
  have hs : second adj a \ univ.erase x = ∅ := by
    ext z
    simp only [mem_sdiff, mem_erase, mem_univ, and_true, not_ne_iff,
      notMem_empty, iff_false]
    rintro ⟨hz, hzx⟩
    subst z
    exact ((mem_second adj a x).mp hz).2.1 hx
  have hoc := card_sdiff_add_card_inter (outN adj a) (univ.erase x)
  have hic := card_sdiff_add_card_inter (inN adj a) (univ.erase x)
  have hsc := second_card_split adj (univ.erase x) a
  rw [ho, card_singleton] at hoc
  rw [hi, card_empty] at hic
  rw [hs, card_empty] at hsc
  have hbad := bad a
  refine ⟨a, hax, hx, ?_, ?_⟩ <;> dsimp [deficit] <;> omega

@[expose] def slack (p : V → ℝ) (u : V) : ℝ :=
  mass p (outN adj u) + mass p (secondIn adj u) - 2 * mass p (inN adj u)

@[expose] def localSlack (p : V → ℝ) (S : Finset V) (u : V) : ℝ :=
  mass p (outN adj u ∩ S) + mass p (restrictedSecondIn adj S u) -
    2 * mass p (inN adj u ∩ S)

@[expose] def gainedIn (S : Finset V) (u : V) : Finset V :=
  (secondIn adj u ∩ S) \ restrictedSecondIn adj S u

theorem restrictedSecondIn_subset_inter (S : Finset V) (u : V) :
    restrictedSecondIn adj S u ⊆ secondIn adj u ∩ S := by
  intro v hv
  exact mem_inter.mpr ⟨restrictedSecondIn_subset adj S u hv, (mem_filter.mp hv).1⟩

/-- The exact gain of a zero-extended induced certificate at a retained row. -/
theorem fair_deletion_identity (p : V → ℝ) (S : Finset V)
    (support : ∀ v, v ∉ S → p v = 0) (u : V) :
    slack adj p u = localSlack adj p S u + mass p (gainedIn adj S u) := by
  have h := sum_sdiff (f := p) (restrictedSecondIn_subset_inter adj S u)
  change mass p (gainedIn adj S u) + mass p (restrictedSecondIn adj S u) =
    mass p (secondIn adj u ∩ S) at h
  rw [mass_inter_support p S _ support] at h
  dsimp [slack, localSlack]
  rw [mass_inter_support p S _ support, mass_inter_support p S _ support]
  linarith

/-- The lost endpoints and gained dual predecessors are the same pairs,
viewed in opposite coordinates. -/
theorem lost_gained_transpose (S : Finset V) (v u : V) (hv : v ∈ S) (hu : u ∈ S) :
    u ∈ lost adj S v ↔ v ∈ gainedIn adj S u := by
  simp only [lost, gainedIn, mem_sdiff, mem_inter, mem_second, mem_secondIn,
    localSecond, restrictedSecondIn, mem_filter, hv, hu, and_true, true_and]
  constructor
  · rintro ⟨⟨hne, hnon, hp⟩, hn⟩
    refine ⟨⟨hne.symm, hnon, hp⟩, ?_⟩
    rintro ⟨_, _, hp'⟩
    exact hn ⟨hne, hnon, hp'⟩
  · rintro ⟨⟨hne, hnon, hp⟩, hn⟩
    refine ⟨⟨hne.symm, hnon, hp⟩, ?_⟩
    rintro ⟨_, _, hp'⟩
    exact hn ⟨hne, hnon, hp'⟩

theorem gained_singleton_edges (x u v : V)
    (hv : v ∈ gainedIn adj (univ.erase x) u) : adj v x ∧ adj x u := by
  obtain ⟨hpair, hnot⟩ := mem_sdiff.mp hv
  obtain ⟨hsecond, hvS⟩ := mem_inter.mp hpair
  obtain ⟨hne, hnon, a, hva, hau⟩ := (mem_secondIn adj u v).mp hsecond
  have hax : a = x := by
    by_contra h
    apply hnot
    exact mem_filter.mpr ⟨hvS, hne, hnon, a, by simp [h], hva, hau⟩
  subst a
  exact ⟨hva, hau⟩

theorem gained_singleton_empty (x u : V) (h : ¬ adj x u) :
    gainedIn adj (univ.erase x) u = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro v hv
  exact h (gained_singleton_edges adj x u v hv).2

/-- Exact weighted double counting of the lost/gained retained pairs. -/
theorem lost_gained_mass (p w : V → ℝ) (S : Finset V) :
    ∑ v ∈ S, p v * mass w (lost adj S v) =
      ∑ u ∈ S, w u * mass p (gainedIn adj S u) := by
  have hl (v : V) (hv : v ∈ S) :
      mass w (lost adj S v) = ∑ u ∈ S, if v ∈ gainedIn adj S u then w u else 0 := by
    have he : lost adj S v = S.filter (fun u => v ∈ gainedIn adj S u) := by
      ext u
      constructor
      · intro h
        have hu : u ∈ S := (mem_inter.mp (mem_sdiff.mp h).1).2
        exact mem_filter.mpr ⟨hu, (lost_gained_transpose adj S v u hv hu).mp h⟩
      · intro h
        obtain ⟨hu, hh⟩ := mem_filter.mp h
        exact (lost_gained_transpose adj S v u hv hu).mpr hh
    simp [mass, he, sum_filter]
  have hr (u : V) : mass p (gainedIn adj S u) =
      ∑ v ∈ S, if v ∈ gainedIn adj S u then p v else 0 := by
    have he : S.filter (fun v => v ∈ gainedIn adj S u) = gainedIn adj S u := by
      ext v
      simp only [gainedIn, mem_filter, mem_sdiff, mem_inter]
      tauto
    rw [← sum_filter, he]
    rfl
  calc
    _ = ∑ v ∈ S, ∑ u ∈ S, if v ∈ gainedIn adj S u then p v * w u else 0 := by
      apply sum_congr rfl
      intro v hv
      rw [hl v hv, mul_sum]
      apply sum_congr rfl
      intro u _
      split_ifs <;> simp
    _ = ∑ u ∈ S, ∑ v ∈ S, if v ∈ gainedIn adj S u then p v * w u else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro u _
      rw [hr u, mul_sum]
      apply sum_congr rfl
      intro v _
      split_ifs <;> simp [mul_comm]

theorem surplus_slack_pairing (p w : V → ℝ) :
    ∑ v, p v * surplus adj w v = ∑ u, w u * slack adj p u := by
  have ho := weighted_double_count adj p w
  have hi := weighted_double_count adj w p
  have hs := second_double_count adj p w
  change (∑ v, p v * outWeight adj w v) = ∑ u, w u * mass p (inN adj u) at ho
  change (∑ u, w u * mass p (outN adj u)) = ∑ v, p v * inWeight adj w v at hi
  have hleft : (∑ v, p v * surplus adj w v) =
      (∑ v, p v * secondWeight adj w v) + (∑ v, p v * inWeight adj w v) -
        2 * ∑ v, p v * outWeight adj w v := by
    simp only [surplus, mul_sub, mul_add, sum_sub_distrib, sum_add_distrib, mul_sum]
    congr 1
    apply sum_congr rfl
    intro v _
    ring
  have hright : (∑ u, w u * slack adj p u) =
      (∑ u, w u * mass p (outN adj u)) + (∑ u, w u * mass p (secondIn adj u)) -
        2 * ∑ u, w u * mass p (inN adj u) := by
    simp only [slack, mul_sub, mul_add, sum_sub_distrib, sum_add_distrib, mul_sum]
    congr 1
    apply sum_congr rfl
    intro u _
    ring
  rw [hleft, hright, ho, ← hi, hs]
  ring

/-- A hypothetical strict counterweight forces the omitted row of every
induced fair certificate to pay for all retained slack and regained pairs. -/
theorem singleton_fair_budget (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (bad : ∀ v, surplus adj w v < 0) (x : V) (p : V → ℝ)
    (hp : FairOn adj (univ.erase x) p) :
    0 < w x ∧ slack adj p x < 0 ∧
      (∑ u ∈ univ.erase x, w u * localSlack adj p (univ.erase x) u) +
        (∑ v ∈ univ.erase x, p v * mass w (lost adj (univ.erase x) v)) <
          w x * (-slack adj p x) := by
  have total : (∑ v, p v * surplus adj w v) < 0 := by
    have hle (v : V) : p v * surplus adj w v ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (hp.1 v) (bad v).le
    obtain ⟨v, _, hv⟩ := hp.2.2.1
    have hs := sum_lt_sum (s := (univ : Finset V)) (g := fun _ => (0 : ℝ))
      (fun v _ => hle v) ⟨v, mem_univ v, mul_neg_of_pos_of_neg hv (bad v)⟩
    simpa using hs
  rw [surplus_slack_pairing adj p w] at total
  have split := sum_erase_add (univ : Finset V) (fun u => w u * slack adj p u) (mem_univ x)
  have kept : (∑ u ∈ univ.erase x, w u * slack adj p u) =
      (∑ u ∈ univ.erase x, w u * localSlack adj p (univ.erase x) u) +
        ∑ v ∈ univ.erase x, p v * mass w (lost adj (univ.erase x) v) := by
    rw [lost_gained_mass adj p w]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro u _
    rw [fair_deletion_identity adj p (univ.erase x) hp.2.1 u]
    ring
  have nonneg : 0 ≤ ∑ u ∈ univ.erase x, w u * slack adj p u := by
    apply sum_nonneg
    intro u hu
    have hs := retained_row adj (univ.erase x) p hp u hu
    apply mul_nonneg (hw u)
    dsimp [slack]
    linarith
  have product : w x * slack adj p x < 0 := by linarith
  have wx : 0 < w x := by
    by_contra h
    have he : w x = 0 := by linarith [hw x]
    simp [he] at product
  have sx : slack adj p x < 0 := by
    by_contra h
    have hz : 0 ≤ w x * slack adj p x := mul_nonneg (hw x) (by linarith)
    linarith
  refine ⟨wx, sx, ?_⟩
  rw [kept] at split
  nlinarith

end CH.CompromiseDeletion

#print axioms CH.CompromiseDeletion.deletion_identity
#print axioms CH.CompromiseDeletion.unit_deletion_bound
#print axioms CH.CompromiseDeletion.singleton_witness
#print axioms CH.CompromiseDeletion.fair_deletion_identity
#print axioms CH.CompromiseDeletion.lost_gained_transpose
#print axioms CH.CompromiseDeletion.gained_singleton_empty
#print axioms CH.CompromiseDeletion.lost_gained_mass
#print axioms CH.CompromiseDeletion.singleton_fair_budget
