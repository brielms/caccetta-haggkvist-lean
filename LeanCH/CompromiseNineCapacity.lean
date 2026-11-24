module

public import LeanCH.CompromiseNineInside

set_option linter.style.header false

/-! Capacity bounds in the seven-element second neighbourhood. -/

open Finset CH.CompromiseSeven CH.CompromiseNineLocal
public section

namespace CH.CompromiseNineFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]
variable (H : Ambient adj) (f : Frame adj)

theorem budget_partition :
    f.goodBudget + (∑ x ∈ f.exceptional, f.omission x) = f.total := by
  dsimp [goodBudget, total]
  rw [← sum_union f.good_exceptional_disjoint, f.good_exceptional_union]

theorem budget_missed_good (a : V) (ha : a ∈ f.A) :
    (f.missing a ∩ f.good).card ≤ f.goodBudget := by
  have hm (g : V) (hg : g ∈ f.missing a ∩ f.good) : 1 ≤ f.omission g := by
    apply card_pos.mpr
    exact ⟨a, mem_sdiff.mpr ⟨ha, by
      simpa using (mem_sdiff.mp (mem_inter.mp hg).1).2⟩⟩
  have hs := sum_le_sum hm
  simp only [sum_const, smul_eq_mul, mul_one] at hs
  exact hs.trans (sum_le_sum_of_subset inter_subset_right)

theorem good_head_card (a : V) :
    (f.good \ f.missing a).card + (f.missing a ∩ f.good).card = f.good.card := by
  rw [inter_comm (f.missing a) f.good]
  exact card_sdiff_add_card_inter f.good (f.missing a)

theorem mem_good_head (a g : V) :
    g ∈ f.good \ f.missing a ↔ g ∈ f.good ∧ adj a g := by
  constructor
  · intro h
    refine ⟨(mem_sdiff.mp h).1, ?_⟩
    by_contra hn
    exact (mem_sdiff.mp h).2 (mem_sdiff.mpr ⟨f.good_sub (mem_sdiff.mp h).1, by simpa using hn⟩)
  · intro h
    exact mem_sdiff.mpr ⟨h.1, fun hh => (mem_sdiff.mp hh).2 (by simpa using h.2)⟩

include H

omit H in
theorem omission_exceptional (z : V) (hz : z ∈ f.exceptional) : 4 ≤ f.omission z := by
  have hzZ := f.exceptional_sub hz
  have hn := (mem_sdiff.mp hz).2
  simp only [good, mem_filter, hzZ, true_and] at hn
  omega

theorem budget_bound : f.goodBudget + 4 * f.exceptional.card ≤ 11 := by
  have hs := sum_le_sum (fun z hz => f.omission_exceptional z hz)
  simp only [sum_const, smul_eq_mul] at hs
  have := f.budget_partition
  have := f.total_le_eleven H
  omega

theorem zin_capacity (z : V) : (inN adj z ∩ f.Z).card ≤ 1 + f.omission z := by
  have hd : Disjoint (inN adj z ∩ f.A) (inN adj z ∩ f.Z) :=
    f.disj.mono inter_subset_right inter_subset_right
  have hc := card_le_card (union_subset
    (inter_subset_left : inN adj z ∩ f.A ⊆ inN adj z)
    (inter_subset_left : inN adj z ∩ f.Z ⊆ inN adj z))
  rw [card_union_of_disjoint hd] at hc
  have hb := H.cap z
  have hp := card_sdiff_add_card_inter f.A (inN adj z)
  rw [inter_comm, f.cardA] at hp
  change f.omission z + (inN adj z ∩ f.A).card = 9 at hp
  omega

theorem good_incoming_capacity :
    (∑ g ∈ f.good, (outN adj g ∩ f.good).card) +
      (∑ x ∈ f.exceptional, (outN adj x ∩ f.good).card) ≤
        f.good.card + f.goodBudget := by
  rw [← sum_union f.good_exceptional_disjoint, f.good_exceptional_union,
    double_count adj f.Z f.good]
  have hs := sum_le_sum (fun g (_hg : g ∈ f.good) => f.zin_capacity H g)
  simpa [sum_add_distrib, goodBudget] using hs

theorem good_outgoing_capacity :
    (∑ g ∈ f.good, f.zOut g) +
      (∑ x ∈ f.exceptional, (outN adj x ∩ f.good).card) ≤
        f.good.card * (1 + f.exceptional.card) + f.goodBudget := by
  have split (g : V) : f.zOut g = (outN adj g ∩ f.good).card +
      (outN adj g ∩ f.exceptional).card := by
    rw [← card_union_of_disjoint (f.good_exceptional_disjoint.mono
      inter_subset_right inter_subset_right), ← inter_union_distrib_left,
      f.good_exceptional_union]
    rfl
  have bound (g : V) (_hg : g ∈ f.good) :
      (outN adj g ∩ f.exceptional).card ≤ f.exceptional.card := card_le_card inter_subset_right
  have hb := sum_le_sum bound
  simp only [sum_const, smul_eq_mul] at hb
  have hi := f.good_incoming_capacity H
  simp_rw [split, sum_add_distrib]
  nlinarith

theorem good_small_head_bound (a : V) (k m : ℕ)
    (hmiss : ∀ g ∈ f.good ∩ f.missing a, m ≤ f.zOut g)
    (hnum : f.good.card * (1 + f.exceptional.card) + f.goodBudget <
      m * (f.missing a ∩ f.good).card + (k + 1) * (f.good \ f.missing a).card) :
    ∃ g ∈ f.good, adj a g ∧ f.zOut g ≤ k := by
  by_contra hn
  have hl (g : V) (hg : g ∈ f.good \ f.missing a) : k + 1 ≤ f.zOut g := by
    obtain ⟨hgg, hag⟩ := (f.mem_good_head a g).mp hg
    have hh : ¬ f.zOut g ≤ k := fun h => hn ⟨g, hgg, hag, h⟩
    omega
  have hs := sum_le_sum hl
  have ht := sum_le_sum hmiss
  simp only [sum_const, smul_eq_mul] at hs ht
  have hp : (∑ g ∈ f.good \ f.missing a, f.zOut g) +
      (∑ g ∈ f.good ∩ f.missing a, f.zOut g) = ∑ g ∈ f.good, f.zOut g := by
    rw [← sum_union (disjoint_left.mpr (fun _ h h' => (mem_sdiff.mp h).2 (mem_inter.mp h').2))]
    congr 1
    ext g
    simp only [mem_union, mem_sdiff, mem_inter]
    tauto
  have hc := f.good_outgoing_capacity H
  rw [inter_comm f.good (f.missing a)] at ht hp
  rw [Nat.mul_comm _ (k + 1)] at hs
  rw [Nat.mul_comm _ m] at ht
  have hadd := add_le_add hs ht
  rw [hp] at hadd
  omega

theorem good_small_head (hgood : ∀ g ∈ f.good, 2 ≤ f.zOut g)
    (a : V) (k : ℕ)
    (hnum : f.good.card * (1 + f.exceptional.card) + f.goodBudget <
      2 * (f.missing a ∩ f.good).card + (k + 1) * (f.good \ f.missing a).card) :
    ∃ g ∈ f.good, adj a g ∧ f.zOut g ≤ k :=
  f.good_small_head_bound H a k 2 (fun g hg => hgood g (mem_inter.mp hg).1) hnum

theorem zOut_le_six (z : V) (hz : z ∈ f.Z) : f.zOut z ≤ 6 := by
  have hs : insert z (outN adj z ∩ f.Z) ⊆ f.Z := insert_subset hz inter_subset_right
  have hc := card_le_card hs
  rw [card_insert_of_notMem (by simp [H.loopless]), f.cardZ] at hc
  change (outN adj z ∩ f.Z).card ≤ 6
  omega

theorem return_cap (z : V) (hz : z ∈ f.Z) (k : ℕ)
    (hk : ∀ h : ℕ, 1 ≤ h → 3 + h ≤ f.omission z + (h - 1) / 3 → h ≤ k) :
    f.aOut z ≤ k := by
  by_cases hp : 1 ≤ f.aOut z
  · exact hk _ hp (f.return_bound H z hz hp)
  · omega

theorem return_cap_four (z : V) (hz : z ∈ f.Z) (hd : f.omission z ≤ 4) : f.aOut z ≤ 1 :=
  f.return_cap H z hz 1 (by intros; omega)

theorem return_cap_five (z : V) (hz : z ∈ f.Z) (hd : f.omission z ≤ 5) : f.aOut z ≤ 2 :=
  f.return_cap H z hz 2 (by intros; omega)

theorem return_cap_six (z : V) (hz : z ∈ f.Z) (hd : f.omission z ≤ 6) : f.aOut z ≤ 4 :=
  f.return_cap H z hz 4 (by intros; omega)

theorem inside_full_missing (a : V) (ha : a ∈ f.A)
    (hreach : ∀ z ∈ f.missing a, z ∈ second adj a) :
    2 + f.extra a ≤ (f.inside a).card + (f.extra a + 1) / 3 := by
  have heq : f.seenMissing a = f.missing a := inter_eq_left.mpr (by
    intro z hz
    exact hreach z hz)
  have hp := f.inside_partition a
  rw [heq] at hp
  change (f.inside a).card = (second adj a ∩ f.A).card + f.extra a at hp
  have := f.internal_second_lower H a ha
  omega

end CH.CompromiseNineFrame.Frame

#print axioms CH.CompromiseNineFrame.Frame.good_outgoing_capacity
#print axioms CH.CompromiseNineFrame.Frame.good_small_head
