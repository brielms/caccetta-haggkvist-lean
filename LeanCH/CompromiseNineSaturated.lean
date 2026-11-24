module

public import LeanCH.CompromiseNineCapacity

set_option linter.style.header false

/-! Degree-nine local case: minimum out-degree two within Z. -/

open Finset CH.CompromiseSeven CH.CompromiseNineLocal
public section

namespace CH.CompromiseNineFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]
variable (H : Ambient adj) (f : Frame adj)
include H

theorem saturated_regular (hmin : ∀ z ∈ f.Z, 2 ≤ f.zOut z) :
    ∀ z ∈ f.Z, f.zOut z = 2 ∧ (inN adj z ∩ f.Z).card = 2 := by
  have small7 : LocalSmall adj := fun S hn hs => H.small S hn (by omega)
  have hout := rigid_seven adj H.loopless H.noDigon H.noTri small7 f.Z f.cardZ hmin
  have hin (z : V) (hz : z ∈ f.Z) : (inN adj z ∩ f.Z).card ≤ 2 := by
    have hb := CH.CompromiseNineLocal.local_degree_bound adj H.loopless H.noDigon
      H.noTri H.small f.Z 2 (by omega) (by rw [f.cardZ]; omega) hmin z hz
    rw [f.cardZ, hout z hz] at hb
    omega
  have heq : (∑ z ∈ f.Z, (inN adj z ∩ f.Z).card) = ∑ _z ∈ f.Z, 2 := by
    rw [← double_count adj f.Z f.Z]
    exact sum_congr rfl hout
  intro z hz
  exact ⟨hout z hz, (sum_eq_sum_iff_of_le hin).mp heq z hz⟩

theorem saturated_omission_pos (hmin : ∀ z ∈ f.Z, 2 ≤ f.zOut z)
    (z : V) (hz : z ∈ f.Z) : 1 ≤ f.omission z := by
  have hi := (f.saturated_regular H hmin z hz).2
  have hc := f.zin_capacity H z
  omega

theorem saturated_exceptional_le_one (hmin : ∀ z ∈ f.Z, 2 ≤ f.zOut z) :
    f.exceptional.card ≤ 1 := by
  have hg : f.good.card ≤ f.goodBudget := by
    have hs := sum_le_sum (fun g hg => f.saturated_omission_pos H hmin g (f.good_sub hg))
    simpa [goodBudget] using hs
  have hc := f.good_exceptional_card
  have hb := f.budget_bound H
  omega

theorem saturated_all_deficient (hmin : ∀ z ∈ f.Z, 2 ≤ f.zOut z) :
    ∀ a ∈ f.A, (inN adj a).card ≤ 8 := by
  have hgmin : ∀ g ∈ f.good, 2 ≤ f.zOut g := fun g hg => hmin g (f.good_sub hg)
  have hX := f.saturated_exceptional_le_one H hmin
  have hG : 6 ≤ f.good.card := by have := f.good_exceptional_card; omega
  intro a ha
  have hp := f.inside_ge_two H hgmin a ha
  by_cases hex : ∃ g ∈ f.good, adj a g
  · obtain ⟨g, hg, hag⟩ := hex
    have hz := (f.saturated_regular H hmin g (f.good_sub hg)).1
    have hc := f.head_deficit H a ha g hag 0 (by
      rw [f.good_aOut_zero H g hg, hz]
      omega)
    omega
  · have hGmiss : f.good ⊆ f.missing a := by
      intro g hg
      refine mem_sdiff.mpr ⟨f.good_sub hg, ?_⟩
      intro hag
      exact hex ⟨g, hg, by simpa using hag⟩
    have hpG : f.good.card ≤ (f.inside a).card := by
      apply card_le_card
      intro g hg
      exact mem_inter.mpr ⟨f.good_missing_reached H a ha g (mem_inter.mpr ⟨hGmiss hg, hg⟩),
        mem_union_right _ (f.good_sub hg)⟩
    have he := f.extra_le_six H a ha
    have hcZ := card_sdiff_add_card_inter f.Z (outN adj a)
    rw [f.cardZ, inter_comm] at hcZ
    change f.extra a + (outN adj a ∩ f.Z).card = 7 at hcZ
    obtain ⟨z, hz⟩ := card_pos.mp (show 0 < (outN adj a ∩ f.Z).card by omega)
    have haz : adj a z := by simpa using (mem_inter.mp hz).1
    have hzZ := (mem_inter.mp hz).2
    have hzG : z ∉ f.good := fun hh => hex ⟨z, hh, haz⟩
    have hd : f.omission z ≤ 5 := by
      have hsub : insert z f.good ⊆ f.Z := insert_subset hzZ f.good_sub
      have hs : (∑ g ∈ insert z f.good, f.omission g) ≤ f.total := sum_le_sum_of_subset hsub
      rw [sum_insert hzG] at hs
      have hgg : f.good.card ≤ ∑ g ∈ f.good, f.omission g := by
        have hh := sum_le_sum (fun g hg => f.saturated_omission_pos H hmin g (f.good_sub hg))
        simpa using hh
      have hb := f.total_le_eleven H
      omega
    have hr := f.return_cap_five H z hzZ hd
    have hq := (f.saturated_regular H hmin z hzZ).1
    have hh := f.head_deficit H a ha z haz 0 (by omega)
    omega

end CH.CompromiseNineFrame.Frame

#print axioms CH.CompromiseNineFrame.Frame.saturated_all_deficient
