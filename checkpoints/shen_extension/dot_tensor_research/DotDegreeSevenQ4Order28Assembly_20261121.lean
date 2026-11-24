import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ4GuardPayment_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ4Order28Budget_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ4SameBank_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

theorem order28_of_guarded_local_selection {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 4) (ho : OutEq 7 D V) (hn : V.card=28)
    (localSelect : ∀ u∈V, (ball D V u 2).card=14 →
      ∃ P⊆V, P.card=2 ∧ ∀ c∈P, ∃ s a, GuardFrame D V c u s a) : False := by
  classical
  let L := V.filter (fun v => (ball D V v 2).card=14)
  let bank := SecondBank D V
  let K := L.image bank
  let roots (B : Finset ℕ) := L.filter (fun v => bank v=B)
  have partition : L=K.biUnion roots := by
    ext u
    constructor
    · intro hu
      exact mem_biUnion.mpr ⟨bank u,mem_image.mpr ⟨u,hu,rfl⟩,mem_filter.mpr ⟨hu,rfl⟩⟩
    · intro hu
      obtain ⟨_,_,h⟩ := mem_biUnion.mp hu
      exact (mem_filter.mp h).1
  have dis : (↑K : Set (Finset ℕ)).PairwiseDisjoint roots := by
    intro B _ C _ ne
    apply disjoint_left.mpr
    intro v b c
    exact ne (((mem_filter.mp b).2).symm.trans (mem_filter.mp c).2)
  have miss (B) (_ : B∈K) (v) (hv : v∈roots B) :
      (roots B).erase v ⊆ V \ (ball D V v 2 ∪ reverseBall D V v 2) := by
    intro x hx
    obtain ⟨ne,xr⟩ := mem_erase.mp hx
    have vx := (mem_filter.mp (mem_filter.mp hv).1).1
    have xx := (mem_filter.mp (mem_filter.mp xr).1).1
    have eq := ((mem_filter.mp hv).2).trans ((mem_filter.mp xr).2).symm
    refine mem_sdiff.mpr ⟨xx,?_⟩
    intro h
    rcases mem_union.mp h with h|h
    · exact same_bank_no_two_q4 hf ho vx xx ne.symm eq h
    · exact same_bank_no_two_q4 hf ho xx vx ne eq.symm (mem_filter.mp h).2
  have get (B) (hb : B∈K) : ∃ v∈L, bank v=B := mem_image.mp hb
  let r (B : Finset ℕ) : ℕ := if h : B∈K then Classical.choose (get B h) else 0
  have rr (B) (hb : B∈K) : r B∈L ∧ bank (r B)=B := by
    simpa only [r,dite_eq_left hb] using Classical.choose_spec (get B hb)
  have rinj : (↑K : Set (Finset ℕ)).InjOn r := by
    intro B hb C hc eq
    have h := (rr B hb).2
    rw [eq,(rr C hc).2] at h
    exact h.symm
  have E (B) (hb : B∈K) :
      ∃ P⊆V, P.card=2 ∧ ∀ c∈P, ∃ s a, GuardFrame D V c (r B) s a :=
    localSelect (r B) (mem_filter.mp (rr B hb).1).1 (mem_filter.mp (rr B hb).1).2
  let escorts (B : Finset ℕ) : Finset ℕ := if h : B∈K then Classical.choose (E B h) else ∅
  have Spec (B) (hb : B∈K) :
      escorts B⊆V ∧ (escorts B).card=2 ∧ ∀ c∈escorts B, ∃ s a, GuardFrame D V c (r B) s a := by
    simpa only [escorts,dite_eq_left hb] using Classical.choose_spec (E B hb)
  refine order28_guarded_bank_budget hf ho hn K roots escorts partition dis
    (fun B hb => (Spec B hb).1) (fun B hb => (Spec B hb).2.1) miss ?_
  intro c cv
  let T := K.filter (fun B => c∈escorts B)
  let J := T.image r
  have cardJ : J.card=T.card := card_image_of_injOn (rinj.mono (fun _ hm => (mem_filter.mp hm).1))
  have group (u) (hu : u∈J) : u∈L ∧ ∃ s a, GuardFrame D V c u s a := by
    obtain ⟨B,bh,rfl⟩ := mem_image.mp hu
    obtain ⟨bk,bp⟩ := mem_filter.mp bh
    exact ⟨(rr B bk).1,(Spec B bk).2.2 c bp⟩
  have sv (u) (hu : u∈J) : u∈V := (mem_filter.mp (group u hu).1).1
  have short (u) (hu : u∈J) : (ball D V u 2).card=14 := (mem_filter.mp (group u hu).1).2
  have binj : (↑J : Set ℕ).InjOn bank := by
    intro u hu v hv eq
    obtain ⟨B,bh,rfl⟩ := mem_image.mp hu
    obtain ⟨C,ch,rfl⟩ := mem_image.mp hv
    rw [(rr B (mem_filter.mp bh).1).2,(rr C (mem_filter.mp ch).1).2] at eq
    rw [eq]
  let s (u : ℕ) := if h : u∈J then Classical.choose (group u h).2 else 0
  let a (u : ℕ) := if h : u∈J then Classical.choose (Classical.choose_spec (group u h).2) else 0
  have frame (u) (hu : u∈J) : GuardFrame D V c u (s u) (a u) := by
    simpa only [s,a,dite_eq_left hu] using
      Classical.choose_spec (Classical.choose_spec (group u hu).2)
  have mark := q4_shared_marks_of_frames hf ho cv sv short binj frame
  have j7 : J.card≤7 := by
    have ci := card_image_of_injOn mark.sInj
    have sub : J.image s⊆outN D V c := by
      intro v hv
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
      exact mark.sMem i hi
    have q := card_le_card sub
    rw [ci,ho c cv] at q
    exact q
  change 14+T.card≤(ball D V c 2).card
  rw [←cardJ]
  by_cases zero : J.card=0
  · simpa only [zero,Nat.add_zero] using
      floor_two14 (by decide : 4≤4) hf (fun v hv => (ho v hv).ge) cv
  obtain ⟨u,hu⟩ := card_pos.mp (Nat.pos_of_ne_zero zero)
  have g := q4_guarded_frame_gain hf ho (sv u hu) (short u hu) (frame u hu)
  by_cases one : J.card=1
  · have b6 : (bank u).card=6 := by
      have st := card_sdiff_add_card_eq_card
        (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
      rw [card_B1 hf (sv u hu),ho u (sv u hu)] at st
      change (bank u).card+8=(ball D V u 2).card at st
      have := short u hu
      omega
    have q := q4_spill_at_least_six hf ho (B:=bank u)
      (fun _ h => ball_subset (mem_sdiff.mp h).1) b6
    change 6≤(spillQ4 D V (SecondBank D V u)).card at q
    omega
  by_cases eq : J.card=7
  · have q := q4_sharedEscort_all_seven hf ho cv mark eq
    omega
  · have q := q4_sharedEscort_thick_spill hf ho mark (by omega) (by omega) u hu
    omega

#print axioms order28_of_guarded_local_selection
end LeanCH.BR.DotDegreeSevenLow

