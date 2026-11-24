import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ6SpillBanks_20261121

namespace LeanCH.BR.DotDegreeSevenQ6
open Finset BRq2 BRq3 BR45 BRsGen

theorem sevenSpill_of_keep {D : CH.Digraph} {V B T : Finset ℕ}
    (hf : QFree D V 6) (he : OutEq 7 D V)
    (hB : B⊆V) (hT : T⊆V) (cB : B.card=7) (cT : T.card=6)
    (sep : Disjoint B T) (keep : ∀ b∈B, outN D V b ⊆ B∪T) :
    SevenSpill D V B T := by
  classical
  have split b (hb : b∈B) :
      outN D V b = outN D B b ∪ outN D T b := by
    ext x
    constructor
    · intro hx
      obtain ⟨_, hx'⟩ := mem_outN.mp hx
      rcases mem_union.mp (keep b hb hx) with h|h
      · exact mem_union_left _ (mem_outN.mpr ⟨h,hx'⟩)
      · exact mem_union_right _ (mem_outN.mpr ⟨h,hx'⟩)
    · intro hx
      rcases mem_union.mp hx with h|h
      · exact mem_outN.mpr ⟨hB (mem_outN.mp h).1,(mem_outN.mp h).2⟩
      · exact mem_outN.mpr ⟨hT (mem_outN.mp h).1,(mem_outN.mp h).2⟩
  have cap b : (outN D T b).card ≤ 6 := by
    rw [←cT]
    exact card_le_card (fun _ hx => (mem_outN.mp hx).1)
  have mn : ∀ b∈B, 1≤(outN D B b).card := by
    intro b hb
    have h := card_union_le (outN D B b) (outN D T b)
    rw [←split b hb,he b (hB hb)] at h
    have hc := cap b
    omega
  have reg : OutEq 1 D B := (dt_reg (q:=6) (by decide)
    (ball_q_one 6 (by decide)) (hf.mono_set hB) mn (by simpa using cB)).1
  refine ⟨hB,hT,cB,cT,sep,reg,keep,?_⟩
  intro b hb t ht
  have h := card_union_le (outN D B b) (outN D T b)
  rw [←split b hb,he b (hB hb),reg b hb] at h
  have eq : outN D T b = T := eq_of_subset_of_card_le
    (fun _ hx => (mem_outN.mp hx).1) (by omega)
  exact (mem_outN.mp (eq ▸ ht)).2

theorem first_spill_of_ball_two14 {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 6) (he : OutEq 7 D V) (hu : u∈V)
    (c2 : (ball D V u 2).card=14) :
    SevenSpill D V ((ball D V u 1).erase u) (ball D V u 2 \ ball D V u 1) := by
  have c1 : (ball D V u 1).card=8 := by
    rw [card_B1 (hf.mono_bound (by decide : 4≤6)) hu,he u hu]
  have csub := card_sdiff_add_card_eq_card
    (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
  refine sevenSpill_of_keep hf he ((erase_subset u _).trans ball_subset)
    (sdiff_subset.trans ball_subset) ?_ (by omega) ?_ ?_
  · rw [card_erase_of_mem (self_mem_ball hu),c1]
  · exact disjoint_left.mpr (fun _ ha hb => (mem_sdiff.mp hb).2 (mem_of_mem_erase ha))
  · intro b hb x hx
    rw [←erase_ball_succ_eq_union (k:=1) hu]
    exact (mem_outN.mp (outN_prefix_erase_root hf hu (by decide : 1+1≤6)
      (mem_of_mem_erase hb) hx)).1

#print axioms sevenSpill_of_keep
#print axioms first_spill_of_ball_two14

end LeanCH.BR.DotDegreeSevenQ6

namespace LeanCH.BR.DotDegreeSevenQ6
open Finset BRq2 BRq3 BR45 BRsGen

theorem second_spill_of_no_return {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 6) (he : OutEq 7 D V) (hu : u∈V)
    (c2 : (ball D V u 2).card=15) (c3 : (ball D V u 3).card=21)
    (nr : ∀ b ∈ ball D V u 2 \ ball D V u 1,
          ∀ a ∈ (ball D V u 1).erase u, D b a ≠ true) :
    SevenSpill D V (ball D V u 2 \ ball D V u 1) (ball D V u 3 \ ball D V u 2) := by
  have c1 : (ball D V u 1).card=8 := by
    rw [card_B1 (hf.mono_bound (by decide : 4≤6)) hu,he u hu]
  have csub := card_sdiff_add_card_eq_card
    (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
  have csub' := card_sdiff_add_card_eq_card
    (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
  refine sevenSpill_of_keep hf he (sdiff_subset.trans ball_subset)
    (sdiff_subset.trans ball_subset) (by omega) (by omega) ?_ ?_
  · exact disjoint_left.mpr (fun _ hb hc => (mem_sdiff.mp hc).2 (mem_sdiff.mp hb).1)
  · intro b hb x hx
    have H := (mem_outN.mp (outN_prefix_erase_root hf hu (by decide : 2+1≤6)
      (mem_sdiff.mp hb).1 hx)).1
    rw [erase_ball_succ_eq_union (k:=2) hu] at H
    rcases mem_union.mp H with K | K
    · apply mem_union_left
      refine mem_sdiff.mpr ⟨mem_of_mem_erase K,?_⟩
      exact fun a => nr b hb x (mem_erase.mpr ⟨(mem_erase.mp K).1,a⟩) (mem_outN.mp hx).2
    · exact mem_union_right _ K

#print axioms second_spill_of_no_return
end LeanCH.BR.DotDegreeSevenQ6
