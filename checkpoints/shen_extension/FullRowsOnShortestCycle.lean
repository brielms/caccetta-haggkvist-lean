import checkpoints.shen_extension.ShellProfileCapacity
import LeanCH.BR.BRRichMissGeometry

namespace LeanCH.BR.FullRowsOnShortestCycle
open Finset BRq2 BRq3 BR45 BRsGen

/-- At most three full rows fit on a carrier of size at most q+d whose
remaining labels cannot contain a cycle. A shortest cycle meets a full
row, and that row must use every outside label. An outside sink pins the
two possible cycle parents. At most one more full row fits outside. -/
theorem at_most_three {D W H q d} (free : QFree D W q) (hq : 2≤q)
    (sub : H⊆W) (positive : ∀x∈W,1≤(outN D W x).card)
    (degree : ∀x∈H,d≤(outN D W x).card) (dpos : 2≤d) (fit : d≤q+1)
    (outside : (W\H).card≤q) (capacity : W.card≤q+d) : H.card≤3 := by
  classical
  by_contra! large
  have n := card_pos.mp (show 0<H.card by omega)
  obtain ⟨p,C,qp,_,cw,cs,one⟩ := exists_minimal_cycle_support (by omega) free positive (n.mono sub)
  let A := W \ C
  let P := C∩H
  have pc : P.Nonempty := by
    by_contra no
    have kept : C⊆W\H := fun x xc=>mem_sdiff.mpr ⟨cw xc,fun xh=>no ⟨x,mem_inter.mpr ⟨xc,xh⟩⟩⟩
    have lo := card_le_card kept
    omega
  obtain ⟨u,um⟩ := pc
  have uc := (mem_inter.mp um).1
  have uh := (mem_inter.mp um).2
  have cover : C∪A=W := union_sdiff_of_subset cw
  have apart : Disjoint C A := disjoint_sdiff
  have partition (x) : (outN D C x).card+(outN D A x).card=(outN D W x).card := by
    rw [←card_outN_union apart,cover]
  have ex := card_sdiff_add_card_eq_card cw
  change A.card+C.card=W.card at ex
  have cut := partition u
  rw [one u uc] at cut
  have deg := degree u uh
  have lim := card_le_card (outN_subset : outN D A u⊆A)
  have exactC : C.card=q+1 := by omega
  have exactA : A.card+1=d := by omega
  have hit x (xp : x∈P) : A⊆outN D W x := by
    have ⟨xc,xh⟩ := mem_inter.mp xp
    have split := partition x
    rw [one x xc] at split
    have price := degree x xh
    have eq : outN D A x=A := eq_of_subset_of_card_le outN_subset (by omega)
    exact fun a am=>(outN_mono (sdiff_subset (s:=W) (t:=C)) x) (eq.symm ▸ am)
  obtain ⟨s,sa,stop⟩ := exists_sink (free.mono_set (show A⊆W from sdiff_subset))
    (card_pos.mp (by omega)) (by omega)
  have sw : s∈W := (mem_sdiff.mp sa).1
  obtain ⟨c,cm⟩ := card_pos.mp (positive s sw)
  have cc : c∈C := by
    by_contra off
    exact stop c (mem_sdiff.mpr ⟨outN_subset cm,off⟩) (mem_outN.mp cm).2
  let B := ball D C c (q-2)
  have bv : B⊆C := ball_subset
  have seen := ball_one_growth (free.mono_set cw) (fun v vm=>(one v vm).ge) cc (q-2) (by omega)
  change q-2+1≤B.card at seen
  have dis : Disjoint P B := by
    apply disjoint_left.mpr
    intro x xp xb
    obtain ⟨_,k,time,path⟩ := mem_ball.mp xb
    exact free c _ (by omega) (by omega)
      (((path.mono cw).snoc sw (mem_outN.mp (hit x xp sa)).2).snoc (cw cc) (mem_outN.mp cm).2)
  have used := card_le_card (union_subset (inter_subset_left : P⊆C) bv)
  rw [card_union_of_disjoint dis] at used
  have front : P.card≤2 := by omega
  obtain ⟨v,vm⟩ := card_pos.mp (by rw [one u uc]; decide : 0<(outN D C u).card)
  obtain ⟨w,wm⟩ := card_pos.mp (by rw [one v (outN_subset vm)]; decide : 0<(outN D C v).card)
  have allOther x (xa : x∈H\C) : outN D A x=A.erase x := by
    obtain ⟨xh,off⟩ := mem_sdiff.mp xa
    have am : x∈A := mem_sdiff.mpr ⟨sub xh,off⟩
    have less := WeightedSD.cycle_two_step_detour_heads hq free cw exactC one uc (outN_subset vm)
      (outN_subset wm) (sub xh) (mem_outN.mp vm).2 (mem_outN.mp wm).2 (mem_outN.mp (hit u um am)).2
    have pair := (card_le_card less).trans (card_insert_le v {w})
    rw [card_singleton] at pair
    have split := partition x
    have demand := degree x xh
    apply eq_of_subset_of_card_le
    · exact fun a aa=>mem_erase.mpr ⟨fun e=>loopfree free (by omega) (sub xh) (e ▸ (mem_outN.mp aa).2),outN_subset aa⟩
    · rw [card_erase_of_mem am]; omega
  have rest := card_sdiff_add_card_inter H C
  rw [inter_comm H C] at rest
  change (H\C).card+P.card=H.card at rest
  obtain ⟨x,xh,y,yh,ne⟩ := one_lt_card.mp (by omega : 1<(H\C).card)
  have ax : x∈A := mem_sdiff.mpr ⟨sub (mem_sdiff.mp xh).1,(mem_sdiff.mp xh).2⟩
  have ay : y∈A := mem_sdiff.mpr ⟨sub (mem_sdiff.mp yh).1,(mem_sdiff.mp yh).2⟩
  have xy := (mem_outN.mp ((allOther x xh).symm ▸ mem_erase.mpr ⟨ne.symm,ay⟩ : y∈outN D A x)).2
  have yx := (mem_outN.mp ((allOther y yh).symm ▸ mem_erase.mpr ⟨ne,ax⟩ : x∈outN D A y)).2
  exact free x 2 (by decide) hq (.step (sub (mem_sdiff.mp yh).1) xy (.step (sub (mem_sdiff.mp xh).1) yx (.refl x)))

attribute [aesop safe forward (immediate := [free,hq,sub,positive,degree,dpos,fit,outside,capacity])
  (rule_sets := [CHGraphFamilies])] at_most_three
#print axioms at_most_three
end LeanCH.BR.FullRowsOnShortestCycle
