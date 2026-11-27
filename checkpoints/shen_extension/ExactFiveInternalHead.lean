import checkpoints.shen_extension.FiveCommonHeads
import checkpoints.shen_extension.VacantPoolBudget

namespace LeanCH.BR.TripleBank
open Finset

/-- At exact five, two nonadjacent inherited rows have a common head in L.
The absence of either mutual arc leaves two omissions in their internal union. -/
theorem exact_five_internal_head {L Y : Finset ℕ} {N : ℕ → Finset ℕ} {p q : ℕ}
    (pl : p ∈ L) (ql : q ∈ L) (pq : p≠q)
    (loopP : p ∉ N p) (loopQ : q ∉ N q) (noPQ : q ∉ N p) (noQP : p ∉ N q)
    (ys : Y.card ≤ L.card) (pf : L.card+2 ≤ (N p).card) (qf : L.card+2 ≤ (N q).card)
    (px : N p \ L ⊆ Y) (qx : N q \ L ⊆ Y) (five : ((N p \ L) ∩ (N q \ L)).card=5) :
    ∃ r∈L, r∈N p ∧ r∈N q := by
  let A := N p ∩ L
  let B := N q ∩ L
  have bound : A ∪ B ⊆ (L.erase p).erase q := by
    intro w wm
    rcases mem_union.mp wm with h | h
    · obtain ⟨n,l⟩ := mem_inter.mp h
      exact mem_erase.mpr ⟨fun eq => noPQ (eq ▸ n),mem_erase.mpr ⟨fun eq => loopP (eq ▸ n),l⟩⟩
    · obtain ⟨n,l⟩ := mem_inter.mp h
      exact mem_erase.mpr ⟨fun eq => loopQ (eq ▸ n),mem_erase.mpr ⟨fun eq => noQP (eq ▸ n),l⟩⟩
  have k := card_le_card bound
  have n := card_erase_add_one pl
  have m := card_erase_add_one (mem_erase.mpr ⟨pq.symm,ql⟩)
  have lim := (card_le_card (union_subset px qx)).trans ys
  have h := card_union_add_card_inter (N p \ L) (N q \ L)
  have i := card_union_add_card_inter A B
  have f := card_sdiff_add_card_inter (N p) L
  have g := card_sdiff_add_card_inter (N q) L
  change (N p \ L).card+A.card=(N p).card at f
  change (N q \ L).card+B.card=(N q).card at g
  obtain ⟨r,rm⟩ := card_pos.mp (by omega : 0<(A∩B).card)
  obtain ⟨a,b⟩ := mem_inter.mp rm
  exact ⟨r,(mem_inter.mp a).2,(mem_inter.mp a).1,(mem_inter.mp b).1⟩

open BRq2 BRq3 BR45

/-- The same common head gives return-path bounds at all five blockers. -/
theorem nonadjacent_five_pressure {D : CH.Digraph} {U L Y : Finset ℕ}
    {c a b d p q t : ℕ}
    (free : QFree D U 3) (cu : c ∈ U) (small : U.card ≤ 3*t) (none : BypassRepair.NoHost 3 t)
    (floor : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card)
    (clear : L ⊆ neutral D U (tightParents D U c t) c) (nb : ∀ l ∈ L, D l c ≠ true)
    (triple : tightParents D U c t = {a,b,d}) (ab : a ≠ b)
    (ad : D a d = true) (bd : D b d = true)
    (pl : p ∈ L) (ql : q ∈ L) (pq : p ≠ q) (cp : D c p = true) (cq : D c q = true)
    (ap : D a p ≠ true) (bq : D b q ≠ true)
    (fullP : t+1 ≤ (outN D U p).card) (fullQ : t+1 ≤ (outN D U q).card)
    (spare : ∀ w ∈ outN D U p ∪ outN D U q, t+1 ≤ (outN D U w).card)
    (five : ((outN D U p \ L) ∩ (outN D U q \ L)).card=5)
    (sat : L.card+1=t) (ys : Y.card≤L.card)
    (outside : ∀ l∈L, outN D U l \ L ⊆ Y) (dL : ∀ l∈L, D d l=true)
    (noPQ : D p q ≠ true) (noQP : D q p ≠ true) :
    ∃ r∈L, D p r=true ∧ D q r=true ∧
      ∀ w∈(outN D U p \ L) ∩ (outN D U q \ L),
        3 ≤ (outN D (U.erase c) r ∩ inN D (U.erase c) w).card + 2*(if D r w=true then 1 else 0) := by
  have loc {r} (rl : r∈L) := mem_erase.mp (mem_sdiff.mp (mem_filter.mp (clear rl)).1).1
  obtain ⟨r,rl,rp,rq⟩ := exact_five_internal_head (N:=outN D U) pl ql pq
    (fun m => loopfree free (by decide) (loc pl).2 (mem_outN.mp m).2)
    (fun m => loopfree free (by decide) (loc ql).2 (mem_outN.mp m).2)
    (fun m => noPQ (mem_outN.mp m).2) (fun m => noQP (mem_outN.mp m).2)
    ys (by omega) (by omega) (outside p pl) (outside q ql) five
  have pr := (mem_outN.mp rp).2
  have qr := (mem_outN.mp rq).2
  exact ⟨r,rl,pr,qr,fun _ wm => exact_five_common_row_budget free cu small none floor clear nb triple ab
    ad bd pl ql pq cp cq ap bq fullP fullQ spare wm five rl (dL r rl) pr qr⟩

#print axioms nonadjacent_five_pressure

#print axioms exact_five_internal_head
end LeanCH.BR.TripleBank
