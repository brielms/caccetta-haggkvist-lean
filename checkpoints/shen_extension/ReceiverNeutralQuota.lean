import checkpoints.shen_extension.ReceiverRemoteBalance

namespace LeanCH.BR.BoundaryTightParentReach
open Finset BRq2 BRq3 BR45 BypassRepair

/-- The reverse graph on g's parents forces enough neutral labels. Only
the exceptional indegree budget and the marked row degree enter. -/
theorem neutral_floor {D H q t g b} (free : QFree D H q)
    (cut : 3≤q) (two : 2≤t) (gm : g∈H) (size : H.card=q*t+1)
    (short : (outN D H g).card+1=t) (live : (inN D H g).Nonempty)
    (columns : ∀a∈inN D H g,t≤(inN D H a).card+(if a=b then 1 else 0))
    (lower : ∀k,2≤k → k≤t → NoHost q k ∧ LoneRow.NoNearHost q k) :
    t≤(q-1)*(neutral D H g).card := by
  let o:=(neutral D H g).card
  change t≤(q-1)*o
  by_contra! small
  have twoO : 2*o≤(q-1)*o := Nat.mul_le_mul_right _ (by omega)
  let k:=t-o
  have cap : k+o=t := by dsimp [k]; omega
  obtain ⟨none,near⟩ := lower k (by omega) (by omega)
  have big := parent_order free cut gm live columns cap.le none near
  have part := partition_card free (by omega) gm
  change (inN D H g).card+(outN D H g).card+o+1=H.card at part
  have qp : q-1+1=q := by omega
  have step := congrArg (fun x=>x*o) qp
  have scale := congrArg (fun x=>q*x) cap
  simp only [Nat.add_mul,one_mul] at step
  simp only [Nat.mul_add] at scale
  omega

/-- At any viable extra column the neutral bound uses just the native
graph, the marked row, and the lower-quota laws. -/
theorem neutral_quota {D H q t g b} (free : QFree D H q)
    (cut : 3≤q) (two : 2≤t) (gm : g∈H) (size : H.card=q*t+1)
    (br : Compose.Boundary.BoundaryRegular q t) (short : (outN D H g).card+1=t)
    (other : ∀a∈H,a≠g → t≤(outN D H a).card)
    (fresh : b∈remote D H q t g) (off : D g b≠true)
    (lower : ∀k,2≤k → k≤t → NoHost q k ∧ LoneRow.NoNearHost q k) :
    t≤(q-1)*(neutral D H g).card := by
  obtain ⟨_,count,cols⟩ := fresh_profile free (by omega) gm size br short other fresh off
  have inc : tight D H t g⊆inN D H g := fun _ m=>mem_inN.mpr ⟨(mem_filter.mp m).1,(mem_filter.mp m).2.1⟩
  have live := card_le_card inc
  exact neutral_floor free cut two gm size short (card_pos.mp (by omega)) (fun a am=>
    (cols a (mem_inN.mp am).1 (fun eq=>loopfree free (by omega) gm (eq ▸ (mem_inN.mp am).2))).ge) lower

attribute [aesop safe forward (immediate := [free,cut,two,gm,size,short,live,columns,lower])
  (rule_sets := [CHGraphFamilies])] neutral_floor
#print axioms neutral_floor
#print axioms neutral_quota
end LeanCH.BR.BoundaryTightParentReach
