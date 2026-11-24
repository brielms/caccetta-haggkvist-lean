import checkpoints.shen_extension.RetainedShortfall
import checkpoints.shen_extension.ParentBankPeel

namespace LeanCH.BR.RetainedShortfall
open Finset BRq2 BRq3 BR45 BypassRepair LoneRow Closure.DeficitLevels Closure.BoundaryHub

/-- On arbitrary carriers boundary in-regularity at a positive quota
already supplies the lower host exclusion: pad and add one source. -/
theorem host_of_regular {q t} (reg : QBoundaryInRegular q t) (pos : 0<t) : NoHost q t := by
  classical
  intro D U live small free degree
  obtain ⟨E,W,size,safe,paid⟩ := ParentBankPeel.pad free live degree small
  let x:=W.sup id+1
  have off : x∉W := by
    intro hit
    have h := le_sup (f:=id) hit
    change x≤W.sup id at h
    dsimp [x] at h
    omega
  have quota := (degree live.choose live.choose_spec).trans (card_le_card outN_subset)
  have enough : t≤W.card := by omega
  let F:=ParentBankPeel.padArc E W
  have all (a) (am : a∈insert x W) : t≤(outN F (insert x W) a).card := by
    rcases mem_insert.mp am with rfl|aw
    · apply enough.trans (card_le_card _)
      intro b bw
      exact mem_outN.mpr ⟨mem_insert_of_mem bw,by simp [F,ParentBankPeel.padArc,bw,off]⟩
    · apply (paid a aw).trans (card_le_card _)
      intro b bm
      obtain ⟨bw,ab⟩ := mem_outN.mp bm
      exact mem_outN.mpr ⟨mem_insert_of_mem bw,by simp [F,ParentBankPeel.padArc,bw,ab]⟩
  have exact := reg F (insert x W) (ParentBankPeel.pad_free safe)
    (by rw [card_insert_of_notMem off,size]) all x (mem_insert_self ..)
  have empty : inN F (insert x W) x=∅ := by
    ext b
    simp [mem_inN,F,ParentBankPeel.padArc,off]
  rw [empty,card_empty] at exact
  omega

/-- Each particular erased label forces enough actual parents without
spare, even on an arbitrary intermediate carrier. -/
theorem regular_column {D U q t x} (br : Compose.Boundary.BoundaryRegular q t)
    (cut : 1≤q) (degree : 2≤t) (free : QFree D U q) (xm : x∈U)
    (live : (U.erase x).Nonempty) (room : U.card≤q*t+1) :
    2+cost t D U x≤total t D U+
      ((U.erase x).filter (fun u=>D u x=true ∧ (outN D U u).card≤t)).card := by
  have none := host_of_regular (RootRegularBridge.inRegular_of_boundaryRegular cut br) (by omega)
  exact column_floor none (RootRegularBridge.near_of_boundaryRegular br none cut degree) free xm live room

attribute [aesop safe forward (immediate := [reg,pos]) (rule_sets := [CHGraphFamilies])] host_of_regular
attribute [aesop safe forward (immediate := [br,cut,degree,free,xm,live,room]) (rule_sets := [CHGraphFamilies])] regular_column
#print axioms host_of_regular
#print axioms regular_column
end LeanCH.BR.RetainedShortfall
