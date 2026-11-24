import checkpoints.shen_extension.ReceiverTightReturns

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 BypassRepair CHRuleCatalog

/-- Price both endpoints of an actual shell return in the very same
omission column. Each count uses every available label up to the cutoff
on the head side, and all shell parents on the other side. -/
theorem turn_counts {D V q r v z b} (free : QFree D V q) (cut : 3≤q) (vm : v∈V)
    (reg : OutEq r D V) (zy : z∈ball D V v 2 \ ball D V v 1)
    (bh : b∈outN D V v) (zb : D z b=true) :
    let H:=outN D V v
    let Y:=ball D V v 2 \ ball D V v 1
    r+1+max (min q (outN D H z).card) (inN D Y b).card ≤
      Y.card+(H\inN D V z).card := by
  classical
  let H:=outN D V v
  let Y:=ball D V v 2 \ ball D V v 1
  let K:=outN D H z
  let I:=inN D Y b
  have bk : b∈K := mem_outN.mpr ⟨bh,zb⟩
  have zi : z∈I := mem_inN.mpr ⟨zy,zb⟩
  have compare {S : Finset ℕ} (zs : z∈S) : (missedBy (D:=D) H S).card≤(H\inN D V z).card :=
    card_le_card fun _ hm=>mem_sdiff.mpr ⟨(mem_filter.mp hm).1,
      fun hit=>(mem_filter.mp hm).2 z zs (mem_inN.mp hit).2⟩
  obtain ⟨B,sub,sz⟩ := exists_subset_card_eq (min_le_right q K.card)
  have pos : 0<K.card := card_pos.mpr ⟨b,bk⟩
  have bz : B.Nonempty := card_pos.mp (by omega)
  have out := return_capacity free cut vm reg (Z:={z}) (by simpa using zy)
    (sub.trans (show K⊆H from outN_subset)) bz (a:=1) (by omega) ReachLedger.noHost_one
    (by simpa using fun h hm=>(mem_outN.mp (sub hm)).2)
  have inc := return_capacity free cut vm reg (Z:=I) (B:={b}) (show I⊆Y from fun _ hit=>(mem_inN.mp hit).1)
    (by simpa using bh) (singleton_nonempty _) (a:=1) (by simp; omega) ReachLedger.noHost_one
    (by simpa using fun w wm=>(mem_inN.mp (show w∈I from wm)).2)
  have left := compare (mem_singleton_self z)
  have right := compare zi
  simp only [card_singleton] at out inc
  change r+1+max (min q K.card) I.card≤Y.card+(H\inN D V z).card
  change r+1+B.card+1≤Y.card+(missedBy (D:=D) H {z}).card+1 at out
  change r+I.card+1+1≤Y.card+(missedBy (D:=D) H I).card+1 at inc
  omega

theorem cut_of_full {q d s k l} (fit : FullWindow q d s k l) : 3≤q := fit.1

attribute [aesop safe forward (immediate := [fit]) (rule_sets := [CHGraphFamilies])] cut_of_full
attribute [aesop safe forward (immediate := [free,cut,vm,reg,zy,bh,zb])
  (rule_sets := [CHGraphFamilies])] turn_counts
#print axioms turn_counts
#print axioms cut_of_full
end LeanCH.BR.LabelledCompromiseRecipe
