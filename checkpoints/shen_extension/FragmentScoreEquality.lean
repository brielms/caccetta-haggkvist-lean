import checkpoints.shen_extension.QuotaLibraryPromotion
import checkpoints.shen_extension.MixedFragmentEscape

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 BRsGen BypassRepair ParentBankPeel

/-- A positive punctured ball still grows by at least one while the
current carrier could host the same quota. The seed is the measured
degree at the specified row, independent of the minimum elsewhere. -/
theorem grow_seed {D W q d v r k j} (free : QFree D W q) (vv : v∈W)
    (degree : ∀x∈W,d≤(outN D W x).card) (own : r≤(outN D W v).card)
    (pos : 0<r) (nohost : NoHost q d) (time : k+1≤q) (room : r+k≤q*d+1)
    (steps : j≤k) : r+j+1≤(ball D W v (j+1)).card := by
  induction j with
  | zero =>
    have one := ReachLedger.ball_one free (by omega : 1≤q) vv
    change r+0+1≤(ball D W v 1).card
    omega
  | succ j ih =>
    have before := ih (by omega)
    by_contra! small
    have inc := card_le_card (ball_mono_radius (D:=D) (W:=W) (u:=v) (Nat.le_succ (j+1)))
    change (ball D W v (j+1)).card≤(ball D W v (j+1+1)).card at inc
    change (ball D W v (j+1+1)).card<r+(j+1)+1 at small
    have rise := PrefixDegreeGrowth.step (d:=d) (j:=j+1) free vv (by omega) degree
      (fun _ live size safe paid=>nohost D _ live size safe paid) (by omega) (by omega)
    omega

/-- At equality every ordinary row is at its floor. If such a row sees
a marked high-degree row, its two-ball is already too large; otherwise
the ordinary rows retain the full lower quota on a smaller carrier. -/
theorem strict_fragment_budget {D W H q d r k lo hi} (free : QFree D W q)
    (time : k+k≤q) (depth : 2≤k) (inside : H⊆W)
    (degree : ∀x∈W,d≤(outN D W x).card) (full : ∀x∈H,r≤(outN D W x).card)
    (ordinary : ∀x∈W,lo+1≤(ball D W x k).card)
    (marked : ∀x∈H,hi+1≤(ball D W x k).card) (gain : lo<r)
    (live : H.card<W.card) (size : W.card-H.card≤q*d) (nohost : NoHost q d) :
    2*(H.card*(hi+1)+(W.card-H.card)*(lo+1))<W.card*(W.card+1) := by
  classical
  by_contra! tight
  let price := fun x : ℕ=>if x∈H then 2*(hi+1) else 2*(lo+1)
  have total : (∑x∈W,price x)=2*(H.card*(hi+1)+(W.card-H.card)*(lo+1)) := by
    rw [←sum_sdiff inside]
    have a := sum_congr (s₁:=H) rfl (fun x (xm : x∈H)=>show price x=2*(hi+1) by simp [price,xm])
    have b := sum_congr (s₁:=W\H) rfl (fun x (xm : x∈W\H)=>show price x=2*(lo+1) by simp [price,(mem_sdiff.mp xm).2])
    rw [a,b]
    simp only [sum_const,nsmul_eq_mul,card_sdiff_of_subset inside,Nat.cast_id]
    ring
  have paid x (xm : x∈W) : price x≤(ball D W x k).card+(ball D W x k).card := by
    by_cases m : x∈H
    · have := marked x m; simp [price,m]; omega
    · have := ordinary x xm; simp [price,m]; omega
  have exactRows := MixedFragmentEscape.score_equality free time price paid (total.symm ▸ tight)
  have left := card_sdiff_of_subset inside
  apply nohost D (W\H) (card_pos.mp (by omega)) (by omega) (free.mono_set sdiff_subset)
  intro x xm
  obtain ⟨xw,xh⟩ := mem_sdiff.mp xm
  apply (degree x xw).trans
  apply card_le_card
  intro y ym
  obtain ⟨yw,xy⟩ := mem_outN.mp ym
  refine mem_outN.mpr ⟨mem_sdiff.mpr ⟨yw,?_⟩,xy⟩
  intro yh
  have neighbors : insert x (outN D W y)⊆ball D W x k := by
    intro z zm
    rcases mem_insert.mp zm with rfl|yz
    · exact self_mem_ball xw
    · exact ball_mono_radius depth (ball_step (X_B1 ym) (outN_subset yz) (mem_outN.mp yz).2)
  have off : x∉outN D W y := fun yx=>digonfree free (by omega) xw yw xy (mem_outN.mp yx).2
  have limit := card_le_card neighbors
  rw [card_insert_of_notMem off] at limit
  have eq := exactRows x xw
  simp [price,xh] at eq
  have := full y yh
  omega

#print axioms grow_seed
#print axioms strict_fragment_budget
end LeanCH.BR.FragmentScoreEquality
