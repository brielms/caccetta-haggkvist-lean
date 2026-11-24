import checkpoints.shen_extension.PowerReceiverBudget
import checkpoints.shen_extension.RetainedRadiusLayers

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 BRsGen BypassRepair RetainedRadiusLayers ParentBankPeel

/-- The old and retained balls have the same paths up to the penultimate
step. Only labels in the actual next shell can disappear at the last step. -/
theorem last_shell {D V q u x i j K} (free : QFree D V q) (uv : u∈V)
    (start : x∈(ball D V u i).erase u) (reach : i+j≤K) (time : K+1≤q) :
    ball D V x (j+1)⊆ball D ((ball D V u K).erase u) x (j+1) ∪
      (ball D V u (K+1)\ball D V u K) := by
  intro z zm
  have xv := ball_subset (mem_of_mem_erase start)
  have big := retained_ball free uv start (by omega : i+(j+1)≤K+1) time
  have inside := ball_subset (big ▸ zm)
  by_cases prev : z∈ball D V u K
  · apply mem_union_left
    have small := retained_ball free uv start reach (by omega : K≤q)
    by_cases early : z∈ball D V x j
    · exact ball_mono_radius (Nat.le_succ j) (small ▸ early)
    obtain ⟨w,wm,arc⟩ := ball_succ_pred xv zm early
    exact ball_step (small ▸ wm) (mem_erase.mpr ⟨(mem_erase.mp inside).1,prev⟩) arc
  · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_of_mem_erase inside,prev⟩)

theorem loss_bound {D V q u x i j K} (free : QFree D V q) (uv : u∈V)
    (start : x∈(ball D V u i).erase u) (reach : i+j≤K) (time : K+1≤q) :
    (ball D V x (j+1)).card≤(ball D ((ball D V u K).erase u) x (j+1)).card+
      ((ball D V u (K+1)).card-(ball D V u K).card) := by
  have lim := (card_le_card (last_shell free uv start reach time)).trans (card_union_le _ _)
  rw [card_sdiff_of_subset (ball_mono_radius (Nat.le_succ _))] at lim
  exact lim

/-- At a retained full row an inherited ball floor can grow again.
The relevant quota is the one on the retained graph. -/
theorem renew_floor {D W q x j d b} (free : QFree D W q) (xm : x∈W)
    (degree : ∀w∈W,d≤(outN D W w).card) (nohost : NoHost q d)
    (time : j+1≤q) (start : b≤(ball D W x j).card) (seed : 1<b) (room : b≤q*d+1) :
    b+1≤(ball D W x (j+1)).card := by
  have mono := card_le_card (ball_mono_radius (D:=D) (W:=W) (u:=x) (show j≤j+1 by omega))
  by_contra! fail
  have gain := PrefixDegreeGrowth.step (d:=d) free xm time degree
    (fun _ ne fit safe paid=>nohost D _ ne fit safe paid) (by omega) (by omega)
  omega

#print axioms last_shell
#print axioms loss_bound
#print axioms renew_floor
end LeanCH.BR.FragmentScoreEquality