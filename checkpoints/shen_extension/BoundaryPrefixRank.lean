import checkpoints.shen_extension.ShortfallBridge
import checkpoints.shen_extension.CyclePrefixGrowth
namespace LeanCH.BR.BoundaryPrefixRank
open Finset BRq2 BRq3 BR45 BRsGen Closure.BoundaryHub

/-- At the regular boundary the punctured child cannot retain a row
strictly above its minimum. The row is an actual native head of the root. -/
theorem heavy_prefix {D V q r d j u} (free : QFree D V q) (root : u∈V)
    (degree : ∀x∈V,r≤(outN D V x).card) (time : j+1≤q) (pos : 2≤j)
    (heavy : d<r) (regular : QBoundaryInRegular q d)
    (size : (ball D V u j).card=q*d+2) :
    (ball D V u j).card+r < (ball D V u (j+1)).card+d := by
  classical
  let W := (ball D V u j).erase u
  have ff := free.mono_set (show W⊆V from (erase_subset _ _).trans ball_subset)
  have wc := card_erase_add_one (a:=u) (self_mem_ball (D:=D) (k:=j) root)
  have sum := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (show j≤j+1 by omega))
  by_contra! small
  have rank := minOut_prefix_erase (d:=d) free root time degree (by omega)
  have rows := regular D W ff (by dsimp [W]; omega) rank
  have total := sum_out_in D W
  rw [sum_congr rfl rows] at total
  have all := (sum_eq_sum_iff_of_le rank).mp total.symm
  obtain ⟨x,xm⟩ := card_pos.mp (by have := degree u root; omega : 0<(outN D V u).card)
  have x1 := X_B1 xm
  have xw : x∈W := mem_erase.mpr ⟨fun eq=>loopfree free (by omega) root (eq ▸ (mem_outN.mp xm).2),
    ball_mono_radius (by omega : 1≤j) x1⟩
  have keep := outN_prefix_erase_root free root (by omega : 1+1≤q) x1
  have still := (degree x (outN_subset xm)).trans (card_le_card (keep.trans
    (outN_mono (erase_subset_erase u (ball_mono_radius (by omega : 2≤j))) x)))
  have exactRow : d=(outN D W x).card := all x xw
  change r≤(outN D W x).card at still
  omega

/-- A small third ball restricts the width of the literal second ball.
The extreme retained-degree-two case uses its boundary regularity. -/
theorem second_cap {D V q r u} (free : QFree D V q) (root : u∈V)
    (degree : ∀x∈V,r≤(outN D V x).card) (hr : 4≤r) (time : r+1≤q)
    (small : (ball D V u 3).card≤3*r+2) : (ball D V u 2).card≤2*r+3 := by
  have nest := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
  by_contra! high
  by_cases fit : (ball D V u 2).card≤2*q+1
  · have lim := PrefixDegreeGrowth.small_rank_step (j:=2) (d:=2) free root (by omega) degree
      (by omega) (by decide) (by decide) (by omega) (by omega)
    simp only [Nat.reduceAdd] at lim
    omega
  by_cases eq : (ball D V u 2).card=q*2+2
  · have lim := heavy_prefix free root degree (by omega) (by decide : 2≤2)
      (by omega : 2<r) (ShortfallBridge.inRegular_two (by omega)) eq
    simp only [Nat.reduceAdd] at lim
    omega
  have lim := PrefixDegreeGrowth.small_rank_step (j:=2) (d:=3) free root (by omega) degree
    (by omega) (by decide) (by decide) (by omega) (by omega)
  simp only [Nat.reduceAdd] at lim
  omega

theorem third_tight {D V q r u} (free : QFree D V q) (root : u∈V)
    (degree : ∀x∈V,r≤(outN D V x).card) (hr : 4≤r) (time : r+1≤q)
    (small : (ball D V u 3).card≤3*r+1) :
    (ball D V u 2).card=2*r+1 ∧ (ball D V u 3).card=3*r+1 := by
  have base := card_ball_two_ge_twice (by omega : 2≤r) (free.mono_bound (by omega)) degree root
  have wide := second_cap free root degree hr time (by omega)
  have lim : (ball D V u 2).card≤q+r+1 := by
    by_contra! high
    have step := PrefixDegreeGrowth.small_rank_step (j:=2) (d:=2) free root (by omega) degree
      (by omega) (by decide) (by decide) (by omega) (by omega)
    simp only [Nat.reduceAdd] at step
    omega
  have paid := FullRowsOnShortestCycle.third_layer free root degree hr (by omega) (by omega) lim
  have count := @card_B3 D V u
  omega

attribute [aesop safe forward (immediate := [free,root,degree,time,pos,heavy,regular,size]) (rule_sets := [CHGraphFamilies])] heavy_prefix
attribute [aesop safe forward (immediate := [free,root,degree,hr,time,small]) (rule_sets := [CHGraphFamilies])] second_cap third_tight
#print axioms heavy_prefix
#print axioms second_cap
#print axioms third_tight
end LeanCH.BR.BoundaryPrefixRank
