import checkpoints.shen_extension.OneSpareBankPacking
import LeanCH.BR.BRFiniteWalk

namespace LeanCH.BR.SharedLayerBarrier
open Finset BRq2 BRq3 BR45

/-- If v can return to every label on the kth shell within k positive
steps, any shortest path from u to v crossing that shell would close a
walk within the forbidden cutoff. -/
theorem barrier {D V q u v k} (safe : QFree D V q) (vv : v∈V) (pos : 0<k)
    (early : v∉ball D V u (k-1))
    (returns : ∀y∈ball D V u k\ball D V u (k-1),∃j,0<j ∧ j≤k ∧ Walk D V v y j) :
    v∉ball D V u q := by
  classical
  intro hit
  obtain ⟨_,i,fit,w⟩ := mem_ball.mp hit
  let live : ∃j,Walk D V u v j := ⟨i,w⟩
  let m := Nat.find live
  have shortest : Walk D V u v m := Nat.find_spec live
  have minlen {j} (road : Walk D V u v j) : m≤j := Nat.find_min' live road
  have km : k≤m := by by_contra! low; exact early (mem_ball.mpr ⟨vv,by exact ⟨m,by omega,shortest⟩⟩)
  obtain ⟨f,head,last,arcs⟩ := shortest.toFun
  have yv : f k∈V := by
    have := (arcs (k-1) (by omega)).1
    rwa [Nat.sub_add_cancel pos] at this
  have pre := walk_between arcs (i:=0) (j:=k) (by omega) km
  rw [head,Nat.sub_zero] at pre
  have post := walk_between arcs km (Nat.le_refl m)
  rw [last] at post
  have ym : f k∈ball D V u k\ball D V u (k-1) := by
    refine mem_sdiff.mpr ⟨mem_ball.mpr ⟨yv,k,le_rfl,pre⟩,?_⟩
    intro short
    obtain ⟨_,j,small,way⟩ := mem_ball.mp short
    have := minlen (way.append post)
    omega
  obtain ⟨j,positive,short,back⟩ := returns (f k) ym
  have bound := minlen w
  exact safe v _ (by omega) (by omega) (back.append post)

/-- Two roots whose marked rows use the same physical full head
miss each other at every radius up to q, even with different second
layers. The selected vertex and the two banks stay on one carrier. -/
theorem shared_full_remote {D V q r u v w} (safe : QFree D V q) (hq : 4≤q)
    (uv : u∈V) (vv : v∈V) (ne : u≠v) (reg : OutEq r D V)
    (us : (N2 D V u).card+1=r) (vs : (N2 D V v).card+1=r)
    (wu : w∈outN D V u) (wv : w∈outN D V v)
    (coversU : ∀x∈N2 D V u,D w x=true) (coversV : ∀x∈N2 D V v,D w x=true) :
    v∉ball D V u q := by
  have miss := OneSpareGrowth.shared_full_misses safe hq uv vv ne reg us vs wu wv coversU coversV
  apply barrier (k:=2) safe vv (by decide) (fun hit=>miss (ball_mono_radius (by decide : 2-1≤2) hit))
  intro y ym
  exact ⟨2,by decide,le_rfl,.step (outN_subset wv) (mem_outN.mp wv).2
    (.step (N2_subV ym) (coversU y ym) (.refl y))⟩

#print axioms barrier
#print axioms shared_full_remote
end LeanCH.BR.SharedLayerBarrier
