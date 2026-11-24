import checkpoints.shen_extension.ReceiverSourceFrontier
import LeanCH.BR.BRCompletionConflict
import LeanCH.BR.BRWeightedExactRepairProfile

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 BRsub AvoidedHeadQuota

/-- A boundary-regular bank with a surplus row cannot repair its sole
short row by a missing arc. The blocking path stays inside that bank. -/
theorem short_return {D V H q t g b} (free : QFree D V q) (hv : H⊆V) (cut : 1≤q)
    (size : H.card=q*t+1) (boundary : Compose.Boundary.BoundaryRegular q t)
    (gm : g∈H) (bm : b∈H) (miss : D g b≠true) (near : t≤(outN D H g).card+1)
    (others : ∀x∈H,x≠g → t≤(outN D H x).card) (excess : ∃x∈H,t<(outN D H x).card) :
    g∈ball D H b (q-1) := by
  by_contra off
  let G : ↥H := ⟨g,gm⟩
  let B : ↥H := ⟨b,bm⟩
  have safe := (WeightedSD.qfree_insert_iff_no_short_return cut (free.mono_set hv) G B).mpr off
  have count x := WeightedSD.outdegree_insert_missing G B miss x
  have deg (x) (xm : x∈H) : t≤(outN (WeightedSD.insertArc D G B) H x).card := by
    rw [count]
    by_cases eq : x=g
    · subst x; simpa [G] using near
    · simpa [G,eq] using others x xm eq
  obtain ⟨x,xm,high⟩ := excess
  have ge : (outN D H x).card≤(outN (WeightedSD.insertArc D G B) H x).card := by rw [count]; omega
  exact WeightedSD.boundary_regular_no_excess cut boundary safe size deg xm (high.trans_le ge)

/-- If the shortcut replaces an actual two-step path on the original
carrier, the blocked return has the full q-1 steps on the smaller bank. -/
theorem punctured_return {D V H q t g b z} (free : QFree D V q) (hv : H⊆V) (cut : 2≤q)
    (size : H.card=q*t+1) (boundary : Compose.Boundary.BoundaryRegular q t)
    (gm : g∈H) (bm : b∈H) (zm : z∈V) (gz : D g z=true) (zb : D z b=true)
    (miss : D g b≠true) (near : t≤(outN D H g).card+1)
    (others : ∀x∈H,x≠g → t≤(outN D H x).card) (excess : ∃x∈H,t<(outN D H x).card) :
    Walk D H b g (q-1) := by
  obtain ⟨_,k,le,walk⟩ := mem_ball.mp (short_return free hv (by omega) size boundary gm bm miss near others excess)
  have lift {x y k} (w : Walk D H x y k) : Walk D V x y k := by
    induction w with
    | refl => exact .refl _
    | step next arc _ ih => exact .step (hv next) arc ih
  have len : k=q-1 := by
    by_contra different
    exact free g (k+1+1) (by omega) (by omega) (.step zm gz (.step (hv bm) zb (lift walk)))
  exact len ▸ walk

/-- Overbooked omissions force a surplus row, independently of boundary
regularity and of which row misses which exceptional column. -/
theorem high_head {D V q r t v} {X : Finset ℕ} {k : ℕ} (free : QFree D V q)
    (cut : 2≤q) (vm : v∈V) (reg : OutEq r D V)
    (inside : X⊆ball D V v 2 \ ball D V v 1)
    (miss : ∀z∈X,k≤(outN D V v \ inN D V z).card)
    (overbook : r*((ball D V v 2 \ ball D V v 1).card+t-r)<X.card*k) :
    ∃h∈outN D V v,t<(outN D (outN D V v) h).card := by
  classical
  by_contra! all
  let H:=outN D V v
  let Y:=ball D V v 2 \ ball D V v 1
  have rows h (hm : h∈H) : (Y\outN D V h).card≤Y.card+t-r := by
    have id := missing_count free cut vm hm (reg h (mem_outN.mp hm).1)
    change (Y\outN D V h).card+r=Y.card+(outN D H h).card at id
    have le : (outN D H h).card≤t := all h hm
    omega
  have enough := sum_le_sum miss
  rw [sum_const_nat (fun _ _=>rfl)] at enough
  have subset := sum_le_sum_of_subset (f:=fun z=>(H\inN D V z).card) inside
  have eq := omitted_entries (D:=D) (show H⊆V from outN_subset) (show Y⊆V from sdiff_subset.trans ball_subset)
  have cap := sum_le_sum rows
  rw [sum_const_nat (fun _ _=>rfl),show H.card=r from reg v vm] at cap
  exact (enough.trans (subset.trans (eq.le.trans cap))).not_gt overbook

attribute [aesop safe forward (immediate := [free,hv,cut,size,boundary,gm,bm,miss,near,others,excess])
  (rule_sets := [CHGraphFamilies])] short_return
attribute [aesop safe forward (immediate := [free,hv,cut,size,boundary,gm,bm,zm,gz,zb,miss,near,others,excess])
  (rule_sets := [CHGraphFamilies])] punctured_return
attribute [aesop safe forward (immediate := [free,cut,vm,reg,inside,miss,overbook])
  (rule_sets := [CHGraphFamilies])] high_head
#print axioms short_return
#print axioms punctured_return
#print axioms high_head
end LeanCH.BR.LabelledCompromiseRecipe
