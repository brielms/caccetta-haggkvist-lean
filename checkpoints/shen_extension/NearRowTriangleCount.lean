import checkpoints.shen_extension.CommonCoreGrowth
import checkpoints.shen_extension.ReplacementRowTypes

namespace LeanCH.BR.NearRowTriangleCount
open Finset BRq2 BRq3 BypassRepair CommonCoreCompression ReplacementRowTypes
open scoped Classical

/-- Any two disjoint degree-sized sets omit at least six directed arcs
from the first to the second at the two-label order. -/
theorem six_missing {D V L B q t} (free : QFree D V q) (hq : 3≤q) (ht : 5≤t)
    (reg : OutEq (t+1) D V) (order : V.card=q*t+2) (lower : ∀ k,k<t+1 → NoHost q k)
    (lv : L⊆V) (bv : B⊆V) (apart : Disjoint L B) (ls : L.card=t+1) (bs : B.card=t+1) :
    6 ≤ ∑ x∈L,(B \ outN D V x).card := by
  classical
  let miss (x) := (B \ outN D V x).card
  by_cases full : ∃ a∈L,B⊆outN D V a
  · obtain ⟨a,al,ab⟩ := full
    have eq : B=outN D V a := eq_of_subset_of_card_le ab (by rw [bs,reg a (lv al)])
    let N := nearby D V t a
    have sizeN : N.card<t := nearby_bound free hq (by omega) reg order (lower t (by omega)) (lv al)
    have nl : (L ∩ N).card≤N.card := card_le_card inter_subset_right
    have two : 1<(L \ N).card := by
      have count := card_sdiff_add_card_inter L N
      omega
    obtain ⟨x,xm,y,ym,xy⟩ := one_lt_card.mp two
    have costly (u) (um : u∈L \ N) : 2≤miss u := by
      obtain ⟨ul,un⟩ := mem_sdiff.mp um
      have off := fun ub => disjoint_left.mp apart ul ub
      have bad : (B ∩ outN D V u).card<t := by
        by_contra! good
        exact un (mem_filter.mpr ⟨mem_sdiff.mpr ⟨lv ul,eq ▸ off⟩,eq ▸ good⟩)
      have count := card_sdiff_add_card_inter B (outN D V u)
      dsimp [miss]; omega
    have xl := (mem_sdiff.mp xm).1
    have yl := (mem_sdiff.mp ym).1
    let K := (L.erase x).erase y
    have ylive : y∈L.erase x := mem_erase.mpr ⟨xy.symm,yl⟩
    have ks : K.card=t-1 := by
      simp only [K,card_erase_of_mem ylive,card_erase_of_mem xl,ls]; omega
    let F := K.biUnion (fun u => B \ outN D V u)
    have lose : 2≤∑ u∈K,miss u := by
      by_contra! few
      have cnt : F.card≤∑ u∈K,miss u := card_biUnion_le
      have fb : F⊆B := biUnion_subset.mpr (fun _ _ => sdiff_subset)
      have size : t≤(B \ F).card := by rw [card_sdiff_of_subset fb,bs]; omega
      have kv : K⊆V := (erase_subset ..).trans ((erase_subset ..).trans lv)
      apply no_near_rectangle free hq (by omega) reg order lower kv (sdiff_subset.trans bv) ks.ge size
      intro u uk h hm
      obtain ⟨hb,hf⟩ := mem_sdiff.mp hm
      by_contra missing
      exact hf (mem_biUnion.mpr ⟨u,uk,mem_sdiff.mpr ⟨hb,fun om => missing (mem_outN.mp om).2⟩⟩)
    have sx := sum_erase_add L miss xl
    have sy := sum_erase_add (L.erase x) miss ylive
    change (∑ u∈K,miss u)+miss y = _ at sy
    change 6≤∑ u∈L,miss u
    have cx := costly x xm
    have cy := costly y ym
    omega
  · have per (a) (al : a∈L) : 1≤miss a := by
      apply card_pos.mpr
      obtain ⟨y,yb,ya⟩ := Finset.not_subset.mp (fun all => full ⟨a,al,all⟩)
      exact ⟨y,mem_sdiff.mpr ⟨yb,ya⟩⟩
    have cnt := sum_le_sum per
    simp only [sum_const,smul_eq_mul,mul_one,ls] at cnt
    change 6≤∑ x∈L,miss x
    omega

#print axioms six_missing
/-- At a Seymour-tight vertex, the missing second-layer arcs count exactly
the transitive triangles with this source (Ai et al., Theorem 6 proof). -/
theorem tight_vertex_triangles {D V q t v} (free : QFree D V q) (hq : 3≤q) (ht : 5≤t)
    (reg : OutEq (t+1) D V) (order : V.card=q*t+2) (lower : ∀ k,k<t+1 → NoHost q k)
    (vv : v∈V) (tight : (BR45.N2 D V v).card=t+1) :
    6 ≤ ∑ x∈outN D V v,(outN D (outN D V v) x).card := by
  classical
  let L := outN D V v
  let B := BR45.N2 D V v
  have dis : Disjoint L B := disjoint_left.mpr (fun _ xl xb => (BR45.mem_N2.mp xb).2 (BR45.X_B1 xl))
  have six := six_missing free hq ht reg order lower (show L⊆V from outN_subset)
    (show B⊆V from fun _ => BR45.N2_subV) dis (reg v vv) tight
  have eq := sum_congr (s₁:=L) rfl (g:=fun x => (outN D L x).card) (f:=fun x => (B \ outN D V x).card) (by
    intro x xl
    obtain ⟨xv,vx⟩ := mem_outN.mp xl
    have all : outN D V x \ B = outN D L x := by
      ext y
      constructor
      · intro ym
        obtain ⟨ya,yb⟩ := mem_sdiff.mp ym
        obtain ⟨yv,xy⟩ := mem_outN.mp ya
        have b2 : y∈ball D V v 2 := mem_ball.mpr ⟨yv,2,le_rfl,.step xv vx (.step yv xy (.refl _))⟩
        have b1 : y∈ball D V v 1 := by
          by_contra off
          exact yb (BR45.mem_N2.mpr ⟨b2,off⟩)
        rcases (mem_ball_one vv).mp b1 with e|yl
        · exact False.elim (digonfree free (by omega) vv xv vx (e ▸ xy))
        · exact mem_outN.mpr ⟨yl,xy⟩
      · intro ym
        obtain ⟨yl,xy⟩ := mem_outN.mp ym
        exact mem_sdiff.mpr ⟨mem_outN.mpr ⟨outN_subset yl,xy⟩,disjoint_left.mp dis yl⟩
    have left := card_sdiff_add_card_inter B (outN D V x)
    have right := card_sdiff_add_card_inter (outN D V x) B
    rw [all,inter_comm (outN D V x) B,reg x xv] at right
    change B.card=t+1 at tight
    omega)
  exact eq ▸ six

#print axioms tight_vertex_triangles
/-- Low local transitive-triangle count forces a strictly larger second
neighbourhood. A sink in the first neighbourhood supplies the weak bound. -/
theorem low_triangles_strict {D V q t v} (free : QFree D V q) (hq : 3≤q) (ht : 5≤t)
    (reg : OutEq (t+1) D V) (order : V.card=q*t+2) (lower : ∀ k,k<t+1 → NoHost q k)
    (vv : v∈V) (few : (∑ x∈outN D V v,(outN D (outN D V v) x).card)<6) :
    t+1 < (BR45.N2 D V v).card := by
  let L := outN D V v
  have sink : ∃ x∈L,(outN D L x).card=0 := by
    by_contra! positive
    have bound := sum_le_sum (s:=L) (f:=fun _ => 1) (g:=fun x => (outN D L x).card)
      (fun x xl => Nat.pos_of_ne_zero (positive x xl))
    have sz : L.card=t+1 := reg v vv
    change (∑ x∈L,(outN D L x).card)<6 at few
    simp only [sum_const,smul_eq_mul,mul_one] at bound
    omega
  obtain ⟨x,xl,zero⟩ := sink
  obtain ⟨xv,vx⟩ := mem_outN.mp xl
  have sub : outN D V x ⊆ BR45.N2 D V v := by
    intro y ym
    obtain ⟨yv,xy⟩ := mem_outN.mp ym
    refine BR45.mem_N2.mpr ⟨mem_ball.mpr ⟨yv,2,le_rfl,.step xv vx (.step yv xy (.refl _))⟩,?_⟩
    intro b1
    rcases (mem_ball_one vv).mp b1 with e|yl
    · exact digonfree free (by omega) vv xv vx (e ▸ xy)
    · have pos := card_pos.mpr (show (outN D L x).Nonempty from ⟨y,mem_outN.mpr ⟨yl,xy⟩⟩)
      omega
  have weak := card_le_card sub
  rw [reg x xv] at weak
  by_contra! small
  exact (Nat.not_le_of_lt few) (tight_vertex_triangles free hq ht reg order lower vv (le_antisymm small weak))

#print axioms low_triangles_strict
end LeanCH.BR.NearRowTriangleCount
