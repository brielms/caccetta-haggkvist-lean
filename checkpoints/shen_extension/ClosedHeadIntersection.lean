import checkpoints.shen_extension.TwoReplacementContraction
import LeanCH.BR.BRq3Top3
import LeanCH.BR.BRRichMissGeometry
import LeanCH.BR.BRShortestCycle
import LeanCH.BR.BRq4All

namespace LeanCH.BR.Closure.ClosedHeadIntersection
open BRq2 BRq3 Finset

/-- The closed out-neighborhoods of every pair meet inside T. -/
def Intersects (D : CH.Digraph) (T : Finset ℕ) : Prop :=
  ∀ u ∈ T, ∀ v ∈ T, ∃ w ∈ T, (w=u ∨ D u w=true) ∧ (w=v ∨ D v w=true)

theorem internal_degree {D : CH.Digraph} {T : Finset ℕ} (safe : QFree D T 3)
    (heads : ∀ u ∈ T, (outN D T u).Nonempty) (pairs : Intersects D T) :
    ∀ v ∈ T, 3 ≤ (outN D T v).card := by
  intro v hv
  let E := outN D T v
  have two {a b} (ha : a ∈ T) (hb : b ∈ T) (ab : D a b=true) := digonfree safe (by decide) ha hb ab
  have three {a b c} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T)
      (ab : D a b=true) (bc : D b c=true) (ca : D c a=true) : False :=
    safe a 3 (by decide) (by decide) (.step hb ab (.step hc bc (.step ha ca (.refl a))))
  have returns {a w} (aE : a ∈ E) (hw : w ∈ T) (aw : D a w=true) :
      ∃ z ∈ E, z=w ∨ D w z=true := by
    obtain ⟨ha,va⟩ := mem_outN.mp aE
    obtain ⟨z,hz,vz,wz⟩ := pairs v hv w hw
    rcases vz with rfl | vz
    · rcases wz with rfl | wv
      · exact False.elim (two hv ha va aw)
      · exact False.elim (three hv ha hw va aw wv)
    · exact ⟨z,mem_outN.mpr ⟨hz,vz⟩,wz⟩
  have single (a) (aE : a ∈ E) (cover : ∀ z ∈ E, z=a) : False := by
    have ha := outN_subset aE
    obtain ⟨w,hw⟩ := heads a ha
    obtain ⟨wT,aw⟩ := mem_outN.mp hw
    obtain ⟨z,zE,zw⟩ := returns aE wT aw
    rw [cover z zE] at zw
    rcases zw with rfl | wa
    · exact loopfree safe (by decide) ha aw
    · exact two ha wT aw wa
  have noArc {a b} (aE : a ∈ E) (bE : b ∈ E) (cover : ∀ z ∈ E, z=a ∨ z=b)
      (ab : D a b=true) : False := by
    have ha := outN_subset aE
    have hb := outN_subset bE
    obtain ⟨w,hw⟩ := heads b hb
    obtain ⟨wT,bw⟩ := mem_outN.mp hw
    obtain ⟨z,zE,zw⟩ := returns bE wT bw
    rcases cover z zE with rfl | rfl
    · rcases zw with rfl | wz
      · exact two ha hb ab bw
      · exact three ha hb wT ab bw wz
    · rcases zw with rfl | wz
      · exact loopfree safe (by decide) hb bw
      · exact two hb wT bw wz
  by_contra small
  have pos := card_pos.mpr (heads v hv)
  have cases : E.card=1 ∨ E.card=2 := by dsimp [E]; omega
  rcases cases with one | two'
  · obtain ⟨a,eq⟩ := card_eq_one.mp one
    exact single a (by simp [eq]) (by simp [eq])
  · obtain ⟨a,b,ne,eq⟩ := card_eq_two.mp two'
    have aE : a ∈ E := by simp [eq]
    have bE : b ∈ E := by simp [eq]
    have cover : ∀ z ∈ E, z=a ∨ z=b := by simp [eq]
    have ha := outN_subset aE
    have hb := outN_subset bE
    obtain ⟨w,wT,aw,bw⟩ := pairs a ha b hb
    have noAB := noArc aE bE cover
    have noBA := noArc bE aE (fun z hz => (cover z hz).symm)
    rcases aw with rfl | aw
    · exact bw.elim ne noBA
    rcases bw with rfl | bw
    · exact noAB aw
    obtain ⟨z,zE,zw⟩ := returns aE wT aw
    rcases cover z zE with rfl | rfl
    · rcases zw with rfl | wz
      · exact loopfree safe (by decide) ha aw
      · exact two ha wT aw wz
    · rcases zw with rfl | wz
      · exact loopfree safe (by decide) hb bw
      · exact two hb wT bw wz

theorem order_ten {D : CH.Digraph} {T : Finset ℕ} (safe : QFree D T 3)
    (heads : ∀ u ∈ T, (outN D T u).Nonempty) (pairs : Intersects D T) (live : T.Nonempty) :
    10 ≤ T.card := by
  obtain ⟨F,sub,degree⟩ := exists_outEq (internal_degree safe heads pairs)
  obtain ⟨u,hu⟩ := live
  exact (top3 (qfree_sub sub safe) degree hu).trans (card_le_card ball_subset)

#print axioms internal_degree
#print axioms order_ten

/-- On a shortest cycle, two roots two positions apart must have an actual
common head off the cycle, and that head has no arc back into the cycle. -/
theorem cycle_head {D : CH.Digraph} {T M : Finset ℕ} {q u v w : ℕ}
    (pairs : Intersects D T) (hq : 3 ≤ q) (safe : QFree D T q) (sub : M ⊆ T)
    (size : M.card=q+1) (one : OutEq 1 D M)
    (um : u ∈ M) (vm : v ∈ M) (wm : w ∈ M) (uv : D u v=true) (vw : D v w=true) :
    ∃ h ∈ T \ M, D u h=true ∧ D w h=true ∧ outN D M h=∅ := by
  have only : outN D M u = {v} := eq_of_subset_of_card_le
    (singleton_subset_iff.mpr (mem_outN.mpr ⟨vm,uv⟩)) (by simp [one u um]) |>.symm
  have neq : u ≠ w := fun eq => digonfree safe (by omega) (sub um) (sub vm) uv (eq ▸ vw)
  have noWU (wu : D w u=true) := safe u 3 (by omega) hq
    (.step (sub vm) uv (.step (sub wm) vw (.step (sub um) wu (.refl u))))
  have noUW (uw : D u w=true) : False := by
    have h : w ∈ outN D M u := mem_outN.mpr ⟨wm,uw⟩
    rw [only,mem_singleton] at h
    exact loopfree safe (by omega) (sub vm) (h ▸ vw)
  obtain ⟨h,ht,uh,wh⟩ := pairs u (sub um) w (sub wm)
  rcases uh with rfl | uh
  · exact False.elim (wh.elim neq noWU)
  rcases wh with rfl | wh
  · exact False.elim (noUW uh)
  have outside : h ∉ M := by
    intro hm
    have hv : h ∈ outN D M u := mem_outN.mpr ⟨hm,uh⟩
    rw [only,mem_singleton] at hv
    exact digonfree safe (by omega) (sub vm) (sub wm) vw (hv ▸ wh)
  refine ⟨h,mem_sdiff.mpr ⟨ht,outside⟩,uh,wh,eq_empty_iff_forall_notMem.mpr ?_⟩
  intro t hit
  have few := WeightedSD.cycle_two_step_detour_heads (by omega : 2≤q) safe sub size one um vm wm ht uv vw uh hit
  have edge := (mem_outN.mp hit).2
  rcases mem_insert.mp few with r | r
  · rw [r] at edge
    exact safe v 3 (by omega) hq (.step (sub wm) vw (.step ht wh (.step (sub vm) edge (.refl v))))
  · rw [mem_singleton.mp r] at edge
    exact digonfree safe (by omega) (sub wm) ht wh edge

/-- Intersecting closed rows turn a radius-(q-1) ball bound at degree m
into one extra copy of q-1 in the order bound, for every m and q. -/
theorem order_from_ball {D : CH.Digraph} {T : Finset ℕ} {q m u : ℕ}
    (pairs : Intersects D T) (hq : 1≤q) (hm : 0<m) (safe : QFree D T q)
    (balls : Ball q m) (degree : ∀ x ∈ T, m ≤ (outN D T x).card)
    (ut : u ∈ T) (exactRow : (outN D T u).card=m) :
    (m+1)*(q-1)+1 ≤ T.card := by
  classical
  let Z := insert u (outN D T u)
  have zt : Z ⊆ T := insert_subset ut outN_subset
  have cardZ : Z.card=m+1 := by
    rw [show Z=insert u (outN D T u) from rfl,card_insert_of_notMem,exactRow]
    exact fun h => loopfree safe hq ut (mem_outN.mp h).2
  obtain ⟨x,xz,top⟩ := Z.exists_max_image (fun z => (BR45.inN D T z).card) (insert_nonempty _ _)
  let L := (BR45.inN D T x).card
  let parents (z : ℕ) := (insert z (BR45.inN D T z)).erase u
  have cover : T.erase u ⊆ Z.biUnion parents := by
    intro y hy
    obtain ⟨yu,yt⟩ := mem_erase.mp hy
    obtain ⟨z,zt',uz,yz⟩ := pairs u ut y yt
    have zi : z ∈ Z := mem_insert.mpr (uz.imp_right (fun a => mem_outN.mpr ⟨zt',a⟩))
    exact mem_biUnion.mpr ⟨z,zi,mem_erase.mpr ⟨yu,mem_insert.mpr
      (yz.imp Eq.symm (fun a => BR45.mem_inN.mpr ⟨yt,a⟩))⟩⟩
  have cost (z) (zz : z ∈ Z) : (parents z).card ≤ L := by
    have has : u ∈ insert z (BR45.inN D T z) := by
      rcases mem_insert.mp zz with rfl | zz
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (BR45.mem_inN.mpr ⟨ut,(mem_outN.mp zz).2⟩)
    have bnd := card_insert_le z (BR45.inN D T z)
    have cap := top z zz
    dsimp only [parents,L]
    rw [card_erase_of_mem has]
    omega
  have upper := ((card_le_card cover).trans card_biUnion_le).trans (sum_le_sum cost)
  rw [sum_const,nsmul_eq_mul,cardZ,card_erase_of_mem ut] at upper
  have row : BR45.inN D T x ⊆ T \ ball D T x (q-1) := by
    intro y hy
    obtain ⟨yt,yx⟩ := BR45.mem_inN.mp hy
    exact mem_sdiff.mpr ⟨yt,fun inBall => no_back_arc safe (zt xz) inBall (by omega) yx⟩
  have lower := card_le_card row
  have sum := card_sdiff_add_card_eq_card (ball_subset (D:=D) (W:=T) (u:=x) (k:=q-1))
  have growth := BR45.ball_of_min balls safe degree x (zt xz)
  change L ≤ _ at lower
  have low : m*(q-1)+1+L ≤ T.card := by omega
  have high : T.card ≤ 1+(m+1)*L := by
    change T.card-1 ≤ (m+1)*L at upper
    omega
  have prod : m*(q-1) ≤ m*L := by rw [Nat.add_mul,Nat.one_mul] at high; omega
  have span : q-1 ≤ L := Nat.le_of_mul_le_mul_left prod hm
  rw [Nat.add_mul,Nat.one_mul]; omega

theorem order_at_girth {D : CH.Digraph} {T : Finset ℕ} {q : ℕ}
    (hq : 3≤q) (free : QFree D T q) (heads : ∀ u ∈ T, (outN D T u).Nonempty)
    (pairs : Intersects D T) (live : T.Nonempty) : 4*(q-1)+1 ≤ T.card := by
  have deg := internal_degree (free.mono_bound hq) heads pairs
  by_cases row : ∃ x ∈ T, (outN D T x).card=3
  · obtain ⟨x,xt,eq⟩ := row
    exact order_from_ball pairs (by omega) (by decide) free (ball_all q (by omega)) deg xt eq
  · have four (x) (xt : x ∈ T) : 4 ≤ (outN D T x).card := by
      have := deg x xt
      have ne : (outN D T x).card ≠ 3 := fun eq => row ⟨_,xt,eq⟩
      omega
    by_cases h : 4≤q
    · have := BR45.dt_size (by omega) (BRq4.ball_all4 q h) free four live
      omega
    · have := order_ten (free.mono_bound hq) heads pairs live
      omega

def HasCycleHeads (D : CH.Digraph) (T : Finset ℕ) : Prop :=
  ∃ q M, 3 ≤ q ∧ 4*(q-1)+1 ≤ T.card ∧ QFree D T q ∧ M ⊆ T ∧ M.card=q+1 ∧ OutEq 1 D M ∧
    ∀ u ∈ M, ∀ v ∈ outN D M u, ∀ w ∈ outN D M v,
      ∃ h ∈ T \ M, D u h=true ∧ D w h=true ∧ outN D M h=∅

theorem shortest_cycle_heads {D : CH.Digraph} {T : Finset ℕ} (safe : QFree D T 3)
    (heads : ∀ u ∈ T, (outN D T u).Nonempty) (pairs : Intersects D T) (live : T.Nonempty) :
    HasCycleHeads D T := by
  obtain ⟨q,M,hq,free,sub,size,one⟩ := BRsGen.exists_minimal_cycle_support (by decide : 1≤3)
    safe (fun x hx => card_pos.mpr (heads x hx)) live
  exact ⟨q,M,hq,order_at_girth hq free heads pairs live,free,sub,size,one,fun u hu v hv w hw => cycle_head pairs hq free sub size one
    hu (outN_subset hv) (outN_subset hw) (mem_outN.mp hv).2 (mem_outN.mp hw).2⟩

#print axioms cycle_head
#print axioms shortest_cycle_heads
#print axioms order_from_ball
#print axioms order_at_girth
end LeanCH.BR.Closure.ClosedHeadIntersection
