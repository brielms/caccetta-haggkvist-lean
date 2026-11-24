import checkpoints.shen_extension.ThinRowTurn
import checkpoints.shen_extension.BankReachTransfer
import LeanCH.BR.BRWeightedPathExposure
namespace LeanCH.BR.ThinRowTurn
open Finset BRq2 BRq3 BR45 BRsGen

/-- A path retaining the very same head bank has two disjoint windows.
If each two-ball is full, all heads of the common bank must lie in
the intersection of those windows' two-balls. -/
theorem common_window {D V X B Z q r} (free : QFree D V q) (hq : 5≤q)
    (xv : X⊆V) (bv : B⊆V) (xbz : Disjoint X (B∪Z)) (bz : Disjoint B Z)
    (db : B.card+1=r) (dz : Z.card+1=r) (f : ℕ→ℕ)
    (fx : ∀i,f i∈X) (edges : ∀i,D (f i) (f (i+1))=true)
    (common : ∀i,B⊆outN D V (f i)) (reach : ∀i,Z⊆ball D V (f i) 2)
    (size : ∀i,(ball D V (f i) 2).card≤2*r+1) :
    ∀b∈B,outN D V b⊆B∪Z := by
  classical
  let W := fun i=>(range 3).image (fun j=>f (i+j))
  have inj := WeightedSD.short_walk_index_injective free hq f (fun i _=>⟨xv (fx _),edges i⟩)
  have window i (hi : i≤3) : ball D V (f i) 2=W i∪(B∪Z) := by
    symm
    apply eq_of_subset_of_card_le
    · apply union_subset
      · intro a am
        obtain ⟨j,jm,rfl⟩ := mem_image.mp am
        have small := mem_range.mp jm
        have walk := walk_between (D:=D) (W:=V) (f:=f) (m:=i+j)
          (fun k _=>⟨xv (fx _),edges k⟩) (by omega : i ≤ i+j) le_rfl
        exact mem_ball.mpr ⟨xv (fx _),_,by omega,walk⟩
      · exact union_subset (fun a am=>ball_mono_radius (by decide : 1≤2)
          (ball_of_adj (bv am) (mem_outN.mp (common i am)).2)) (reach i)
    · have dis : Disjoint (W i) (B∪Z) := xbz.mono_left (by
          intro a am
          obtain ⟨j,_,rfl⟩ := mem_image.mp am
          exact fx _)
      have ci : (W i).card=3 := by
        apply (card_image_of_injOn (s:=range 3) (f:=fun j=>f (i+j)) ?_).trans (card_range 3)
        intro k km j jm eq
        have a := mem_range.mp km
        have b := mem_range.mp jm
        have eq' := inj (mem_range.mpr (by omega : i+k<5+1)) (mem_range.mpr (by omega : i+j<5+1)) eq
        omega
      rw [card_union_of_disjoint dis,card_union_of_disjoint bz,ci]
      have := size i
      omega
  have apart : Disjoint (W 0) (W 3) := by
    apply disjoint_left.mpr
    intro a am bm
    obtain ⟨k,km,ke⟩ := mem_image.mp am
    obtain ⟨j,jm,je⟩ := mem_image.mp bm
    have i := mem_range.mp km
    have j' := mem_range.mp jm
    have := inj (mem_range.mpr (by omega : 0+k<5+1)) (mem_range.mpr (by omega : 3+j<5+1)) (ke.trans je.symm)
    omega
  intro b bm a am
  have seen i : a∈ball D V (f i) 2 := ball_step
    (ball_of_adj (bv bm) (mem_outN.mp (common i bm)).2) (outN_subset am) (mem_outN.mp am).2
  have v := seen 0
  have w := seen 3
  rw [window 0 (by decide)] at v
  rw [window 3 (by decide)] at w
  by_contra no
  exact disjoint_left.mp apart ((mem_union.mp v).resolve_right no) ((mem_union.mp w).resolve_right no)

/-- Once the common bank is closed in B∪Z, one light row in Z supplies
its exterior heads. All of those heads, both banks, and four distinct
labels of the path occur within three steps of its first label. -/
theorem third_excess {D V X B Z q r} (free : QFree D V q) (hq : 5≤q)
    (xv : X⊆V) (bv : B⊆V) (zv : Z⊆V) (xbz : Disjoint X (B∪Z)) (bz : Disjoint B Z)
    (db : B.card+1=r) (dz : Z.card+1=r) (low : 2≤r) (room : r≤q+3)
    (degree : ∀v∈V,r≤(outN D V v).card) (f : ℕ→ℕ)
    (fx : ∀i,f i∈X) (edges : ∀i,D (f i) (f (i+1))=true)
    (common : ∀i,B⊆outN D V (f i)) (reach : ∀i,Z⊆ball D V (f i) 2)
    (size : ∀i,(ball D V (f i) 2).card≤2*r+1) :
    3*r+1≤(ball D V (f 0) 3).card := by
  classical
  have closed := common_window free hq xv bv xbz bz db dz f fx edges common reach size
  have near := BankReachTransfer.reaches_bank (k:=1) free (by omega) bv zv bz
    (fun v vm=>low.trans (degree v vm)) (fun v vm=>dz ▸ (degree v (bv vm)).trans
      (card_le_card (fun a (am : a∈outN D V v)=>mem_outN.mpr ⟨closed v vm am,(mem_outN.mp am).2⟩)))
    (by omega) (by omega) (by omega)
  obtain ⟨z,zm,light⟩ : ∃z∈Z,(outN D Z z).card≤1 := by
    by_contra! high
    have := corB (by omega : 1≤q) (free.mono_set zv) high (card_pos.mp (by omega))
    omega
  let A := (outN D V z)\Z
  let P := (range 4).image f
  have pathcard : P.card=4 := (card_image_of_injOn (WeightedSD.short_walk_index_injective free
    (by omega : 3≤q) f (fun i _=>⟨xv (fx _),edges i⟩))).trans (card_range 4)
  have ap : r≤A.card+1 := by
    have sub : outN D V z⊆A∪outN D Z z := by
      intro a am
      by_cases az : a∈Z
      · exact mem_union_right _ (mem_outN.mpr ⟨az,(mem_outN.mp am).2⟩)
      · exact mem_union_left _ (mem_sdiff.mpr ⟨am,az⟩)
    have := (card_le_card sub).trans (card_union_le _ _)
    have := degree z (zv zm)
    omega
  have first : P⊆X := by
    intro a am
    obtain ⟨i,_,rfl⟩ := mem_image.mp am
    exact fx _
  have dis : Disjoint (P∪(B∪Z)) A := by
    apply disjoint_left.mpr
    intro a am head
    have arc := (mem_outN.mp (mem_sdiff.mp head).1).2
    rcases mem_union.mp am with path|bank
    · obtain ⟨i,_,rfl⟩ := mem_image.mp path
      exact no_back_arc free (xv (fx _)) (reach i zm) (by omega) arc
    · rcases mem_union.mp bank with ab|az
      · obtain ⟨i,_,le,p⟩ := near a ab z zm
        exact no_back_arc free (bv ab) (mem_ball.mpr ⟨zv zm,i,le,p⟩ : z∈ball D V a 2) (by omega) arc
      · exact (mem_sdiff.mp head).2 az
  have all : (P∪(B∪Z))∪A⊆ball D V (f 0) 3 := by
    apply union_subset _ (fun a am=>ball_step (reach 0 zm) (outN_subset (mem_sdiff.mp am).1)
      (mem_outN.mp (mem_sdiff.mp am).1).2)
    apply union_subset _ (union_subset (fun a am=>ball_mono_radius (by decide : 1≤3)
      (ball_of_adj (bv am) (mem_outN.mp (common 0 am)).2)) (fun a am=>ball_mono_radius (by decide : 2≤3) (reach 0 am)))
    intro a am
    obtain ⟨i,im,rfl⟩ := mem_image.mp am
    have le := mem_range.mp im
    have walk := walk_between (D:=D) (W:=V) (f:=f) (m:=i)
      (fun k _=>⟨xv (fx _),edges k⟩) (by omega : 0 ≤ i) le_rfl
    exact mem_ball.mpr ⟨xv (fx _),_,by omega,walk⟩
  have cap := card_le_card all
  rw [card_union_of_disjoint dis,card_union_of_disjoint (xbz.mono_left first),card_union_of_disjoint bz,pathcard] at cap
  omega

attribute [aesop safe forward (immediate := [free,hq,xv,bv,xbz,bz,db,dz,f,fx,edges,common,reach,size]) (rule_sets := [CHGraphFamilies])] common_window
attribute [aesop safe forward (immediate := [free,hq,xv,bv,zv,xbz,bz,db,dz,low,room,degree,f,fx,edges,common,reach,size]) (rule_sets := [CHGraphFamilies])] third_excess
#print axioms common_window
#print axioms third_excess
end LeanCH.BR.ThinRowTurn
