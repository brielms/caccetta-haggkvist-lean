import checkpoints.shen_extension.LocalBallTransfer
import checkpoints.shen_extension.OneSpareTightRow

namespace LeanCH.BR.GuardedLayerGrowth
open Finset BRq2 BRq3 BR45 BRsGen OneSpareGrowth

/-- An actual return y→x would close through a reachable one-head row
feeding y. The number of forbidden labels follows from the radius. -/
theorem no_return {D V q r u k} (free : QFree D V q) (hq : 4≤q) (uv : u∈V)
    (reg : OutEq r D V) (two : 2≤r) (short : (N2 D V u).card+1=r)
    (time : k+2≤q) (room : r≤2*q) (pressure : r<2*k+3) :
    ∀y∈N2 D V u,∀x∈outN D V u,D y x≠true := by
  intro y ym x xm edge
  let X := outN D V u
  have sz : X.card=r := reg u uv
  obtain ⟨b,bm,one⟩ := LocalBallTransfer.reach_light free (by omega)
    (outN_subset : X⊆V) xm (fun v vm=>two.trans (reg v vm).ge)
    (fun v vm=>internal_positive free hq uv reg short vm) (sz.le.trans room)
    (by omega) (by omega : X.card<2*k+3)
  obtain ⟨bx,j,len,walk⟩ := mem_ball.mp bm
  have byArc := sends_layer free hq uv reg short bx one y ym
  exact free x _ (by omega) (by omega) (((walk.mono outN_subset).snoc (N2_subV ym) byArc).snoc (outN_subset xm) edge)

/-- Removing all first-layer returns costs each second-layer row at
most the size of the third layer. Apply degree two on those same rows. -/
theorem guarded_third {D V q r u k} (free : QFree D V q) (hq : 4≤q) (uv : u∈V)
    (reg : OutEq r D V) (two : 2≤r) (short : (N2 D V u).card+1=r)
    (time : k+2≤q) (room : r≤2*q) (pressure : r<2*k+3) :
    r≤(N3 D V u).card+1 := by
  have no := no_return free hq uv reg two short time room pressure
  by_contra! low
  have rows (y) (ym : y∈N2 D V u) : 2≤(outN D (N2 D V u) y).card := by
    have sub : outN D V y⊆outN D (N2 D V u) y ∪ N3 D V u := by
      intro z zm
      have e := (mem_outN.mp zm).2
      rcases headY (free.mono_bound hq) uv ym (outN_subset zm) e with hit|last
      · rcases mem_union.mp hit with x|yy
        · exact (no y ym z x e).elim
        · exact mem_union_left _ (mem_outN.mpr ⟨yy,e⟩)
      · exact mem_union_right _ last
    have bound := (card_le_card sub).trans (card_union_le _ _)
    rw [reg y (N2_subV ym)] at bound
    omega
  have bound := corB (by omega : 1≤q) (free.mono_set (fun _ (m : _∈N2 D V u)=>N2_subV m))
    rows (card_pos.mp (by omega))
  omega

/-- Mixed local rank in a punctured second ball. Every first-layer row
keeps its original heads. Only the next frontier can be lost. -/
theorem fragment_budget {D V q r u t} (free : QFree D V q) (hq : 4≤q) (uv : u∈V)
    (reg : OutEq r D V) (room : r≤2*q) (two : 2≤t) (rank : t≤q)
    (loss : t+(N3 D V u).card≤r) :
    let m := ((ball D V u 2).erase u).card
    2*(r*(r+t)+(m-r)*(2*t+1))≤m*(m+1) := by
  let X := outN D V u
  let W := (ball D V u 2).erase u
  have wv : W⊆V := (erase_subset u _).trans ball_subset
  have xw : X⊆W := by
    rw [show X=(ball D V u 1).erase u from (erase_ball_one_eq_outN free (by omega) uv).symm]
    exact erase_subset_erase _ (ball_mono_radius (by decide : 1≤2))
  have floor := minOut_prefix_erase free uv (by omega : 2+1≤q) (fun v vm=>(reg v vm).ge) loss
  have full (v) (vm : v∈X) : (outN D W v).card=r := by
    have same : outN D W v=outN D V v := Subset.antisymm (outN_mono wv _)
      (outN_prefix_erase_root free uv (by omega : 1+1≤q) (X_B1 vm))
    rw [same,reg v (outN_subset vm)]
  have cap := marked_capacity (free.mono_set wv) hq two rank floor xw full room
  simpa only [show X.card=r from reg u uv] using cap

#print axioms no_return
#print axioms guarded_third
#print axioms fragment_budget
end LeanCH.BR.GuardedLayerGrowth
