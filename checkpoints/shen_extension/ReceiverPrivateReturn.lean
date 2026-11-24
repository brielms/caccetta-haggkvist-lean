import checkpoints.shen_extension.ReceiverRemoteBalance

namespace LeanCH.BR.BoundaryTightParentReach
open Finset BRq2 BRq3 BR45 BypassRepair LabelledCompromiseRecipe AvoidedHeadQuota

@[ch_numeric_guard] def ParentWindow (q d M : ℕ) : Prop :=
  let t:=(d-1)/q
  let c:=2*d-(M+2*t+1)
  c+2≤t ∧ d≤q*(t-c)+c+t

instance {q d M} : Decidable (ParentWindow q d M) := by unfold ParentWindow; infer_instance

/-- A native two-step target outside the reconstructed row supplies a tight
parent reached at the exact depth, retaining the actual intermediary z. -/
theorem private_walk {D V H Y q t g z b} (free : QFree D V q) (cut : 3≤q)
    (hv : H⊆V) (yv : Y⊆V) (gm : g∈H) (zm : z∈Y) (bm : b∈H)
    (gz : D g z=true) (zb : D z b=true) (off : D g b≠true)
    (rec : remote D H q t g=outN D H g)
    (rows : ∀a∈H,(Y\outN D V a).card+t=(outN D H a).card+1) :
    ∃a∈tight D H t g, Walk D H b a (q-2) ∧ Y\outN D V a={z} := by
  classical
  have ne : b≠g := fun e=>digonfree free (by omega) (hv gm) (yv zm) gz (e ▸ zb)
  have no : b∉remote D H q t g := fun m=>off (mem_outN.mp (rec ▸ m)).2
  have clash : ¬ Disjoint (ball D H b (q-2)) (tight D H t g) :=
    fun dis=>no (mem_filter.mpr ⟨mem_erase.mpr ⟨ne,bm⟩,dis⟩)
  obtain ⟨a,reach,am⟩ := not_disjoint_iff.mp clash
  obtain ⟨ah,ag,deg⟩ := mem_filter.mp am
  obtain ⟨_,k,cap,w⟩ := mem_ball.mp reach
  have orig := w.mono hv
  have len : k=q-2 := by
    by_contra diff
    exact free a (k+1+1+1) (by omega) (by omega)
      (.step (hv gm) ag (.step (yv zm) gz (.step (hv bm) zb orig)))
  have noHead : D a z≠true := fun az=>free a (k+1+1) (by omega) (by omega)
    (.step (yv zm) az (.step (hv bm) zb orig))
  have inside : {z}⊆Y\outN D V a := singleton_subset_iff.mpr
    (mem_sdiff.mpr ⟨zm,fun hit=>noHead (mem_outN.mp hit).2⟩)
  have debit := rows a ah
  exact ⟨a,am,len ▸ w,(eq_of_subset_of_card_le inside (by rw [card_singleton]; omega)).symm⟩

/-- Reconstruct the marked full row from its tight parents, or identify a
second full row. The number of omitted shell incidences is a free input. -/
theorem receiver_fork {D V q d t v g M} (free : QFree D V q) (cut : 3≤q)
    (vm : v∈V) (reg : OutEq d D V) (mult : d=q*t+1)
    (br : Compose.Boundary.BoundaryRegular q t)
    (lower : ∀k,2≤k → k≤t → NoHost q k ∧ LoneRow.NoNearHost q k)
    (one : (ball D V v 2\ball D V v 1).card+t=d+1) (gm : g∈outN D V v)
    (full : (ball D V v 2\ball D V v 1)⊆outN D V g)
    (floor : M≤∑a∈outN D V v,((ball D V v 2\ball D V v 1)\outN D V a).card)
    (window : let c:=2*d-(M+2*t+1); c+2≤t ∧ d≤q*(t-c)+c+t) :
    let H:=outN D V v
    let Y:=ball D V v 2\ball D V v 1
    (∃a∈H,a≠g ∧ Y⊆outN D V a) ∨
      (remote D H q t g=outN D H g ∧ ∀z∈Y,∀b∈H,D z b=true → D g b≠true →
        ∃a∈tight D H t g,Walk D H b a (q-2) ∧ Y\outN D V a={z}) := by
  classical
  let H:=outN D V v
  let Y:=ball D V v 2\ball D V v 1
  change Y.card+t=d+1 at one
  have rows a (am : a∈H) : (Y\outN D V a).card+t=(outN D H a).card+1 := by
    have id := missing_count free (by omega) vm am (reg a (outN_subset am))
    change (Y\outN D V a).card+d=Y.card+(outN D H a).card at id
    omega
  by_cases otherFull : ∃a∈H,a≠g ∧ Y⊆outN D V a
  · exact Or.inl otherFull
  have short := rows g gm
  rw [sdiff_eq_empty_iff_subset.mpr full,card_empty] at short
  have other a (am : a∈H) (ne : a≠g) : t≤(outN D H a).card := by
    have positive : 0<(Y\outN D V a).card := by
      by_contra! zero
      exact otherFull ⟨a,am,ne,sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp (by omega))⟩
    have := rows a am
    omega
  have size : H.card=d := reg v vm
  have eq := remote_exact (fun a=>(Y\outN D V a).card) (free.mono_set (show H⊆V from outN_subset)) cut gm
    (size.trans mult) br (by omega) other rows floor (size ▸ window) lower
  exact Or.inr ⟨eq,fun z zm b bm zb off=>private_walk free cut outN_subset
    (show Y⊆V from sdiff_subset.trans ball_subset) gm zm bm (mem_outN.mp (full zm)).2 zb off eq rows⟩

#print axioms private_walk
#print axioms receiver_fork
end LeanCH.BR.BoundaryTightParentReach
