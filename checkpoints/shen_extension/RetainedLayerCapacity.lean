import checkpoints.shen_extension.RetainedRadiusLayers

namespace LeanCH.BR.RetainedLayerCapacity
open Finset BRq2 BRq3 BR45 BRsGen RetainedMixedCapacity RetainedRadiusLayers

/-- A sink in the actual second layer sends all its heads into the third
layer if the second layer has no return to the first. -/
theorem sink_expansion {D V q r u} (free : QFree D V q) (hq : 4 ≤ q) (root : u∈V)
    (degree : ∀x∈V,r ≤ (outN D V x).card) (live : (N2 D V u).Nonempty)
    (fits : (N2 D V u).card ≤ q)
    (no : ∀y∈N2 D V u,∀x∈outN D V u,D y x≠true) :
    ∃y∈N2 D V u,outN D V y⊆N3 D V u ∧ r ≤ (N3 D V u).card := by
  obtain ⟨y,ym,sink⟩ := exists_sink (free.mono_set (fun _ m=>N2_subV m)) live fits
  have sub : outN D V y⊆N3 D V u := by
    intro z zm
    obtain ⟨zv,yz⟩ := mem_outN.mp zm
    rcases headY (free.mono_bound hq) root ym zv yz with yz'|third
    · rcases mem_union.mp yz' with first|second
      · exact (no y ym z first yz).elim
      · exact (sink z second yz).elim
    · exact third
  exact ⟨y,ym,sub,(degree y (N2_subV ym)).trans (card_le_card sub)⟩

/-- Count three sets of *the same* rows in the punctured ball W of radius k.
Rows within a steps retain all their heads. Rows within b steps retain their
entire native j-ball. Scores and radii are free parameters. -/
theorem prefix_three_scores {D V q v k a b i j l h r d base high near}
    (free : QFree D V q) (root : v∈V) (time : k+1 ≤ q) (radii : i+l ≤ q)
    (full : a+1 ≤ k) (inside : b ≤ a) (reach : b+j ≤ k) (left : j ≤ i) (right : j ≤ l)
    (degree : ∀x∈V,r ≤ (outN D V x).card)
    (reserve : d+(ball D V v (k+1) \ ball D V v k).card ≤ r)
    (nearby : ∀x∈(ball D V v b).erase v,h ≤ (ball D V x j).card) (gain : near ≤ 2*h)
    (scores : ∀W : Finset ℕ,QFree D W q → (∀x∈W,d ≤ (outN D W x).card) →
      ∀x∈W,base ≤ (ball D W x i).card+(ball D W x l).card ∧
        (r ≤ (outN D W x).card → high ≤ (ball D W x i).card+(ball D W x l).card)) :
    let W := (ball D V v k).erase v
    let A := (ball D V v a).erase v
    let B := (ball D V v b).erase v
    (W.card-A.card)*base+(A.card-B.card)*high+B.card*near ≤ W.card*(W.card+1) := by
  dsimp only
  let W := (ball D V v k).erase v
  let A := (ball D V v a).erase v
  let B := (ball D V v b).erase v
  let score := fun x => (ball D W x i).card+(ball D W x l).card
  have aw : A⊆W := erase_subset_erase v (ball_mono_radius (by omega : a ≤ k))
  have ba : B⊆A := erase_subset_erase v (ball_mono_radius inside)
  have ff := free.mono_set (show W⊆V from (erase_subset _ _).trans ball_subset)
  have localScore := scores W ff (minOut_prefix_erase free root time degree reserve)
  have hn (x) (xm : x∈B) : near ≤ score x :=
    gain.trans ((Nat.mul_le_mul_left 2 (nearby x xm)).trans
      (two_scores free root xm reach (by omega : k ≤ q) left right))
  have hh (x) (xm : x∈A) : high ≤ score x := by
    apply (localScore x (aw xm)).2
    exact (degree x (ball_subset (mem_of_mem_erase xm))).trans (card_le_card
      ((outN_prefix_erase_root free root (by omega : a+1 ≤ q) (mem_of_mem_erase xm)).trans
        (outN_mono (erase_subset_erase v (ball_mono_radius full)) x)))
  have count := strata (f:=score) aw ba (Subset.rfl : B⊆B)
    (fun x xm=>(localScore x xm).1) hh hn hn
  simpa only [Nat.sub_self,Nat.zero_mul,Nat.add_zero] using
    count.trans (weighted_rows ff radii (score:=score) (fun _ _=>le_rfl))

attribute [aesop safe forward (immediate := [free,hq,root,degree,live,fits,no])
  (rule_sets := [CHGraphFamilies])] sink_expansion
attribute [aesop safe forward (immediate := [free,root,time,radii,full,inside,reach,left,right,degree,reserve,nearby,gain,scores])
  (rule_sets := [CHGraphFamilies])] prefix_three_scores

#print axioms sink_expansion
#print axioms prefix_three_scores
end LeanCH.BR.RetainedLayerCapacity
