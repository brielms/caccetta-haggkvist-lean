import checkpoints.shen_extension.OneSpareTurns

namespace LeanCH.BR.OneSpareGrowth
open Finset BRq2 BRq3 BR45

theorem turn_ball_lower {D V q u a b} (free : QFree D V q) (hq : 4≤q) (uv : u∈V)
    (ax : a∈outN D V u) (bx : b∈outN D V u) (ab : D a b=true)
    (allY : ∀y∈N2 D V u,D a y=true) :
    (N2 D V u).card+(N3 D V u).card+2+(outN D (outN D V u) b).card≤(ball D V a 2).card := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  let H := outN D X b
  have f4 := free.mono_bound hq
  have av := outN_subset ax
  have bv := outN_subset bx
  have ne : a≠b := fun eq=>n1 f4 av (eq ▸ ab)
  have zy : Disjoint Y Z := disjoint_left.mpr (fun _ ym zm=>(mem_N3.mp zm).2 (mem_N2.mp ym).1)
  have xx : Disjoint (Y∪Z) X := by
    apply disjoint_left.mpr
    intro x xm hit
    rcases mem_union.mp xm with y|z
    · exact (mem_N2.mp y).2 (X_B1 hit)
    · exact (mem_N3.mp z).2 (ball_mono_radius (by decide : 1≤2) (X_B1 hit))
  have hh : Disjoint ({a,b} : Finset ℕ) H := by
    apply disjoint_left.mpr
    intro x xm hx
    rcases mem_insert.mp xm with eq|h
    · subst x; exact n2 f4 av bv ab (mem_outN.mp hx).2
    · obtain rfl := mem_singleton.mp h; exact n1 f4 bv (mem_outN.mp hx).2
  let K := ({a,b} : Finset ℕ)∪H
  have dis := xx.mono_right (show K⊆X from union_subset (insert_subset ax (singleton_subset_iff.mpr bx)) outN_subset)
  have reach : (Y∪Z)∪K⊆ball D V a 2 := by
    apply union_subset (union_subset ?_ ?_) (union_subset ?_ ?_)
    · intro y ym
      exact ball_mono_radius (by decide : 1≤2) (ball_of_adj (N2_subV ym) (allY y ym))
    · intro z zm
      obtain ⟨y,ym,yz⟩ := third_parent uv zm
      exact ball_step (ball_of_adj (N2_subV ym) (allY y ym)) (N3_subV zm) yz
    · exact insert_subset (self_mem_ball av)
        (singleton_subset_iff.mpr (ball_mono_radius (by decide : 1≤2) (ball_of_adj bv ab)))
    · intro c cm
      exact ball_step (ball_of_adj bv ab) (outN_subset (mem_outN.mp cm).1) (mem_outN.mp cm).2
  have cap := card_le_card reach
  rw [card_union_of_disjoint dis,card_union_of_disjoint zy] at cap
  dsimp only [K] at cap
  rw [card_union_of_disjoint hh,card_pair ne] at cap
  simpa only [X,Y,Z,H,add_assoc] using cap

/-- If all returns land on c, the physical row of c needs at least three
heads in the first layer. Otherwise a row of the second layer could be
erased leaving degree two on too few labels. -/
theorem three_internal {D V q r u c} (free : QFree D V q) (hq : 4≤q) (uv : u∈V)
    (reg : OutEq r D V) (three : 3≤r) (room : r≤2*q) (cx : c∈outN D V u)
    (ySize : (N2 D V u).card+1=r) (zSize : (N3 D V u).card+2=r)
    (returns : ∀y∈N2 D V u,∀x∈outN D V u,D y x=true → x=c) :
    3≤(outN D (outN D V u) c).card := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  let A := outN D Y c
  have f4 := free.mono_bound hq
  have cv := outN_subset cx
  have yc : Y.card+1=r := ySize
  have zc : Z.card+2=r := zSize
  by_contra! few
  have split := reg c cv
  rw [outN_X_eq f4 uv cx,card_outN_union disjXY] at split
  have m : Y.card≤A.card+1 := by dsimp [Y,A]; omega
  have rest : (Y\A).card≤1 := by
    rw [card_sdiff_of_subset (outN_subset : A⊆Y)]
    change Y.card-A.card≤1
    exact Nat.sub_le_iff_le_add.mpr (by omega)
  have paid (y) (ym : y∈A) : 2≤(outN D A y).card := by
    have yY : y∈Y := outN_subset ym
    have cy := (mem_outN.mp ym).2
    have sub : outN D V y⊆outN D A y∪Z := by
      intro w wm
      obtain ⟨wv,yw⟩ := mem_outN.mp wm
      rcases headY f4 uv yY wv yw with hit|zm
      · rcases mem_union.mp hit with xm|inY
        · have eq := returns y yY w xm yw
          subst w
          exact (n2 f4 cv (N2_subV yY) cy yw).elim
        · by_cases inside : w∈A
          · exact mem_union_left _ (mem_outN.mpr ⟨inside,yw⟩)
          · -- An unpaid Y label is the only possible returner. If it
            -- never returns, work on the whole second layer instead.
            by_cases wc : D w c=true
            · exact (free c 3 (by decide) (by omega)
                (.step (N2_subV yY) cy (.step wv yw (.step cv wc (.refl c))))).elim
            · have no (t) (tm : t∈Y) : D t c≠true := by
                intro tc
                have off : t∉A := fun ta=>n2 f4 cv (N2_subV tm) (mem_outN.mp ta).2 tc
                have eq := card_le_one.mp rest w (mem_sdiff.mpr ⟨inY,inside⟩) t (mem_sdiff.mpr ⟨tm,off⟩)
                exact wc (eq.symm ▸ tc)
              have all (t) (tm : t∈Y) : 2≤(outN D Y t).card := by
                have lim : outN D V t⊆outN D Y t∪Z := by
                  intro j jm
                  rcases headY f4 uv tm (outN_subset jm) (mem_outN.mp jm).2 with h|z
                  · rcases mem_union.mp h with x|yy
                    · have eq := returns t tm j x (mem_outN.mp jm).2
                      exact (no t tm (eq ▸ (mem_outN.mp jm).2)).elim
                    · exact mem_union_left _ (mem_outN.mpr ⟨yy,(mem_outN.mp jm).2⟩)
                  · exact mem_union_right _ z
                have cap := (card_le_card lim).trans (card_union_le _ _)
                rw [reg t (N2_subV tm)] at cap
                omega
              have cap : 2*q+1≤Y.card := corB (by omega) (free.mono_set (fun _ (m : _∈Y)=>N2_subV m))
                all (card_pos.mp (by omega))
              omega
      · exact mem_union_right _ zm
    have cap := (card_le_card sub).trans (card_union_le _ _)
    rw [reg y (N2_subV yY)] at cap
    omega
  have cap : 2*q+1≤A.card := corB (by omega) (free.mono_set (fun _ (m : _∈A)=>N2_subV (outN_subset m)))
    paid (card_pos.mp (by omega))
  have size : A.card≤Y.card := card_le_card (outN_subset : A⊆Y)
  exact (show ¬2*q+1≤Y.card by omega) (cap.trans size)

theorem every_full_tall {D V q r u a} (free : QFree D V q) (hq : 4≤q) (uv : u∈V)
    (reg : OutEq r D V) (three : 3≤r) (room : r≤2*q) (ax : a∈outN D V u)
    (one : (outN D (outN D V u) a).card=1) (short : (N2 D V u).card+1=r)
    (floor : r≤(N3 D V u).card+2) (upper : ∀v∈V,(ball D V v 2).card≤2*r+1) :
    2*r<(ball D V a 2).card := by
  by_contra! small
  obtain ⟨b,ab⟩ := card_eq_one.mp one
  obtain ⟨c,bc,zsize,ret⟩ := propagate free hq uv reg short floor ax ab small
  have bm : b∈outN D (outN D V u) a := ab.symm ▸ mem_singleton_self b
  have cm : c∈outN D (outN D V u) b := bc.symm ▸ mem_singleton_self c
  have cx := outN_subset cm
  have bx := outN_subset bm
  have threeC := three_internal free hq uv reg three room cx short zsize ret
  have allY := sends_layer free hq uv reg short bx (by rw [bc,card_singleton])
  have lower := turn_ball_lower free hq uv bx cx (mem_outN.mp cm).2 allY
  have hi := upper b (outN_subset bx)
  omega

#print axioms turn_ball_lower
#print axioms three_internal
#print axioms every_full_tall
end LeanCH.BR.OneSpareGrowth
