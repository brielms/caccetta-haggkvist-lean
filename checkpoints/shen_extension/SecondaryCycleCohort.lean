import checkpoints.shen_extension.PhysicalCycleStockReplay
namespace LeanCH.BR.SecondaryCycleCohort
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking ShellCycleSupply

/-- A low root with equally wide first and second shells can use its
second shell as the first-shell bank of an actual child. Its near and
far cohort payments then use the very same physical cycle. -/
theorem cohort {D V q r u} (free : QFree D V q) (hq : 4≤q) (hr : 5≤r)
    (fit : r≤q+1) (reg : OutEq r D V) (uv : u∈V)
    (ys : (N2 D V u).card=r) (zs : (N3 D V u).card+1=r) :
    (∃s∈outN D V u,outN D V s=N2 D V u ∧ N2 D V s=N3 D V u ∧
      (ball D V s 3).card+r≤(ball D V u 4).card ∧
      ∀y∈N2 D V u,Rooted D V y (N2 D V u) ∧
        ∀k,k+2≤q → k+2+((ball D V s (k+2)).card-(ball D V s 1).card)≤(ball D V y (k+1)).card) ∨
    ∀w∈outN D V u,Rooted D V w (outN D V u) ∧
      4+r+((ball D V u 4).card-(ball D V u 2).card)≤(ball D V w 3).card := by
  rcases equal_rows_marked free hq hr fit reg uv ys zs with ⟨s,sm,row,_,three⟩|first
  · left
    have sv := outN_subset sm
    have all := EqualShellEscape.flat_exit free hq hr fit reg uv ys zs
    have bank : exterior D V (N2 D V u)=N3 D V u := by
      ext z
      constructor
      · intro hit
        obtain ⟨seen,off⟩ := mem_sdiff.mp hit
        obtain ⟨y,ym,edge⟩ := mem_biUnion.mp seen
        exact (mem_union.mp ((all y ym).1 edge)).resolve_left off
      · intro zm
        obtain ⟨y,ym⟩ := card_pos.mp (by omega : 0<(N2 D V u).card)
        exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨y,ym,mem_outN.mpr ⟨N3_subV zm,(all y ym).2 z zm⟩⟩,
          fun zy=>(mem_N3.mp zm).2 (mem_N2.mp zy).1⟩
    have nextBank := head_exterior free (by omega) sv
    rw [row,bank] at nextBank
    have supply := narrow_supply free hq reg sv fit (show (N2 D V s).card+1=r by rw [←nextBank]; exact zs)
    rw [row] at supply
    exact ⟨s,sm,row,nextBank.symm,three,supply⟩
  · exact Or.inr first

/-- With the earlier radius small, a child outside the low-score cohort
supplies a quantitative third-ball contribution at every labelled cycle
row. The threshold is a freely chosen score, and the two radii are explicit. -/
theorem large_child {D V q r s k b a} {C : Finset ℕ} (free : QFree D V q) (reg : OutEq r D V)
    (sv : s∈V) (small : (ball D V s 3).card≤a) (time : k+2≤q)
    (high : b≤(ball D V s 3).card+(ball D V s (k+2)).card)
    (stock : ∀y∈C,∀j,j+2≤q → j+2+((ball D V s (j+2)).card-(ball D V s 1).card)≤(ball D V y (j+1)).card)
    (hq : 4≤q) : ∀y∈C,b+k+2≤(ball D V y (k+1)).card+a+(r+1) := by
  have one := card_B1 (free.mono_bound hq) sv
  rw [reg s sv] at one
  intro y ym
  have bound := stock y ym k time
  omega

attribute [aesop safe forward (immediate := [free,hq,hr,fit,reg,uv,ys,zs]) (rule_sets := [CHGraphFamilies])] cohort
attribute [aesop safe forward (immediate := [free,reg,sv,small,time,high,stock,hq]) (rule_sets := [CHGraphFamilies])] large_child
ch_family_split_result cohort
#print axioms cohort
#print axioms large_child
end LeanCH.BR.SecondaryCycleCohort
