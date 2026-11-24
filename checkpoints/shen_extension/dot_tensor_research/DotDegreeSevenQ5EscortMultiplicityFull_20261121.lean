import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5EscortMultiplicity_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5Order34_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

/-- The common core can be empty only when all seven possible omissions
occur. The seven actual second successors and six other heads then
give the same score charge, without overcharging the empty core. -/
theorem sharedEscort_all_seven_score
    {D : CH.Digraph} {V J : Finset ℕ} {c : ℕ}
    {s a : ℕ→ℕ} {T : ℕ→Finset ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (hc : c∈V)
    (P : SharedEscortMarks D V (outN D V c) J s a T) (j7 : J.card=7) :
    43≤(ball D V c 2).card+(ball D V c 3).card ∧ ∀ i∈J, 7≤(T i).card := by
  classical
  let X := outN D V c
  let Y := J.image s
  let W := J.image a
  have yX : Y⊆X := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    exact P.sMem i hi
  have yJ : Y.card=J.card := card_image_of_injOn P.sInj
  have yEq : Y=X := eq_of_subset_of_card_le yX (by rw [yJ,j7,ho c hc])
  have indep (x) (hx : x∈X) (y) (hy : y∈X) : D x y≠true := by
    have h : y∈Y := yEq.symm ▸ hy
    obtain ⟨i,hi,rfl⟩ := mem_image.mp h
    exact P.avoidS i hi x hx
  have wJ : W.card=J.card := by
    apply card_image_of_injOn
    intro i hi j hj e
    by_contra ne
    have mem := P.aOther i hi j hj ne
    rw [e] at mem
    exact P.aNot j hj mem
  have hsupport (i j : ℕ) (hi : i∈J) (hj : j∈J) (neq : i≠j) :
      outN D V (s j)⊆T i := by
    intro x hx
    have jX : s j∈X := P.sMem j hj
    have ne : s j≠s i := fun e => neq (P.sInj hj hi e).symm
    rcases mem_union.mp (P.support i hi (s j) jX ne hx) with xX|xT
    · exact (indep (s j) jX x xX (mem_outN.mp hx).2).elim
    · exact xT
  obtain ⟨h,hh⟩ := card_pos.mp (by omega : 0<J.card)
  let Z := (outN D V (s h)).erase (a h)
  have z6 : Z.card=6 := by
    have mem : a h∈outN D V (s h) := mem_outN.mpr ⟨P.aV h hh,P.aArc h hh⟩
    have hV := (mem_outN.mp (P.sMem h hh)).1
    rw [show Z=(outN D V (s h)).erase (a h) from rfl,card_erase_of_mem mem,ho _ hV]
  have nz (i) (hi : i∈J) : a i∉Z := by
    intro ia
    have ne : i≠h := by
      intro e
      subst i
      exact (mem_erase.mp ia).1 rfl
    exact P.aNot i hi (hsupport i h hi hh ne (mem_of_mem_erase ia))
  have nW : Disjoint (insert c X) W := disjoint_left.mpr (by
    intro x hx xW
    obtain ⟨i,hi,rfl⟩ := mem_image.mp xW
    rcases mem_insert.mp hx with ce|inX
    · have sc : D (s i) c=true := ce ▸ P.aArc i hi
      have ⟨iv,cs⟩ := mem_outN.mp (P.sMem i hi)
      exact hf c 2 (by decide) (by decide) (.step iv cs (.step hc sc (.refl c)))
    · exact P.aOut i hi inX)
  have nZ : Disjoint (insert c X ∪ W) Z := disjoint_left.mpr (by
    intro x mx xz
    have e := (mem_outN.mp (mem_of_mem_erase xz)).2
    rcases mem_union.mp mx with ix|wx
    · rcases mem_insert.mp ix with xc|xx
      · have ⟨sv,cs⟩ := mem_outN.mp (P.sMem h hh)
        exact hf c 2 (by decide) (by decide) (.step sv cs (.step hc (xc ▸ e) (.refl c)))
      · exact indep _ (P.sMem h hh) _ xx e
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp wx
      exact nz i hi xz)
  have xin : insert c X⊆ball D V c 2 := by
    intro x hx
    rcases mem_insert.mp hx with rfl|xX
    · exact self_mem_ball hc
    · obtain ⟨xv,e⟩ := mem_outN.mp xX
      exact mem_ball.mpr ⟨xv,1,by decide,.step xv e (.refl x)⟩
  have win : W⊆ball D V c 2 := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    obtain ⟨sv,cs⟩ := mem_outN.mp (P.sMem i hi)
    exact mem_ball.mpr ⟨P.aV i hi,2,by decide,
      .step sv cs (.step (P.aV i hi) (P.aArc i hi) (.refl _))⟩
  have zin : Z⊆ball D V c 2 := by
    intro x hx
    obtain ⟨xv,e⟩ := mem_outN.mp (mem_of_mem_erase hx)
    obtain ⟨sv,cs⟩ := mem_outN.mp (P.sMem h hh)
    exact mem_ball.mpr ⟨xv,2,by decide,.step sv cs (.step xv e (.refl x))⟩
  have notCX : c∉X := by
    intro cx
    exact hf c 1 (by decide) (by decide) (.step hc (mem_outN.mp cx).2 (.refl c))
  have lower := card_le_card (union_subset (union_subset xin win) zin)
  rw [card_union_of_disjoint nZ,card_union_of_disjoint nW,card_insert_of_notMem notCX,
    wJ,j7,z6,ho c hc] at lower
  have large : 22≤(ball D V c 3).card := by
    by_contra! cap
    let U := ball D V c 2
    have sub : U⊆ball D V c 3 := ball_mono_radius (by decide)
    have cl := card_le_card sub
    change (ball D V c 2).card≤(ball D V c 3).card at cl
    have eq : U=ball D V c 3 := eq_of_subset_of_card_le sub (by change (ball D V c 3).card≤(ball D V c 2).card; omega)
    have deg (v) (hv : v∈U) : 7≤(outN D U v).card := by
      have keep : outN D V v⊆outN D U v := by
        intro x hx
        obtain ⟨xv,e⟩ := mem_outN.mp hx
        exact mem_outN.mpr ⟨eq.symm ▸ ball_step hv xv e,e⟩
      exact (ho v (ball_subset hv)).ge.trans (card_le_card keep)
    have n := five_free_ge35 (hf.mono_set ball_subset) deg ⟨c,self_mem_ball hc⟩
    change 35≤(ball D V c 2).card at n
    omega
  refine ⟨by omega,?_⟩
  intro i hi
  have pos : 0<(J.erase i).card := by rw [card_erase_of_mem hi,j7]; decide
  obtain ⟨j,jm⟩ := card_pos.mp pos
  obtain ⟨ne,hj⟩ := mem_erase.mp jm
  have n := card_le_card (hsupport i j hi hj ne.symm)
  rw [ho _ (mem_outN.mp (P.sMem j hj)).1] at n
  exact n

#print axioms sharedEscort_all_seven_score
end LeanCH.BR.DotDegreeSevenLow

