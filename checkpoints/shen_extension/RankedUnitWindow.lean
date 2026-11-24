import checkpoints.shen_extension.RankedArcMenus

namespace LeanCH.BR.RankedUnitWindow
open Finset BRq2 BRq3 BR45 BRsub WeightedSD Closure RankedHeadChoices

/-- The unit-weight test at the edge of a regular degree window. If a row
    could afford no single lost head, pruning cannot improve its head bank.
    The equality and containment use the actual native forward balls. -/
theorem unit_window {q r : ℕ} {D : CH.Digraph} {V W : Finset ℕ}
    (hq : 2≤q) (ws : W⊆V) (reg : ∀i∈V,(outN D V i).card=r)
    (room : (V\W).card < 1+q*r)
    (noLoss : 1+q*r ≤ (V\W).card+q)
    (outer : V.card ≤ 1+q*r) :
    let U := V\W
    let safe := FlatPeelReach.interior D V U (q-1)
    heads q D U (fun _=>1) (q-2)=safe ∧
      ∀ E : CH.Digraph,(∀i j,E i j=true → D i j=true) →
        heads q E U (fun _=>1) (q-2)⊆safe := by
  classical
  intro U safe
  change 1+q*r≤U.card+q at noLoss
  have us : U⊆V := sdiff_subset
  have rowCount (G : CH.Digraph) (S : Finset ℕ) (v) :
      row q G S (fun _=>1) v = 1+q*((outN G S v).card:ℚ) := by
    simp [WeightedSD.row,outW_eq_mass,mass]
  have value (i) (iv : i∈V) : row q D V (fun _=>1) i = 1+q*(r:ℚ) := by
    rw [rowCount,reg i iv]
  have m : mass U (fun _=>1)=(U.card:ℚ) := by simp [mass]
  have paid {E : CH.Digraph} (sub : ∀i j,E i j=true → D i j=true) {i} (iu : i∈U)
      (strict : mass U (fun _=>1)<row q E U (fun _=>1) i) :
      outN D V i ⊆ outN E U i := by
    have enclosed : outN E U i ⊆ outN D V i := fun j jj=>
      mem_outN.mpr ⟨us (outN_subset jj),sub i j (mem_outN.mp jj).2⟩
    rw [m,rowCount] at strict
    have lt : U.card<1+q*(outN E U i).card := by exact_mod_cast strict
    have full : r≤(outN E U i).card := by
      by_contra! less
      have le := Nat.mul_le_mul_left q (Nat.succ_le_of_lt less)
      rw [Nat.mul_succ] at le
      omega
    exact (Finset.eq_of_subset_of_card_le enclosed ((reg i (us iu)) ▸ full)).symm.subset
  have bound (E : CH.Digraph) (sub : ∀i j,E i j=true → D i j=true) :
      heads q E U (fun _=>1) (q-2) ⊆ safe := by
    intro h hk
    obtain ⟨hu,all⟩ := mem_filter.mp hk
    have lift (l) (short : l≤q-1) (j) (p : Walk D V h j l) : j∈U ∧ Walk E U h j l := by
      induction l generalizing j with
      | zero =>
        cases p
        exact ⟨hu,.refl _⟩
      | succ l ih =>
        obtain ⟨i,path,jv,ij⟩ := p.unsnoc
        obtain ⟨iu,ep⟩ := ih (by omega) i path
        have rowOk := all i (mem_ball.mpr ⟨iu,l,by omega,ep⟩)
        have edge := mem_outN.mp (paid sub iu rowOk.1 (mem_outN.mpr ⟨jv,ij⟩))
        exact ⟨edge.1,ep.snoc edge.1 edge.2⟩
    refine mem_filter.mpr ⟨us hu,fun j hit=>?_⟩
    obtain ⟨_,l,short,p⟩ := mem_ball.mp hit
    exact (lift l short j p).1
  refine ⟨Subset.antisymm (bound D (fun _ _ e=>e)) ?_,bound⟩
  intro h hs
  obtain ⟨hv,stays⟩ := mem_filter.mp hs
  have hu := stays (self_mem_ball hv)
  refine mem_filter.mpr ⟨hu,fun i ib=>?_⟩
  have iu := ball_subset ib
  have rad : q-2+1=q-1 := by omega
  have off := (avoid_iff (k:=q-2) ws hu).mpr (by simpa only [rad] using stays) i ib
  have loss : outW D W (fun _=>1) i=0 := sum_eq_zero (fun z zw=>by simp [off z zw])
  have tests (j) (ju : j∈U) := FreshMenuExitRules.ranked_costs (w:=fun _=>1)
    (by omega : 0<q) ws (value i (us iu)) (value j (us ju))
  have strict : (U.card:ℚ)<1+q*(r:ℚ) := by exact_mod_cast room
  have net : (W.card:ℚ) ≤ 1+q*(r:ℚ)-U.card := by
    have split := card_sdiff_add_card_eq_card ws
    have le : W.card+U.card≤1+q*r := by dsimp [U]; omega
    have le' : (W.card:ℚ)+U.card≤1+q*(r:ℚ) := by exact_mod_cast le
    linarith
  refine ⟨(tests i iu).1.mpr (by rw [loss,mul_zero]; change 0<1+q*(r:ℚ)-mass U _; rw [m]; linarith),
    fun j ju=>(tests j ju).2.mpr ?_⟩
  rw [loss,mul_zero,zero_add,outW_eq_mass]
  change mass (outN D W j) (fun _=>1) ≤ 1+q*(r:ℚ)-mass U _
  rw [m]
  exact (mass_mono outN_subset (fun _ _=>(by decide : (0:ℚ)≤1))).trans (by simpa [mass] using net)

structure WindowLaw (q r : ℕ) (D : CH.Digraph) (V : Finset ℕ) : Prop where
  tests : ∀W⊆V, (V\W).card < 1+q*r → 1+q*r ≤ (V\W).card+q → V.card ≤ 1+q*r →
    let U := V\W
    let safe := FlatPeelReach.interior D V U (q-1)
    heads q D U (fun _=>1) (q-2)=safe ∧ ∀ E : CH.Digraph,(∀i j,E i j=true → D i j=true) →
      heads q E U (fun _=>1) (q-2)⊆safe

@[aesop safe forward (immediate := [hq,reg]) (rule_sets := [CHGraphFamilies])]
theorem register {q r D V} (hq : 2≤q) (reg : ∀i∈V,(outN D V i).card=r) :
    WindowLaw q r D V := ⟨fun _ ws room noLoss upper=>unit_window hq ws reg room noLoss upper⟩

#print axioms unit_window
#print axioms register
end LeanCH.BR.RankedUnitWindow
