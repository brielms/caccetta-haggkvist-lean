import checkpoints.shen_extension.ShortestCycleWeights

namespace LeanCH.BR.Closure.TwoCycleTransfer
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor ShenPrimeTransition ShortestCycleWeights

/-- The unique successor at a vertex of a genuine cycle. -/
noncomputable def succHead (D : CH.Digraph) (A : Finset ℕ) (u : ℕ) : ℕ := by
  classical
  exact if h : (outN D A u).Nonempty then (outN D A u).min' h else u

private theorem succ_mem {D V q A u} (c : Cycle D V q A) (ua : u∈A) :
    succHead D A u ∈ outN D A u := by
  have pos : (outN D A u).Nonempty := card_pos.mp (by rw [c.heads u ua]; decide)
  simpa only [succHead,dite_eq_left pos] using (outN D A u).min'_mem pos

private theorem succ_eq {D V q A u z} (c : Cycle D V q A) (ua : u∈A)
    (hz : z∈outN D A u) : succHead D A u = z :=
  card_le_one.mp (c.heads u ua).le _ (succ_mem c ua) _ hz

private theorem succ_inj {D V q A u v} (c : Cycle D V q A)
    (ua : u∈A) (va : v∈A) (same : succHead D A u=succHead D A v) : u=v := by
  obtain ⟨za,uz⟩ := mem_outN.mp (succ_mem c ua)
  have vz := (mem_outN.mp (succ_mem c va)).2
  rw [←same] at vz
  exact card_le_one.mp (c.incoming _ za).le _ (mem_inN.mpr ⟨ua,uz⟩) _ (mem_inN.mpr ⟨va,vz⟩)

/-- Shared tails whose successor on A disappears when A outside C is erased. -/
noncomputable def crossing (D : CH.Digraph) (A C : Finset ℕ) : Finset ℕ := by
  classical exact (A∩C).filter fun u => succHead D A u∈A\C

/-- Weight moved to z from deleted successors, along the prescribed cycle C. -/
noncomputable def deposit (D : CH.Digraph) (A C : Finset ℕ) (w : ℕ→ℕ) (z : ℕ) : ℕ :=
  ∑u∈crossing D A C, if succHead D C u=z then w (succHead D A u) else 0

/-- Deleted mass whose predecessor is also deleted. This is left out of the new total. -/
noncomputable def unused (D : CH.Digraph) (A C : Finset ℕ) (w : ℕ→ℕ) : ℕ :=
  ∑z∈(A\C)\((crossing D A C).image (succHead D A)), w z

theorem recipient_location {D V q A C u} (ca : Cycle D V q A) (cc : Cycle D V q C)
    (hu : u∈crossing D A C) : succHead D C u ∈ C\A := by
  obtain ⟨shared,gone⟩ := mem_filter.mp hu
  obtain ⟨ua,uc⟩ := mem_inter.mp shared
  obtain ⟨zc,uz⟩ := mem_outN.mp (succ_mem cc uc)
  refine mem_sdiff.mpr ⟨zc,?_⟩
  intro za
  have same := succ_eq ca ua (mem_outN.mpr ⟨za,uz⟩)
  exact (mem_sdiff.mp gone).2 (same ▸ zc)

/-- Each surviving successor receives exactly the weight of its paired deleted head. -/
theorem paired_deposit {D V q A C} (cc : Cycle D V q C) (w : ℕ→ℕ) {u}
    (hu : u∈crossing D A C) : deposit D A C w (succHead D C u) = w (succHead D A u) := by
  classical
  have uc := (mem_inter.mp (mem_filter.mp hu).1).2
  unfold deposit
  rw [sum_eq_single u]
  · simp
  · intro v hv ne
    have vc := (mem_inter.mp (mem_filter.mp hv).1).2
    exact ite_eq_right (fun eq => ne (succ_inj cc vc uc eq))
  · exact fun miss => (miss hu).elim

/-- Receipts plus the unused mass account for every removed unit. -/
theorem mass_balance {D V q A C} (ca : Cycle D V q A) (cc : Cycle D V q C) (w : ℕ→ℕ) :
    (∑z∈V\(A\C), (w z+deposit D A C w z))+unused D A C w = ∑z∈V,w z := by
  classical
  let Z := A\C
  let U := V\Z
  let B := crossing D A C
  let S := B.image (succHead D A)
  have zv : Z⊆V := sdiff_subset.trans ca.sub
  have sz : S⊆Z := by
    intro z zs
    obtain ⟨u,hu,rfl⟩ := mem_image.mp zs
    exact (mem_filter.mp hu).2
  have dest (u) (hu : u∈B) : succHead D C u ∈ U := by
    obtain ⟨zc,_⟩ := mem_sdiff.mp (recipient_location ca cc hu)
    exact mem_sdiff.mpr ⟨cc.sub zc,fun zdel => (mem_sdiff.mp zdel).2 zc⟩
  have inj : Set.InjOn (succHead D A) (B : Set ℕ) := by
    intro u hu v hv eq
    exact succ_inj ca (mem_inter.mp (mem_filter.mp hu).1).1 (mem_inter.mp (mem_filter.mp hv).1).1 eq
  have imageSum : (∑z∈S,w z) = ∑u∈B,w (succHead D A u) := sum_image inj
  have credits : (∑z∈U,deposit D A C w z) = ∑u∈B,w (succHead D A u) := by
    unfold deposit
    rw [sum_comm]
    apply sum_congr rfl
    intro u hu
    simp [dest u hu]
  have used := sum_sdiff sz (f:=w)
  have whole := sum_sdiff zv (f:=w)
  change (∑z∈U,w z)+(∑z∈Z,w z)=∑z∈V,w z at whole
  change (∑z∈U,(w z+deposit D A C w z))+(∑z∈Z\S,w z)=_
  rw [sum_add_distrib,credits,←imageSum]
  omega

private theorem paid_on_cycle {D V q A C p} (ca : Cycle D V q A) (cc : Cycle D V q C)
    (w : ℕ→ℕ) (pa : p∈A) (pu : p∈V\(A\C)) :
    (∑z∈outN D (A\C) p,w z) ≤ ∑z∈outN D (V\(A\C)) p,deposit D A C w z := by
  classical
  have pc : p∈C := by
    by_contra no
    exact (mem_sdiff.mp pu).2 (mem_sdiff.mpr ⟨pa,no⟩)
  by_cases any : (outN D (A\C) p).Nonempty
  · obtain ⟨s,hs⟩ := any
    obtain ⟨sz,ps⟩ := mem_outN.mp hs
    have same := succ_eq ca pa (mem_outN.mpr ⟨(mem_sdiff.mp sz).1,ps⟩)
    have single : outN D (A\C) p={s} := by
      ext z
      constructor
      · intro hz
        obtain ⟨zz,pz⟩ := mem_outN.mp hz
        exact mem_singleton.mpr ((succ_eq ca pa (mem_outN.mpr ⟨(mem_sdiff.mp zz).1,pz⟩)).symm.trans same)
      · intro eq
        exact mem_singleton.mp eq ▸ hs
    have cross : p∈crossing D A C := mem_filter.mpr ⟨mem_inter.mpr ⟨pa,pc⟩,same ▸ sz⟩
    obtain ⟨rc,edge⟩ := mem_outN.mp (succ_mem cc pc)
    have rg : succHead D C p∈outN D (V\(A\C)) p :=
      mem_outN.mpr ⟨mem_sdiff.mpr ⟨cc.sub rc,fun gone => (mem_sdiff.mp gone).2 rc⟩,edge⟩
    have bound := single_le_sum (f:=deposit D A C w) (fun _ _ => Nat.zero_le _) rg
    simpa only [single,sum_singleton,paired_deposit cc w cross,same] using bound
  · simp [not_nonempty_iff_eq_empty.mp any]

private theorem row_balance {q D V Z p} {w g : ℕ→ℕ} (zv : Z⊆V) :
    score q D (V\Z) (fun z => w z+g z) p+q*(∑z∈outN D Z p,w z) =
      score q D V w p+g p+q*(∑z∈outN D (V\Z) p,g z) := by
  have partition := sum_sdiff zv (f:=fun z => if D p z=true then w z else 0)
  have rows : (∑z∈outN D (V\Z) p,w z)+(∑z∈outN D Z p,w z)=∑z∈outN D V p,w z := by
    simpa only [outN,sum_filter] using partition
  have form (S : Finset ℕ) (v : ℕ→ℕ) : score q D S v p=v p+q*(∑z∈outN D S p,v z) := by
    simp only [score,outN,sum_filter]
  rw [form,form,sum_add_distrib,Nat.mul_add]
  have mul := congrArg (q * ·) rows
  simp only [Nat.mul_add] at mul
  omega

/-- The graph, weights, and the two cycles belong to the current strict state.
The model X supplies only its support, budget and minimality. -/
theorem transfer {q n} (X : Model q n) {D : CH.Digraph} {w : ℕ→ℕ} {A C : Finset ℕ}
    (free : QFree D X.V q) (positive : ∀z∈X.V,0<w z) (budget : (∑z∈X.V,w z)≤n)
    (strict : Strict q D X.V w) (ca : Cycle D X.V q A) (cc : Cycle D X.V q C) (ne : A≠C) :
    let Z := A\C
    let U := X.V\Z
    let g := deposit D A C w
    let F := unused D A C w
    Cycle D U q C ∧
    (∀u∈U, u∈A → (∑z∈U,(w z+g z)) < score q D U (fun z => w z+g z) u) ∧
    ∃p∈X.V\A, (∃z∈Z,D p z=true) ∧
      score q D U (fun z => w z+g z) p ≤ (∑z∈U,(w z+g z)) ∧
      score q D X.V w p+F+g p+q*(∑z∈outN D U p,g z) ≤
        (∑z∈X.V,w z)+q*(∑z∈outN D Z p,w z) := by
  classical
  intro Z U g F
  have zv : Z⊆X.V := sdiff_subset.trans ca.sub
  have cu : C⊆U := fun z zc => mem_sdiff.mpr ⟨cc.sub zc,fun gone => (mem_sdiff.mp gone).2 zc⟩
  have used := mass_balance ca cc w
  change (∑z∈U,(w z+g z))+F=∑z∈X.V,w z at used
  have paid (u) (uu : u∈U) (ua : u∈A) : (∑z∈U,(w z+g z))<score q D U (fun z => w z+g z) u := by
    have cover := Nat.mul_le_mul_left q (paid_on_cycle ca cc w ua uu)
    have bal := row_balance (q:=q) (D:=D) (w:=w) (g:=g) (p:=u) zv
    change score q D U (fun z => w z+g z) u+q*(∑z∈outN D Z u,w z) =
      score q D X.V w u+g u+q*(∑z∈outN D U u,g z) at bal
    change q*(∑z∈outN D Z u,w z)≤q*(∑z∈outN D U u,g z) at cover
    have old := nat_strict.mp strict u (mem_sdiff.mp uu).1
    omega
  have nz : Z.Nonempty := sdiff_nonempty.mpr (fun sub =>
    ne (eq_of_subset_of_card_le sub (cc.size.trans ca.size.symm).le))
  have len := card_sdiff_add_card_eq_card zv
  have fewer : U.card<X.V.card := by have := card_pos.mpr nz; dsimp [U]; omega
  obtain ⟨z,zc⟩ := card_pos.mp (show 0<C.card by rw [cc.size];omega)
  have fail : ¬Strict q D U (fun y => w y+g y) := fun h => fewer.not_ge
    (X.minimal D U _ ⟨z,cu zc⟩ (free.mono_set sdiff_subset)
      (fun v vu => (positive v (mem_sdiff.mp vu).1).trans_le (Nat.le_add_right _ _))
      ((by omega : (∑z∈U,(w z+g z))≤∑z∈X.V,w z).trans budget) h)
  rw [nat_strict] at fail
  push Not at fail
  obtain ⟨p,pu,low⟩ := fail
  have pa : p∉A := fun hit => low.not_gt (paid p pu hit)
  have bal := row_balance (q:=q) (D:=D) (w:=w) (g:=g) (p:=p) zv
  change score q D U (fun z => w z+g z) p+q*(∑z∈outN D Z p,w z) =
    score q D X.V w p+g p+q*(∑z∈outN D U p,g z) at bal
  have bill : score q D X.V w p+F+g p+q*(∑z∈outN D U p,g z) ≤
      (∑z∈X.V,w z)+q*(∑z∈outN D Z p,w z) := by omega
  have reaches : (outN D Z p).Nonempty := by
    by_contra no
    rw [not_nonempty_iff_eq_empty.mp no,sum_empty,Nat.mul_zero,Nat.add_zero] at bill
    have old := nat_strict.mp strict p (mem_sdiff.mp pu).1
    omega
  obtain ⟨y,hy⟩ := reaches
  exact ⟨⟨cu,cc.size,cc.heads,cc.incoming⟩,paid,p,mem_sdiff.mpr ⟨(mem_sdiff.mp pu).1,pa⟩,
    ⟨y,mem_outN.mp hy⟩,low,bill⟩

#print axioms recipient_location
#print axioms paired_deposit
#print axioms mass_balance
#print axioms transfer
end LeanCH.BR.Closure.TwoCycleTransfer
