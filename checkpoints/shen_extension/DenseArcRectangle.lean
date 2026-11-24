import checkpoints.shen_extension.RecursiveHeadTransition

namespace LeanCH.BR.Closure.DenseArc
open BRq2 BRq3 Finset

def middle (D : CH.Digraph) (V : Finset ℕ) (u y : ℕ) : Finset ℕ :=
  (outN D V u).filter (fun x => D x y=true)

private def entry (D : CH.Digraph) (u y : ℕ) : ℕ := if D u y then 1 else 0

private theorem row_sum (D : CH.Digraph) (V : Finset ℕ) (x) :
    ∑ y ∈ V, entry D x y = (outN D V x).card := by
  simp only [entry,outN,card_filter]

private theorem middle_sum (D : CH.Digraph) (V : Finset ℕ) (u y) :
    ∑ x ∈ V, entry D u x * entry D x y = (middle D V u y).card := by
  simp only [middle,outN,filter_filter,card_filter,entry]
  apply sum_congr rfl
  intro x _
  cases D u x <;> cases D x y <;> decide

/-- Count each transitive triangle at each of its three edges. The selected
arc maximizes the actual middle set over every labelled arc in the graph. -/
theorem dense_arc {D V} (safe : QFree D V 3) (someArc : ∃ u ∈ V, ∃ y ∈ V, D u y=true) :
    ∃ u ∈ V, ∃ y ∈ V, D u y=true ∧
      (∀ v ∈ V, ∀ z ∈ V, D v z=true → (middle D V v z).card ≤ (middle D V u y).card) ∧
      4*(∑ v ∈ V, (outN D V v).card) ≤ V.card*(V.card+3*(middle D V u y).card) := by
  classical
  let arcs := (V ×ˢ V).filter (fun p => D p.1 p.2=true)
  obtain ⟨u0,hu0,y0,hy0,e0⟩ := someArc
  have nz : arcs.Nonempty := ⟨(u0,y0),mem_filter.mpr ⟨mem_product.mpr ⟨hu0,hy0⟩,e0⟩⟩
  obtain ⟨⟨u,y⟩,uy,top⟩ := arcs.exists_max_image (fun p => (middle D V p.1 p.2).card) nz
  obtain ⟨uv,yv⟩ := mem_product.mp (mem_filter.mp uy).1
  have maxF (v) (vv : v ∈ V) (z) (zv : z ∈ V) (e : D v z=true) :
      (middle D V v z).card ≤ (middle D V u y).card :=
    top (v,z) (mem_filter.mpr ⟨mem_product.mpr ⟨vv,zv⟩,e⟩)
  refine ⟨u,uv,y,yv,(mem_filter.mp uy).2,maxF,?_⟩
  let a := entry D
  let f (v z x : ℕ) := a v z * (a v x * a x z)
  let g (v : ℕ) := ∑ x ∈ V, (a v x + a x v)
  let n := V.card
  let m := ∑ v ∈ V, ∑ z ∈ V, a v z
  let L := (middle D V u y).card
  let total := ∑ v ∈ V, ∑ z ∈ V, ∑ x ∈ V, f v z x
  have localCount (v) (vv : v ∈ V) (z) (zv : z ∈ V) (x) (xv : x ∈ V) :
      a v z * ((a v x+a x v)+(a z x+a x z)) ≤ a v z + f v z x + f v x z + f x z v := by
    have nd := digonfree safe (by decide : 2≤3) vv xv
    have nd' := digonfree safe (by decide : 2≤3) zv xv
    have nt (vz : D v z=true) (zx : D z x=true) (xv' : D x v=true) : False :=
      safe v 3 (by decide) (by decide) (.step zv vz (.step xv zx (.step vv xv' (.refl v))))
    cases h : D v z <;> cases i : D v x <;> cases j : D x v <;>
      cases k : D z x <;> cases l : D x z <;> simp_all [a,f,entry]
  have sumG : ∑ v ∈ V, g v = 2*m := by
    dsimp only [g,m]
    simp only [sum_add_distrib]
    rw [sum_comm (f:=fun v x => a x v)]
    omega
  have degreeSq : (∑ v ∈ V, (g v)^2) = ∑ v ∈ V, ∑ z ∈ V, a v z * (g v+g z) := by
    simp only [Nat.mul_add,sum_add_distrib]
    rw [sum_comm (f:=fun v z => a v z * g z),← sum_add_distrib]
    apply sum_congr rfl
    intro v _
    simp only [← sum_mul,← Nat.add_mul,g,sum_add_distrib,pow_two]
  have globalCount : (∑ v ∈ V, (g v)^2) ≤ n*m + 3*total := by
    have compare := sum_le_sum (fun v (vv : v ∈ V) => sum_le_sum (fun z (zv : z ∈ V) =>
      sum_le_sum (fun x (xv : x ∈ V) => localCount v vv z zv x xv)))
    have perm1 : (∑ v ∈ V, ∑ z ∈ V, ∑ x ∈ V, f v x z) = total :=
      sum_congr rfl (fun _ _ => sum_comm)
    have perm2 : (∑ v ∈ V, ∑ z ∈ V, ∑ x ∈ V, f x z v) = total := by
      calc
        _ = ∑ v ∈ V, ∑ x ∈ V, ∑ z ∈ V, f x z v := sum_congr rfl (fun _ _ => sum_comm)
        _ = ∑ x ∈ V, ∑ v ∈ V, ∑ z ∈ V, f x z v := sum_comm
        _ = total := sum_congr rfl (fun _ _ => sum_comm)
    have left (v z) : (∑ x ∈ V, a v z * ((a v x+a x v)+(a z x+a x z))) =
        a v z * (g v+g z) := by rw [← mul_sum,sum_add_distrib]
    have constant (v z) : ∑ _x ∈ V, a v z = n * a v z := sum_const_nat (fun _ _ => rfl)
    simp only [left,← degreeSq,sum_add_distrib,constant,← mul_sum,perm1,perm2] at compare
    change (∑ v ∈ V,(g v)^2) ≤ n*m + total + total + total at compare
    omega
  have tri : total ≤ m*L := by
    dsimp only [total,m]
    simp only [sum_mul]
    apply sum_le_sum
    intro v vv
    apply sum_le_sum
    intro z zv
    change (∑ x ∈ V, a v z * (a v x * a x z)) ≤ _
    rw [← mul_sum,middle_sum]
    by_cases vz : D v z=true
    · exact Nat.mul_le_mul_left _ (maxF v vv z zv vz)
    · simp [a,entry,vz]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq V g (fun _ => (1:ℕ))
  simp only [mul_one,one_pow,sum_const_nat,sumG] at cs
  have sq : (2*m)^2 ≤ n*(∑ v ∈ V,(g v)^2) := by simpa [n,Nat.mul_comm] using cs
  have ineq := sq.trans (Nat.mul_le_mul_left n (globalCount.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 3 tri) _)))
  have mPos : 0<m := by
    have h := single_le_sum (fun z (_ : z ∈ V) => Nat.zero_le (a u0 z)) hy0
    have i := single_le_sum (fun v (_ : v ∈ V) => Nat.zero_le (∑ z ∈ V, a v z)) hu0
    have one : a u0 y0=1 := by simp [a,entry,e0]
    dsimp only [m]; omega
  have mul : m*(4*m) ≤ m*(n*(n+3*L)) := by nlinarith only [ineq]
  have le := Nat.le_of_mul_le_mul_left mul mPos
  have count : m=∑ v ∈ V,(outN D V v).card := sum_congr rfl (fun v _ => row_sum D V v)
  rwa [count] at le

#print axioms dense_arc

theorem supply {D V s} (safe : QFree D V 3) (live : V.Nonempty) (pos : 0<s)
    (degree : ∀ v∈V, s ≤ (outN D V v).card) :
    ∃ u ∈ V, ∃ y ∈ V, D u y=true ∧
      (∀ v ∈ V, ∀ z ∈ V, D v z=true → (middle D V v z).card ≤ (middle D V u y).card) ∧
      4*s ≤ V.card+3*(middle D V u y).card := by
  obtain ⟨v,vv⟩ := live
  obtain ⟨z,zh⟩ := card_pos.mp (pos.trans_le (degree v vv))
  obtain ⟨u,uv,y,yv,e,top,bound⟩ := dense_arc safe ⟨v,vv,z,(mem_outN.mp zh).1,(mem_outN.mp zh).2⟩
  have sumDeg : V.card*s ≤ ∑ x∈V, (outN D V x).card := by
    simpa only [sum_const_nat] using (sum_le_sum degree)
  refine ⟨u,uv,y,yv,e,top,Nat.le_of_mul_le_mul_left ?_ (card_pos.mpr ⟨v,vv⟩)⟩
  calc V.card*(4*s) = 4*(V.card*s) := by ring
       _ ≤ 4*(∑ x∈V, (outN D V x).card) := Nat.mul_le_mul_left _ sumDeg
       _ ≤ _ := bound

#print axioms supply
end LeanCH.BR.Closure.DenseArc
