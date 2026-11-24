import checkpoints.shen_extension.TwoCutReplacement
import checkpoints.shen_extension.CanonicalCycleLaw

namespace LeanCH.BR.Closure.TwoCutParentBanks
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse PunctureParentFlow
open scoped Matrix

/-- Weight of actual parents of y which miss z. -/
def exclusive {V : Finset ℕ} (E : CH.Digraph) (w : V→ℝ) (y z : V) :=
  ∑i : V, if E i y=true ∧ E i z=false then w i else 0

def Coupled {V : Finset ℕ} (q : ℕ) (E : CH.Digraph) (M : Matrix V V ℝ)
    (p u v : V→ℝ) (c : ℝ) (S T : Finset V) : Prop :=
  ∃a b : ℝ,∃s : V→ℝ,0<a ∧ 0<b ∧ (∀i,0≤s i) ∧ a+b+(∑i,s i)=1 ∧
    (∀i,p i=a*u i+b*v i+(s ᵥ* M) i) ∧
    ∃y∈S,∃z∈T,s y=0 ∧ s z=0 ∧
      c-1+a*u z≤(q:ℝ)*a*(exclusive E u y z-exclusive E u z y) ∧
      c-1+b*v y≤(q:ℝ)*b*(exclusive E v z y-exclusive E v y z) ∧
      c-1≤(q:ℝ)*exclusive E p y z ∧ c-1≤(q:ℝ)*exclusive E p z y

private theorem column {q : ℕ} {E : CH.Digraph} {V : Finset ℕ} (w : V→ℝ) (j : V) :
    (w ᵥ* realMatrix q E V) j=w j+(q:ℝ)*∑i : V,if E i j=true then w i else 0 := by
  classical
  change (∑i : V,w i*realMatrix q E V i j)=_
  simp_rw [realMatrix_entry,mul_add]
  rw [sum_add_distrib,mul_sum]
  congr 1
  · simp [mul_ite]
  · exact sum_congr rfl fun i _ => by cases E i j <;> simp [mul_comm]

private theorem contrast {q : ℕ} {E : CH.Digraph} {V : Finset ℕ} (w : V→ℝ) (y z : V) :
    (w ᵥ* realMatrix q E V) y-(w ᵥ* realMatrix q E V) z=
      w y-w z+(q:ℝ)*(exclusive E w y z-exclusive E w z y) := by
  rw [column,column]
  have part : (∑i : V,if E i y=true then w i else 0)-(∑i : V,if E i z=true then w i else 0)=
      exclusive E w y z-exclusive E w z y := by
    unfold exclusive
    rw [←sum_sub_distrib,←sum_sub_distrib]
    exact sum_congr rfl fun i _ => by cases E i y <;> cases E i z <;> simp
  linarith only [congrArg (fun t : ℝ => (q:ℝ)*t) part]

/-- Any independently chosen singleton certificates and any two prescribed
disjoint-block certificates can be used on this same graph and equalizer. -/
theorem on_source {q E V} (free : QFree E V q) (small : SmallerSmallRow q V.card) (two : 2≤V.card)
    {x p : ℕ→ℚ} {c : ℚ} (high : 1<c) (xp : ∀i∈V,0<x i) (xm : mass V x=1) (pm : mass V p=1)
    (rows : ∀i∈V,WeightedSD.row q E V x i=c) (cols : ∀i∈V,WeightedSD.col q E V p i=c)
    {M : Matrix V V ℝ} (cert : Punctures (realMatrix q E V) M)
    {S T : Finset V} (hs : S.Nonempty) (ht : T.Nonempty) (sep : Disjoint S T)
    {u v : V→ℝ} (cu : CutCertificate (realMatrix q E V) Sᶜ u)
    (cv : CutCertificate (realMatrix q E V) Tᶜ v) :
    Coupled q E M (fun i : V => (p i:ℝ)) u v (c:ℝ) S T := by
  classical
  let R := realMatrix q E V
  let pv := fun i : V => (p i:ℝ)
  obtain ⟨unit,l,lp,lm,mix,_,_⟩ := (laws free small two high xp xm pm rows cols).2 M cert
  have off (i j : V) (ij : i≠j) := (cert i).columns j (mem_erase.mpr ⟨ij.symm,mem_univ _⟩)
  have ua (i) (out : i∉S) := cu.columns i (mem_compl.mpr out)
  have va (i) (out : i∉T) := cv.columns i (mem_compl.mpr out)
  obtain ⟨a,b,s,ap,bp,sn,norm,recov,y,ys,z,zt,syz,szz,uy,vz⟩ :=
    TwoCutReplacement.replace_two R M unit (fun i => (cert i).mass) off pv l lp lm
      (funext mix) (by exact_mod_cast high : (1:ℝ)<c) (realMatrix_rational_columns p c cols)
      S T hs ht sep u v cu.mass cv.mass ua va
  have zeroU : u y=0 := cu.outside y (fun h => (mem_compl.mp h) ys)
  have zeroV : v z=0 := cv.outside z (fun h => (mem_compl.mp h) zt)
  have U := ua z (disjoint_right.mp sep zt)
  have W := va y (disjoint_left.mp sep ys)
  have diff {i j : V} {w : V→ℝ} {a : ℝ} (ap : 0<a) (low : (c:ℝ)-1≤a*((w ᵥ* R) i-1))
      (upper : (w ᵥ* R) j≤1) (zero : w i=0) :
      (c:ℝ)-1+a*w j≤(q:ℝ)*a*(exclusive E w i j-exclusive E w j i) := by
    have e := contrast (q:=q) (E:=E) w i j
    rw [zero] at e
    change (w ᵥ* R) i-(w ᵥ* R) j=_ at e
    nlinarith only [low,mul_le_mul_of_nonneg_left upper ap.le,congrArg (fun t : ℝ => a*t) e]
  have du := diff ap uy U zeroU
  have dv := diff bp vz W zeroV
  have residual (i) : 0≤(s ᵥ* M) i := sum_nonneg (fun j _ => mul_nonneg (sn j) ((cert j).nonneg i))
  have mono {w : V→ℝ} {k : ℝ} (i j : V) (dom : ∀h,k*w h≤pv h) :
      k*exclusive E w i j≤exclusive E pv i j := by
    unfold exclusive
    rw [mul_sum]
    exact sum_le_sum fun h _ => by split_ifs <;> simp_all only [mul_zero,le_refl]
  have eu := mono y z (fun h => (le_add_of_nonneg_right (mul_nonneg bp.le (cv.nonneg h))).trans
    ((le_add_of_nonneg_right (residual h)).trans_eq (recov h).symm))
  have ev := mono z y (fun h => (le_add_of_nonneg_left (mul_nonneg ap.le (cu.nonneg h))).trans
    ((le_add_of_nonneg_right (residual h)).trans_eq (recov h).symm))
  have bankNon (w : V→ℝ) (nn : ∀i,0≤w i) (i j : V) : 0≤exclusive E w i j :=
    sum_nonneg (fun h _ => by split_ifs <;> first | exact nn h | exact le_rfl)
  refine ⟨a,b,s,ap,bp,sn,norm,recov,y,ys,z,zt,syz,szz,du,dv,?_,?_⟩
  · nlinarith only [du,mul_nonneg ap.le (cu.nonneg z),
      mul_nonneg (mul_nonneg (Nat.cast_nonneg q : (0:ℝ)≤q) ap.le) (bankNon u cu.nonneg z y),
      mul_le_mul_of_nonneg_left eu (Nat.cast_nonneg q : (0:ℝ)≤q)]
  · nlinarith only [dv,mul_nonneg bp.le (cv.nonneg y),
      mul_nonneg (mul_nonneg (Nat.cast_nonneg q : (0:ℝ)≤q) bp.le) (bankNon v cv.nonneg y z),
      mul_le_mul_of_nonneg_left ev (Nat.cast_nonneg q : (0:ℝ)≤q)]

#print axioms on_source
end LeanCH.BR.Closure.TwoCutParentBanks
