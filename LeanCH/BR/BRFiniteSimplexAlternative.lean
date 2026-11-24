import LeanCH.BR.BRFiniteRationalFeasibility

/-! Rectangular simplex separation, with exact descent of closed rational
feasibility before the real compact minimax argument is applied. -/
namespace LeanCH.BR.FiniteDual
open Finset
universe u v
variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]

def rectPayoff (B : I→J→ℝ) (w : J→ℝ) (l : I→ℝ) : ℝ :=
  ∑i,l i*(∑j,B i j*w j)

theorem rectPayoff_transpose (B : I→J→ℝ) (w : J→ℝ) (l : I→ℝ) :
    rectPayoff B w l=∑j,w j*(∑i,l i*B i j) := by
  simp only [rectPayoff,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro i _
  ring

theorem exists_rect_saddle [Nonempty I] [Nonempty J] (B : I→J→ℝ) :
    ∃w∈simplex,∃l∈simplex,∀z∈simplex,∀r∈simplex,
      rectPayoff B w r≤rectPayoff B z l := by
  classical
  have hx (l : I→ℝ) : (fun w=>rectPayoff B w l)=linearEval (fun j=>∑i,l i*B i j) := by
    funext w
    exact rectPayoff_transpose B w l
  have hy (w : J→ℝ) : (fun l=>rectPayoff B w l)=linearEval (fun i=>∑j,B i j*w j) := rfl
  have contJ (c : J→ℝ) : Continuous (linearEval c) := by
    change Continuous (fun x:J→ℝ=>∑j,x j*c j)
    fun_prop
  have contI (c : I→ℝ) : Continuous (linearEval c) := by
    change Continuous (fun x:I→ℝ=>∑i,x i*c i)
    fun_prop
  exact Sion.exists_isSaddlePointOn simplex_nonempty simplex_convex simplex_compact
    (fun l _=>by rw [hx]; exact (contJ _).lowerSemicontinuous.lowerSemicontinuousOn simplex)
    (fun l _=>by rw [hx]; exact ((linearEval _).convexOn simplex_convex).quasiconvexOn)
    simplex_convex simplex_nonempty simplex_compact
    (fun w _=>by rw [hy]; exact (contI _).upperSemicontinuous.upperSemicontinuousOn simplex)
    (fun w _=>by rw [hy]; exact ((linearEval _).concaveOn simplex_convex).quasiconcaveOn)

theorem real_simplex_strict_separator [Nonempty I] [Nonempty J] (B : I→J→ℝ)
    (hno : ¬∃w∈simplex,∀i,0≤∑j,B i j*w j) :
    ∃l∈simplex,∀j,(∑i,l i*B i j)<0 := by
  classical
  obtain ⟨w,hw,l,hl,hs⟩ := exists_rect_saddle (fun i j=>-B i j)
  have hex : ∃i,(∑j,B i j*w j)<0 := by
    by_contra hn
    push Not at hn
    exact hno ⟨w,hw,hn⟩
  obtain ⟨i,hi⟩ := hex
  refine ⟨l,hl,?_⟩
  intro j
  have h := hs (point j) (point_mem j) (point i) (point_mem i)
  have he : (∑k,l k*B k j)≤∑k,B i k*w k := by
    simpa [rectPayoff,point,neg_mul,mul_neg,sum_neg_distrib] using h
  exact he.trans_lt hi

theorem rational_simplex_feasible (A : I→J→ℚ) (b : I→ℚ) (x : J→ℝ)
    (hx : x∈simplex) (hr : ∀i,(b i:ℝ)≤∑j,(A i j:ℝ)*x j) :
    ∃y : J→ℚ,(∀j,0≤y j) ∧ (∑j,y j)=1 ∧ ∀i,b i≤∑j,A i j*y j := by
  classical
  let C : (I ⊕ (J ⊕ Bool))→J→ℚ := fun e j=>
    match e with
    | .inl i => -A i j
    | .inr (.inl k) => if j=k then -1 else 0
    | .inr (.inr h) => if h then 1 else -1
  let d : (I ⊕ (J ⊕ Bool))→ℚ := fun e=>
    match e with
    | .inl i => -b i
    | .inr (.inl _) => 0
    | .inr (.inr h) => if h then 1 else -1
  have hreal : ∀e,(∑j,(C e j:ℝ)*x j)≤(d e:ℝ) := by
    intro e
    rcases e with i | k | h
    · simpa [C,d,neg_mul,sum_neg_distrib] using hr i
    · have he (j : J) : (C (.inr (.inl k)) j : ℝ) = if j=k then -1 else 0 := by
        by_cases hj : j=k <;> simp [C,hj]
      simp_rw [he]
      simpa [d] using hx.1 k
    · cases h <;> simp [C,d,hx.2]
  obtain ⟨y,hy⟩ := rational_weak_feasible C d x hreal
  refine ⟨y,?_,?_,?_⟩
  · intro j
    simpa [C,d] using hy (.inr (.inl j))
  · have hu := hy (.inr (.inr true))
    have hl := hy (.inr (.inr false))
    simp [C,d,sum_neg_distrib] at hu hl
    linarith
  · intro i
    simpa [C,d,neg_mul,sum_neg_distrib] using hy (.inl i)

theorem rational_simplex_strict_separator [Nonempty J] (B : I→J→ℚ)
    (hno : ¬∃w : J→ℚ,(∀j,0≤w j) ∧ (∑j,w j)=1 ∧ ∀i,0≤∑j,B i j*w j) :
    ∃l : I→ℝ,(∀i,0≤l i) ∧ (∑i,l i)=1 ∧ ∀j,(∑i,l i*(B i j:ℝ))<0 := by
  classical
  have hreal : ¬∃w∈simplex,∀i,0≤∑j,(B i j:ℝ)*w j := by
    rintro ⟨w,hw,hr⟩
    obtain ⟨y,hy,hm,hrows⟩ := rational_simplex_feasible B (fun _=>0) w hw (by simpa using hr)
    exact hno ⟨y,hy,hm,hrows⟩
  cases isEmpty_or_nonempty I with
  | inl hI =>
    letI := hI
    exact False.elim (hreal ⟨point (Classical.arbitrary J),point_mem _,fun i=>isEmptyElim i⟩)
  | inr hI =>
    letI := hI
    obtain ⟨l,hl,hsep⟩ := real_simplex_strict_separator (fun i j=>(B i j:ℝ)) hreal
    exact ⟨l,hl.1,hl.2,hsep⟩

theorem rational_demand_strict_separator [Nonempty J]
    (R : I→J→ℚ) (d : I→ℚ) (P : ℚ) (hP : 0≤P)
    (hno : ¬∃α : J→ℚ,(∀j,0≤α j) ∧ (∑j,α j)=P ∧ ∀i,d i≤∑j,R i j*α j) :
    ∃l : I→ℝ,(∀i,0≤l i) ∧ (∑i,l i)=1 ∧
      ∀j,(P:ℝ)*(∑i,l i*(R i j:ℝ)) < ∑i,l i*(d i:ℝ) := by
  classical
  have hn : ¬∃w : J→ℚ,(∀j,0≤w j) ∧ (∑j,w j)=1 ∧
      ∀i,0≤∑j,(P*R i j-d i)*w j := by
    rintro ⟨w,hw,hm,hr⟩
    apply hno
    refine ⟨fun j=>P*w j,fun j=>mul_nonneg hP (hw j),by simp [← mul_sum,hm],?_⟩
    intro i
    have he : (∑j,(P*R i j-d i)*w j) = (∑j,R i j*(P*w j))-d i := by
      simp only [sub_mul,sum_sub_distrib,← mul_sum,hm,mul_one]
      congr 1
      apply sum_congr rfl
      intro j _
      ring
    have hri := hr i
    rw [he] at hri
    exact sub_nonneg.mp hri
  obtain ⟨l,hl,hm,hs⟩ := rational_simplex_strict_separator (fun i j=>P*R i j-d i) hn
  refine ⟨l,hl,hm,?_⟩
  intro j
  have he : (∑i,l i*((P*R i j-d i:ℚ):ℝ)) =
      (P:ℝ)*(∑i,l i*(R i j:ℝ)) - ∑i,l i*(d i:ℝ) := by
    simp only [Rat.cast_sub,Rat.cast_mul,mul_sub,sum_sub_distrib,mul_sum]
    congr 1
    apply sum_congr rfl
    intro i _
    ring
  exact sub_neg.mp (he ▸ hs j)

end LeanCH.BR.FiniteDual
