import checkpoints.shen_extension.ThirdStripEndpoints
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! A ball-growth step with arbitrary source degree, comparison degree, and cutoff. -/
namespace LeanCH.BR.ShenStripTransfer
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip

/-- At three consecutive radii, compare the actual last two layers with the
prefix deficiency budget. The gap between source and comparison degree is j.
The three g's measure losses from the ideal ball size s*k+1. -/
theorem growth_from_prefix {D : CH.Digraph} {V : Finset ℕ} {s d j L k u g0 g1 g2 : ℕ}
    (hu : u ∈ V) (hd : d+j=s)
    (h0 : s*k+1 ≤ (ball D V u k).card+g0)
    (h1 : s*(k+1)+1 ≤ (ball D V u (k+1)).card+g1)
    (hslope : 2*g1≤j+g2+g0)
    (hkey : ((s:ℤ)-g1+g0)*((s:ℤ)-1-j-g2+g1) < (L:ℤ)-s*(k+1)+g1)
    (hzero : s*(k+2)≤L+g2)
    (supply : (ball D V u (k+2)).card+g2≤s*(k+2) →
      L≤(ball D V u (k+1)).card-1+(ball D V u (k+1) \ ball D V u k).card*
        (d+(ball D V u (k+2) \ ball D V u (k+1)).card-s)) :
    s*(k+2)+1 ≤ (ball D V u (k+2)).card+g2 := by
  let P := (ball D V u (k+1)).card
  let c := (ball D V u (k+1) \ ball D V u k).card
  let t := (ball D V u (k+2) \ ball D V u (k+1)).card
  have hc : c+(ball D V u k).card=P :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have ht : t+P=(ball D V u (k+2)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hpos : 1≤P := Finset.card_pos.mpr ⟨u,self_mem_ball hu⟩
  change s*(k+1)+1≤P+g1 at h1
  by_contra! hbad
  have hexp : s*(k+2)=s*(k+1)+s := by ring
  have hdef := supply (by omega)
  change L≤P-1+c*(d+t-s) at hdef
  by_cases hshort : t≤j
  · have he : d+t-s=0 := by omega
    rw [he,Nat.mul_zero,Nat.add_zero] at hdef
    omega
  let l := d+t-s
  have hl : l+j=t := by dsimp [l]; omega
  have hb : L+1≤P+c*l := by change L≤P-1+c*l at hdef; omega
  have hb' : t+P+g2≤s*(k+2) := by omega
  zify at hc hl hb hb' h0 h1 hslope
  let e : ℤ := P+ (g1:ℤ) - ((s:ℤ)*(k+1)+1)
  have he : 0≤e := by dsimp [e]; linarith
  have hcb : (c:ℤ)≤s-(g1:ℤ)+g0+e := by dsimp [e]; linarith
  have hlb : (l:ℤ)≤s-(1:ℤ)-j-g2+g1-e := by dsimp [e]; linarith
  have m1 := mul_le_mul_of_nonneg_right hcb (Int.natCast_nonneg l)
  have m2 := mul_le_mul_of_nonneg_left hlb (by linarith [Int.natCast_nonneg c] :
    0≤(s:ℤ)-g1+g0+e)
  have m3 := mul_nonneg he (by linarith : (0:ℤ)≤j+g2+g0-2*g1)
  dsimp [e] at m1 m2 m3
  nlinarith only [hb,hkey,m1,m2,m3,sq_nonneg ((P:ℤ)+g1-((s:ℤ)*(k+1)+1))]

/-- The original global order supplier for the three-radius transfer. -/
theorem growth_step {D : CH.Digraph} {V : Finset ℕ} {q s d j L k u g0 g1 g2 : ℕ}
    (order : ∀ F W, QFree F W q → (∀ v ∈ W, d ≤ (outN F W v).card) →
      W.Nonempty → L ≤ W.card)
    (hf : QFree D V q) (hm : ∀ v ∈ V, s ≤ (outN D V v).card) (hu : u ∈ V)
    (hd : d+j=s) (hk : k+2≤q)
    (h0 : s*k+1 ≤ (ball D V u k).card+g0)
    (h1 : s*(k+1)+1 ≤ (ball D V u (k+1)).card+g1)
    (hg : g1≤g2) (hslope : 2*g1≤j+g2+g0)
    (hkey : ((s:ℤ)-g1+g0)*((s:ℤ)-1-j-g2+g1) < (L:ℤ)-s*(k+1)+g1)
    (hzero : s*(k+2)≤L+g2) :
    s*(k+2)+1 ≤ (ball D V u (k+2)).card+g2 := by
  apply growth_from_prefix hu hd h0 h1 hslope hkey hzero
  intro bad
  have ht := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u)
    (show k+1≤k+2 by omega))
  rw [show s*(k+2)=s*(k+1)+s by ring] at bad
  exact prefix_deficiency_of_size order hf hu hk hm (by omega : d≤s) (by omega)

#print axioms growth_from_prefix
#print axioms growth_step
end LeanCH.BR.ShenStripTransfer
