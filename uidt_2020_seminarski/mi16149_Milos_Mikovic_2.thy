theory seminarski_drugi

imports Complex_Main


begin

(* 
  2. Seminarski
  zadaci 5. 6. 7. sa linka : https://matematiranje.in.rs/III%20godina/6.nizovi/1.MATEMATICKA%20INDUKCIJA.pdf
  Svaki nosi po 10 poena

  S obzirom da imam poteskoca oko dokaza 6. zadatka , dodao sam dokaz prvog seminarskog rada
  
*)

(* zadatak 5 *)

lemma zadatak_5:
  fixes n :: nat
  shows "(11::nat) dvd 6^(2*n)+3^(n+2)+3^(n)"
proof(induction n)
case 0
  have "6 ^ (2 * 0) + 3 ^ (0 + 2) + 3 ^ 0 = (6::nat)^(0) + 3^(2)+(3::nat)^(0)" 
    using mult_0_right plus_nat.add_0 by presburger
  also have "... = 1 + 9 + 1" by auto
  also have "... = 11" by auto
  from this show ?case by auto
next
  case (Suc n)
  then show ?case
  proof-
  have "6 ^ (2 * Suc n) + 3 ^ (Suc n + 2) + 3 ^ Suc n = 6 ^ (2*(n+1)) + 3 ^ ((n+1)+2) + 3 ^ (n+1)" by auto
  also have "... = 6^(2*n + 2) + 3 ^ (n + 2 + 1) + 3^ (n+1)" by auto
  also have "... = (6::nat)^(2*(n::nat))*6^(2) + 3^(n+2)*3^(1) + 3 ^ (n) * 3^(1)"  by simp
  also have "... = 36*6^(2*n)+3*3^(n+2)+3*3^(n)" by auto
  also have "... = 36*6^(2*n) + (36-33)*3^(n+2) + (36-33)*3^(n)" by auto
  also have "... = 36*6^(2*n) + 36*3^(n+2)-33*3^(n+2) + 36*3^(n) - 33*3^(n)" by auto
  also have "... = 36*(6^(2*(n::nat)) + 3^(n+2) + 3^(n)) - (33::nat)*((3::nat)^(n+2) + 3^(n))" by auto
  finally show ?thesis using dvd_mult Suc by blast
qed
qed

(* Zadatak 6 *)

definition SumaN1_minus_sumaN :: "nat \<Rightarrow> real" where
  "SumaN1_minus_sumaN n = 1/(2*(2*n+1)*(n+1))"

primrec suma' :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "suma' 0 m = 0" | 
  "suma' (Suc n) m = 1 / (Suc n + m) + suma' n m"

definition suma :: "nat \<Rightarrow> real" where
  "suma n = suma' n n"

definition sumaSuc :: "nat \<Rightarrow> real" where
  "sumaSuc n = (suma n) + SumaN1_minus_sumaN n"



value "suma 3"
value "sumaSuc 2"
value "SumaN1_minus_sumaN 2"

lemma sumaSuc_vece_suma:
  fixes n :: nat
  assumes "n > 1"
  shows "suma (Suc n) \<ge> suma n"
  using assms
proof(induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  show ?case sorry
  (*
  have "suma (Suc (Suc n)) = suma' (Suc (Suc n)) (Suc (Suc n))" 
    using suma_def by blast
  also have "... = 1 / ((Suc (Suc n)) + (Suc (Suc n))) + suma' (Suc n) (Suc (Suc n))" 
    using suma'.simps(2) by blast
  also have "... =  1 / ((Suc (Suc n)) + (Suc (Suc n))) + (1 / (Suc n + (Suc (Suc n)))) + suma' n (Suc (Suc n))" 
    by simp
  *)
qed

lemma pomocnaLema:
  fixes n :: nat
  assumes "n > 1"
  shows "suma' n (Suc n) \<le> suma' n n"
  sorry

lemma zadatak_6:
  fixes n :: nat
  assumes "n > 1"
  shows "suma n > 13/24"
  using assms
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  show ?case sorry
(*
  Ako pokazem da  suma (Suc n) \<ge> suma n onda sledi da iz IH da suma (Suc n) \<ge> 13/24 cime smo dokazali teoremu.
  Lemom sumaSuc_vece_suma pokusavam da dokazem da suma (Suc n) \<ge> suma n.

  have "suma (Suc n) = suma' (Suc n) (Suc n)" 
    by (simp add: suma_def) 
  also have "... = 1 / (Suc n + Suc n) + suma' n (Suc n)" 
    by simp
  also have "... \<le>  1 / (Suc n + Suc n) + suma' n n" 
  *)
qed

  


(* Zadatak 7  *)

lemma pomocno_tvrdjenje_zadatak_7:
  fixes n :: nat
  assumes "n \<ge> 3"
  shows "2*n+1 < 2^n"
  using assms
proof (induction n)
  case 0
  then show ?case 
  by simp
next
  case (Suc n)
  show ?case
proof (cases "Suc n = 3")
  case True
  then show ?thesis by auto
next
  case False
   hence "n \<ge> 3"  
   using Suc
   by simp
  have "2 * (Suc n) + 1 = 2*(n+1) + 1" 
    by auto
  also have "... = 2*n + 3"
    by auto
  also have "... = 2*n + 1 + 2" by auto
  finally show ?thesis 
  using Suc.IH \<open>3 \<le> n\<close> by auto
qed
qed


lemma zadatak_7:
  assumes "n \<ge> 5"
  shows "2^n > n^2"
  using assms
proof (induction n)
case 0
then show ?case by auto
next
case (Suc n)
  show ?case
  proof (cases "Suc n = 5")
    case True
    then show ?thesis by auto
  next
    case False
    hence "n \<ge> 5" using Suc by auto
    have "(Suc n) ^ 2 = (n+1)*(n+1)"
      by (metis Suc_eq_plus1 power2_eq_square)
    also have "... = n^2 + 2*n + 1"
      by (simp add: power2_eq_square)
    from this have "2*n+1 < 2^n" using Suc(2) pomocno_tvrdjenje_zadatak_7[of n] by auto
    from this have "n^2 + 2*n + 1 < 2^n + 2^n" 
      using Suc.IH \<open>5 \<le> n\<close> by linarith
    finally show ?thesis 
    using \<open>(Suc n)\<^sup>2 = (n + 1) * (n + 1)\<close> \<open>(n + 1) * (n + 1) = n\<^sup>2 + 2 * n + 1\<close> \<open>n\<^sup>2 + 2 * n + 1 < 2 ^ n + 2 ^ n\<close> by auto
  qed
qed


(* Dodatak dokaz 1. seminarskog rada


  zadatak (3. razred A kategorija 4. zadatak) : https://imomath.com/srb/zadaci/2005_republicko.pdf
  resenje (46. strana pdf-a) : https://imomath.com/srb/zadaci/bilten2005.pdf
  
  Zadatak : Neka za pozitivne realne brojeve x i y vazi x^2 + y^3 \<ge> x^3 + y^4 ,
             dokazati da vazi x^3 + y^3 \<le> 2. 
 
  Resenje : Kako vazi y^2 + y^4 \<ge> 2*y^3 (dokazuje se lemom l1) koristeci uslov zadatka tj.
  x^2 + y^3 \<ge> x^3 + y^4 imamo da x^2 - x^3 \<ge> y^4 - y^3 \<ge> y^3 - y^2
  Takodje odavde imamo da vazi x^2 + y^2 \<ge> x^3 + y^3 koristeci prvi i poslednji deo gornje 
  nejednakosti (pokazano lemom l2). 
  Na kraju jos je potrebno dokazati da 2^(1/3)*(x^3+y^3)^(2/3) \<ge> x^2 + y^2 cime smo 
  dokazali teoremu (pokazujemo lemom l3).
  l1,l2,l3 treba objediniti i dokazati polazno tvrdjenje lemom "treci_razred_a_kategorija_4_zadatak"

 *)


lemma kvad_binoma_plus:
  fixes x :: real and y :: real
  shows "(x + y)^2 = x^(2) + 2*x*y + y^(2)"
  by (simp add: power2_sum)

lemma kvad_binoma_minus:
  fixes x :: real and y :: real
  shows "(x - y)^2 = x^(2) - 2*x*y + y^(2)"
  by (simp add: power2_diff)

lemma stepen:
  fixes n m :: nat and x :: real
  shows "(x^(n))^(m) = x^(n*m)"
  by (simp add: power_mult)

lemma kvad_binoma_univ:
  fixes x :: real and y ::real and n :: nat
  shows "(x^n + y^n)^2 = x^(2*n) + 2*x^n*y^n + y^(2*n)"
  using kvad_binoma_plus stepen by (auto simp add : algebra_simps)

lemma pomocna1:
  fixes x::real and y::real and z::real
  shows "x^(2)*(2*x) = 2*x^(3)" 
  by (simp add: power2_eq_square power3_eq_cube)

lemma pomocna2:
  fixes x::real and y::real and n::nat and z::real and k::nat
  shows "x^(n)*(x^(k) - y + z) = x^(n+k) - x^(n)*y + x^(n)*z"
  by (metis (no_types, hide_lams) add_diff_eq diff_add_cancel distrib_left power_add)


lemma l1:
  fixes y::real
  assumes "x > 0"
  assumes "y > 0"
  shows "y^(2) + y^(4) \<ge> 2*y^(3)"
proof-
   have "y^(2)*(y-(1::real))^(2) \<ge> 0" 
     by simp
   from this have "(y::real)^(2)*(y^(2) - 2*y^(1) + (1::real)) \<ge> 0" 
     using kvad_binoma_minus by auto
   from this have "y^(2)*y^(2) - y^(2)*(2*y^(1)) + y^(2)*(1::real) \<ge> 0" 
     by (simp add: pomocna2)
   from this have "y^(4) - 2*y^(3) + y^(2) \<ge> 0" 
     using pomocna1 by auto
   from this show "y^(2) + y^(4) \<ge> 2*y^(3)" 
     by auto
 qed



lemma l2:
  fixes x ::real and y::real
  assumes "y^(2) + y^(4) \<ge> 2*y^(3)"
  assumes "x^(2) + y^(3) \<ge> x^(3) + y^(4)"
  assumes "x > 0"
  assumes "y > 0"
  shows "x^2 + y^2 \<ge> x^3 + y^3"
proof-
  have "x^(2) - x^(3) \<ge> y^(4)-y^(3)" 
    using assms(2) by auto
  from this have "y^(4)-y^(3) \<ge> y^(3)-y^(2)"
    using assms(1) by auto
  from this `x^(2) - x^(3) \<ge> y^(4)-y^(3)` 
  show "x^2 + y^2 \<ge> x^3 + y^3" 
    by auto
qed

value "(2::real) powr 2"
value "(2::real)^2"


lemma l3:
  fixes x :: real and y :: real
  assumes "x \<ge> 0"
  assumes "y \<ge> 0"
  shows "(root 3 2) * (root 3 (x^3 + y^3))^2 \<ge> x^(2) + y^(2)"
  sorry
(*
  ovaj dokaz bi mogao da se uradi preko izvoda ali nemam dovoljno znanja o tome u issabelu 
  Tako da sam uzeo da ova lemma vazi...

Pokusaj dokaza...

proof-
  have "((root 3 2) * (root 3 ((x^3 + y^3) ^ 2)))^3 = (root 3 2)^3 * (root 3 ((x^3 + y^3) ^ 2)^3)" 
    by (simp add: power_mult_distrib)
  also have "... = 2 * (root 3 ((x^3 + y^3) ^ 2)^3)" 
    by simp
  also have "... = 2 * (x^3 + y^3) ^ 2" by simp
  also have "... = 2* (x^6 + 2*x^3*y^3 + y^6)" using kvad_binoma_univ by auto
  also have "... = 2*x^6 + 4*x^3*y^3 + 2*y^6" by auto
  also have "... \<ge> x^6 + 3*x^4*y^2 + 3*x^2*y^4 + y^6"
*)

lemma treci_razred_A_kategorija_4_zadatak:
  fixes x::real and y::real
  assumes "x^(2) + y^(3) \<ge> x^(3) + y^(4)"
  assumes "x > 0"
  assumes "y > 0"
  assumes "u = root 3 (x^3 + y^3)"
  assumes "v = root 3 2"
  assumes "u > 0"
  assumes "v > 0"
  shows "x^(3) + y^(3) \<le> 2"
proof-
  have "y^2 + y^4 \<ge> 2*y^3" using l1 
    using assms(3) by auto
  from this have "x^2 + y^2 \<ge> x^3 + y^3" using l2 
    using assms(1) by auto
  from this have "(root 3 2) * (root 3 (x^3 + y^3))^2 \<ge> x^(2) + y^(2)" 
    by (smt assms(2) assms(3) l3)
  from this have "(root 3 2) * (root 3 (x^3 + y^3))^2 \<ge> x^(3) + y^(3)" using l2 
    using \<open>2 * y ^ 3 \<le> y\<^sup>2 + y ^ 4\<close> assms(1) by linarith 
  from this have "(root 3 2) * (u powr 2) \<ge> u powr 3"  using assms
    by (simp add: real_root_mult)
  from this have "root 3 2 \<ge> (u powr 3)/(u powr 2)" 
    using assms(6) pos_divide_le_eq powr_gt_zero by blast
  from this have "root 3 2 \<ge> u powr (3 - 2)" 
    by (metis powr_diff) 
  from this have "root 3 2 \<ge> u powr 1" 
    by simp  
  from this have "root 3 2 \<ge> (root 3 (x^3+y^3))^1" using assms by auto
  from this show ?thesis using assms 
  by simp
qed



end
