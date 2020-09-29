theory mi16315_Andjela_Janosevic
  imports Complex_Main
begin

text \<open>

Zadatak 2, drugi razred sa linka: https://imomath.com/srb/zadaci/RS_2016_republicko_resenja.pdf


Neka su x, y, z nenegativni brojevi takvi da je x+y+z = 1.
Dokazati da vazi nejednakost x^3 + y^3 + z^3 + 2*(x*y+y*z+z*x) \<ge> (3::real)/(4::real)
\<close>


text \<open>

Resenje:

  Pokazemo da je 2*(x*y+y*z+z*x) = 1 - x^2 - y^2 - z^2
  Tada je  x^3 + y^3 + z^3 + 1 - x^2 - y^2 - z^2  \<ge> 3/4 odnosno
  x^3 + y^3 + z^3 - x^2 - y^2 - z^2 + 1/4 \<ge> 0
  koristeci uslov x + y + z = 1:
   x^3 + y^3 + z^3 - x^2 - y^2 - z^2 + 1/4*(x+y+z) \<ge> 0
  dobijamo nejednakost x*(x - 1/2)^2 +  y*(y - 1/2)^2 +  z*(z - 1/2)^2  \<ge> 0
  Jednakost vazi ako su svi sabirci na levoj strani poslednje nejednakosti jednaki nuli
  tj. uz uslov x+y+z=1 ako je (x, y, z) \<in> {(1/2, 1/2, 0),(1/2, 0, 1/2),(0, 1/2, 1/2)}.

\<close>





text\<open> Pokazujemo da je 2*(x*y+y*z+z*x) = 1 - x^2 - y^2 - z^2\<close>


lemma pomocna:
  fixes x y z :: real
  assumes "x \<ge> 0" "y \<ge> 0" "z \<ge> 0"  " x + y + z = 1" 
  shows "y+z = 1-x " "x+y = 1-z" "x+z = 1-y"
  using  Groups.cancel_comm_monoid_add_class.add_implies_diff
proof -
  from assms(4) have "x + y = 1 - z" by auto
  from assms(4) have "x + z = 1 - y" by auto
  from assms(4) have "y + z = 1 - x" by auto
  from this `x + y = 1 - z` `x + z = 1 - y` show "y+z = 1-x " "x+y = 1-z" "x+z = 1-y" by auto
qed

 
thm Groups.cancel_comm_monoid_add_class.add_implies_diff
thm left_diff_distrib
thm  right_diff_distrib



lemma pomocna_lema_1:
  fixes x y z :: real
  assumes "x \<ge> 0" "y \<ge> 0" "z \<ge> 0"  " x + y + z = 1" 
  shows " 2*(x*y+y*z+z*x) = 1 - x^2 - y^2 - z^2 "
proof -
  have " 2*(x*y+y*z+z*x) = 2*x*y + 2*y*z + 2*z*x" by simp
  also have "... = x*y + x*y + y*z + y*z + z*x + z*x" by simp
 thm  distrib_left
  also have "... = x*(y+z) + x*y + y*z +y*z +z*x"  by (simp add: distrib_left) 
  also have "... = x*(y+z) + y*(x+z) + z*(x+y)"  by (simp add: distrib_left)
  also have "... = x*(1 - x) + y*(x+z) + z*(x+y) " using assms(4) pomocna
    by (metis (no_types, hide_lams) add_diff_cancel_left' add_diff_cancel_right diff_add_cancel)
  also have "... = x*(1 - x) + y*(1 - y) +  z*(1 - z) " using assms(4) pomocna
  proof -
    have "1 - z = x + y"
      by (metis assms(4) eq_diff_eq')
    then show ?thesis
      by force
  qed
thm  right_diff_distrib
  also have "... = x - x^2 + y*(1 - y) +  z*(1 - z) " using right_diff_distrib
    by (simp add: right_diff_distrib power2_eq_square)
  also have "... = x - x^2 + y - y^2 + z - z^2"  using right_diff_distrib
    by (simp add: right_diff_distrib power2_eq_square)
  also have "... = x + y + z - x^2 - y^2 - z^2" by simp
  also have "... = 1 - x^2 - y^2 - z^2" using assms(4) by simp
  finally show ?thesis by simp
  qed


text\<open>Sada treba pokazati da je  x^3 + y^3 + z^3 + 1 - x^2 - y^2 - z^2  \<ge> 3/4 \<close>



lemma pomocna_lema_:
  fixes x y z :: real
  assumes "x \<ge> 0" "y \<ge> 0" "z \<ge> 0"  " x + y + z = 1" 
  shows "x^3 + y^3 + z^3 + 1 - x^2 - y^2 - z^2  \<ge> 3/4"
  using assms
proof -
  have "x\<le>1" "y\<le>1" "z\<le>1" using assms
      apply linarith
    using assms(1) assms(3) assms(4) apply auto[1]
    using assms(1) assms(2) assms(4) by auto
  also have "x^2*(x-1) + y^2*(y-1) + z^2*(z-1) +1/4 \<ge>0" 
  proof-
    have "0\<le>x" "x\<le>1" "0\<le>y" "y\<le>1" "0\<le>z" "z\<le>1"
      apply (simp add: assms(1)) 
      apply (simp add: calculation(1)) 
      apply (simp add: assms(2))
      apply (simp add: calculation(2)) 
      apply (simp add: assms(3))
      by (simp add: calculation(3)) 
    also have "x-1 \<le>0" "y-1 \<le>0" "z-1\<le>0" using assms sledgehammer
  qed
qed




lemma lema1:
  fixes x y z :: real
  assumes  "x \<ge> 0" "y \<ge> 0" "z \<ge> 0"  " x + y + z = 1"  "x^3 + y^3 + z^3 + 1 - x^2 - y^2 - z^2  \<ge> 3/4"
  shows  "x^3 + y^3 + z^3 - x^2 - y^2 - z^2 + 1/4 \<ge>0"
  using assms(5) by linarith 
proof - 
  from assms(5) show "x^3 + y^3 + z^3 - x^2 - y^2 - z^2 + 1/4 \<ge>0" by auto
qed


lemma lema_kvadrat_binoma:
   fixes x :: real
   assumes "x \<ge> 0"
   shows  " (x - 1/2)^2 = x^2 - x + 1/4"
proof-
  have "(x-1/2)^2 = (x-1/2)*(x-1/2)" 
    by (simp add: power2_eq_square)
  also have "... = x*(x-1/2) - 1/2*(x-1/2)"
    by (simp add: left_diff_distrib) 
  also have "... = x^2 - 1/2*x  - 1/2*(x-1/2)"
    by (simp add: power2_eq_square right_diff_distrib)
  also have "... = x^2 - 1/2*x - 1/2*x + 1/2*1/2"   by (simp add: power2_eq_square right_diff_distrib)
  also have "... = x^2 -x + 1/4" by simp
  finally show ?thesis by simp
qed


text\<open>Sada pokazujemo  da je  x^3 + y^3 + z^3 + 1 - x^2 - y^2 - z^2  \<ge> 3/4
odnosno x^3 + y^3 + z^3 - x^2 - y^2 - z^2 + 1/4 \<ge>0 \<close>


lemma pomocna_lema_2:
  fixes x y z :: real
  assumes "x \<ge> 0" "y \<ge> 0" "z \<ge> 0"  " x + y + z = 1" 
  shows "x^3 + y^3 + z^3 + 1 - x^2 - y^2 - z^2  \<ge> 3/4"
  using assms sledgehammer
proof -
  have  "x^3 + y^3 + z^3 - x^2 - y^2 - z^2 + 1/4 \<ge>0"  using assms lema1 by blast
  also have "... = x^3 + y^3 + z^3 - x^2 - y^2 - z^2 + 1/4*(x+y+z)" using assms(4) by simp
  also have  "... = x^3 + y^3 + z^3 - x^2 - y^2 - z^2 + 1/4*x + 1/4*y + 1/4*z" by simp
  also have  "... = x*(x - 1/2)^2 +  y^3+ z^3 - y^2 - z^2  + 1/4*y + 1/4*z " using lema_kvadrat_binoma by blast
  also have "... =  x*(x - 1/2)^2 +  y*(y - 1/2)^2 +  z*(z - 1/2)^2" using lema_kvadrat_binoma by blast
  from this `x^3 + y^3 + z^3 - x^2 - y^2 - z^2 + 1/4 \<ge>0` have " x*(x - 1/2)^2 +  y*(y - 1/2)^2 +  z*(z - 1/2)^2  \<ge> 0"
    using calculation by linarith
  from this show  "x^3 + y^3 + z^3 + 1 - x^2 - y^2 - z^2  \<ge> 3/4" 
    using \<open>0 \<le> x ^ 3 + y ^ 3 + z ^ 3 - x\<^sup>2 - y\<^sup>2 - z\<^sup>2 + 1 / 4\<close> by linarith 
qed



  text\<open>Jednakost vazi ako su svi sabirci na levoj strani poslednje nejednakosti jednaki nuli
tj. uz uslov x+y+z=1 ako je (x, y, z) \<in> {(1/2, 1/2, 0),(1/2, 0, 1/2),(0, 1/2, 1/2)}. \<close>




lemma zadatak:
  fixes x y z :: real
  assumes "x \<ge> 0" "y \<ge> 0" "z \<ge> 0"  " x + y + z = 1" 
  shows "x^3 + y^3 + z^3 + 2*(x*y+y*z+z*x) \<ge> (3::real)/(4::real)"
  sorry





lemma zadatak:
  fixes x y z :: real
  assumes "x \<ge> 0" "y \<ge> 0" "z \<ge> 0"  " x + y + z = 1" 
  shows "x^3 + y^3 + z^3 + 2*(x*y+y*z+z*x) \<ge> (3::real)/(4::real)"
proof -
  have " 2*(x*y+y*z+z*x) = 1 - x^2 - y^2 - z^2 " using pomocna_lema_1 assms by auto
  from this  have  "x^3 + y^3 + z^3 + 1 - x^2 - y^2 - z^2  \<ge> 3/4" using  pomocna_lema_2 assms by auto
  from this have  " x*(x - 1/2)^2 +  y*(y - 1/2)^2 +  z*(z - 1/2)^2  \<ge> 0"  using  pomocna_lema_2 assms by auto


end



