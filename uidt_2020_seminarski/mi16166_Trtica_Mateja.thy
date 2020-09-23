theory mi16166_Trtica_Mateja
  imports Complex_Main
begin

text \<open>
Zadatak 1, treci razred.
Link: https://imomath.com/srb/zadaci/2014_okruzno.pdf
Tekst zadatka:
Neka su x,y,z realni brojevi takvi da vazi x+y+z=0. Dokazati da vazi nejednakost:

  6*(x^3 + y^3 + z^3)\<le> (x^2 + y^2 + z^2)^3
\<close>

lemma kub_binoma:
  fixes x y :: real
  assumes "x\<ge>0" "y\<ge>0"
  shows  "(-x-y)^3 =-(x^3)-3*(x^2)*y - 3*x*(y^2)- y^3" 
  using assms
proof-
have "(-x-y)^3 = (-x-y)*(-x-y)*(-x-y)" 
  by (simp add: power3_eq_cube)
  also have "... = (x*x+x*y+y*x+y*y)*(-x-y)"
    by (simp add: add.commute add_diff_eq mult.commute right_diff_distrib')
  also have "... = (x*x+x*y+y*x+y*y)*(-x) - (x*x+x*y+y*x+y*y)*y"
    using right_diff_distrib by blast
  also have "... = (-x)*x*x - x*y*x - y*x*x -  y*y*x - (x*x+x*y+y*x+y*y)*y"
    by (simp add: distrib_right)
  also have "... = -(x*x*x) - x*y*x - y*x*x - y*y*x - x*x*y - x*y*y - y*x*y -
y*y*y" 
    by (simp add: distrib_right left_diff_distrib)
  also have "... = -(x^3) - x*y*x - y*x*x - y*y*x - x*x*y - x*y*y - y*x*y - y^3"
    by (simp add: power3_eq_cube)
  also have "... = -(x^3) - 3*(x^2)*y - 3*(y^2)*x - y^3"
    by (simp add: power2_eq_square)
  finally show ?thesis by simp
qed

lemma kvadrat_binoma:
  fixes x y :: real
  assumes "x>0" "y>0"
  shows "(-x-y)^2 = x^2 + 2*x*y + y^2"
proof-
  have "(-x-y)^2 = (-x-y)*(-x-y)"
    using power2_eq_square 
    by auto
  also have "... = ((-x)*(-x)-x*(-y)-y*(-x)+y*y)"
    by (simp add: left_diff_distrib' right_diff_distrib')
  also have "... = x^2 + 2*x*y + y^2"
    by (simp add: power2_eq_square)
  finally show ?thesis
    .
qed

lemma p1:
  fixes x y z :: real
  assumes "x \<ge>0" "y \<ge>0" "z =-x -y"
  shows  "(x^3 + y^3 + z^3)^2 = 9*(x^2)*(y^2)*(x+y)^2"
  using assms
proof-
  have "(x^3 + y^3 + z^3)^2 = (x^3 + y^3 + (-x-y)^3)^2 " using assms(3) by auto
  also have "(-x-y)^3 =  -(x^3) - 3*(x^2)*y - 3*(y^2)*x - y^3" using kub_binoma 
    by (simp add: assms(1) assms(2))
  also  have "(x^3 + y^3 + z^3)^2 =(x^3 + y^3 - (x^3) -3*(x^2)*y - 3*x*(y^2) - y^3)^2"
  proof -
    have f1: "\<forall>r ra rb. (ra::real) + (r + rb) = r + (rb + ra)"
by simp
have f2: "\<forall>r ra. (r::real) * (ra * r) = ra * r\<^sup>2"
by (simp add: power2_eq_square)
  have "(x * x * x + y ^ 3 + z ^ 3)\<^sup>2 = (x * x * x + y ^ 3 + (- (x * x * x) + - (3 * x\<^sup>2 * y) + - (3 * y\<^sup>2 * x) + - (y ^ 3)))\<^sup>2"
    by (metis (no_types) add_uminus_conv_diff calculation power3_eq_cube)
  then have "(x * x * x + y ^ 3 + z ^ 3)\<^sup>2 = (- (y ^ 3) + (x * x * x + y ^ 3 + (- (x * x * x) + - (3 * x\<^sup>2 * y) + - (3 * y\<^sup>2 * x))))\<^sup>2"
    using f1 by metis
then have "(x * x * x + y ^ 3 + z ^ 3)\<^sup>2 = (x * x * x + (y ^ 3 + - (3 * y\<^sup>2 * x + 3 * x\<^sup>2 * y + y ^ 3 + x * x * x)))\<^sup>2"
by simp
  then have "(x * x * x + y ^ 3 + z ^ 3)\<^sup>2 = (x * x * x + (y ^ 3 + - (x * x * x + (y ^ 3 + (x * (3 * y\<^sup>2) + y * (x * (3 * x)))))))\<^sup>2"
using f2 by (metis (no_types) add.commute mult.commute)
  then have "(x * x * x + y ^ 3 + z ^ 3)\<^sup>2 = (x * x * x + (y ^ 3 + - (x * x * x + (y ^ 3 + x * (3 * (y * (x + y)))))))\<^sup>2"
    by (simp add: add.commute distrib_left mult.left_commute power2_eq_square)
  then have "(x * x * x + y * (y * y) + z ^ 3)\<^sup>2 = (x * x * x + (y * (y * y) + - (x * x * x + (y * (y * y) + x * (y * ((x + y) * 3))))))\<^sup>2"
    by (simp add: mult.commute mult.left_commute power3_eq_cube)
  then have "(x * x * x + y * (y * y) + z ^ 3)\<^sup>2 = (y * (y * y) + (x * x * x + - (y * (y * y) + (x * x * x + x * (y * ((x + y) * 3))))))\<^sup>2"
    by simp
  then have "(x * x * x + y * y * y + z ^ 3)\<^sup>2 = (x * x * x + (y * y * y + - (x * x * x + (y * y * y + x * (y * ((x + y) * 3))))))\<^sup>2"
    by (simp add: mult.commute)
  then have "(x ^ 3 + y ^ 3 + z ^ 3)\<^sup>2 = (x ^ 3 + (y ^ 3 + - (x ^ 3 + (y ^ 3 + y * (x * (3 * x) + 3 * x * y)))))\<^sup>2"
    by (simp add: distrib_left mult.commute mult.left_commute power3_eq_cube)
  then have "(x ^ 3 + y ^ 3 + z ^ 3)\<^sup>2 = (x ^ 3 + (y ^ 3 + - (x ^ 3 + (y ^ 3 + (3 * x * y\<^sup>2 + 3 * x\<^sup>2 * y)))))\<^sup>2"
    using f2 by (metis (no_types) add.commute distrib_left mult.commute)
  then have "(x ^ 3 + y ^ 3 + z ^ 3)\<^sup>2 = (x ^ 3 + (y ^ 3 + (- (y ^ 3) + (- (3 * x * y\<^sup>2) + - (3 * x\<^sup>2 * y) + - (x ^ 3)))))\<^sup>2"
    by force
  then have "(x ^ 3 + y ^ 3 + z ^ 3)\<^sup>2 = (x ^ 3 + (- (y ^ 3) + (y ^ 3 + - (x ^ 3) + (- (3 * x * y\<^sup>2) + - (3 * x\<^sup>2 * y)))))\<^sup>2"
    by (simp add: add.commute)
  then show ?thesis
    by (simp add: add.commute)
qed
  also have "... = (-3*(x^2)*y - 3*x*(y^2))^2"
    by simp
  also have "... = (-3*x*x*y - 3*x*y*y)^2"
    by (simp add: ab_semigroup_mult_class.mult_ac(1) power2_eq_square)
  also have "... = (-3*x*y*(x+y))^2"
  proof -
    have f1: "\<forall>r ra. - (ra::real) - r = - (r + ra)"
      by auto
    have "\<forall>r ra rb. (ra::real) * - rb - r * rb = rb * (- ra - r)"
      by (simp add: right_diff_distrib)
    then have "(y * ((x + y) * (x * - 3)))\<^sup>2 = (x * (y * (x * - 3 - y * 3)))\<^sup>2"
      using f1 by (metis (no_types) add.commute mult.commute mult.left_commute mult_minus_right)
    then show ?thesis
      by (simp add: mult.commute mult.left_commute right_diff_distrib)
  qed
  also have "... = (-3*x*y*(x+y))*(-3*x*y*(x+y))"
    using power2_eq_square by blast
  also have "... = (-3)*(-3)*x*x*y*y*(x+y)*(x+y)"
    by auto
  also have "... = 9*(x^2)*(y^2)*(x+y)^2"
    by (simp add: power2_eq_square)
  then show ?thesis
    using \<open>(- x - y) ^ 3 = - (x ^ 3) - 3 * x\<^sup>2 * y - 3 * y\<^sup>2 * x - y ^ 3\<close> assms(3) calculation by auto
qed

lemma p2:
  fixes x y z :: real
  assumes "x\<ge>0" "y\<ge>0" "z = -x - y"
  shows "(x^2+y^2+z^2)^3 = 8*(x^2+y^2+x*y)^3"
  using assms
proof-
  have "(x^2+y^2+z^2)^3 = (x^2+y^2+(-x-y)^2)^3" using assms(3) by auto
  also have "... = (x^2 + y^2 + x^2 + 2*x*y + y^2)^3" using kvadrat_binoma 
  proof -
have f1: "\<forall>r ra. - (ra::real) - r = - (r + ra)"
by simp
  have "\<forall>r ra rb. (r::real) + (ra + rb)\<^sup>2 = ra\<^sup>2 + (r + (2 * ra * rb + rb\<^sup>2))"
    by (simp add: power2_sum)
  then have "\<forall>r ra rb. (r::real) + (ra + rb)\<^sup>2 = ra\<^sup>2 + (r + (rb\<^sup>2 + 2 * ra * rb))"
    by simp
then have "(x\<^sup>2 + (y\<^sup>2 + (- x - y)\<^sup>2)) ^ 3 = (x\<^sup>2 + (x\<^sup>2 + (y\<^sup>2 + (y\<^sup>2 + 2 * x * y)))) ^ 3"
using f1 by (metis (no_types) add.commute power2_minus)
  then show ?thesis
    by (simp add: add.commute add.left_commute)
qed
  also have "... = (2*(x^2) + 2*(y^2) + 2*x*y)^3"
    by (simp add: add.commute add.left_commute)
  also have "... =2^3*(x^2 + y^2 + x*y)^3"
    by (metis (no_types, hide_lams) ab_semigroup_mult_class.mult_ac(1) power_mult_distrib ring_class.ring_distribs(1))
  also have "... = 8 *(x^2+y^2+x*y)^3"
    by simp
  then show ?thesis
    by (simp add: calculation)
qed

  
lemma zadatak:
  fixes x y z :: real
  assumes "x + y + z = 0" "x\<ge>0" "y\<ge>0" "z = -x -y"
  shows "6*(x^3 + y^3 + z^3)^2\<le> (x^2 + y^2 + z^2)^3"
  using assms
proof-
  have "x^2+y^2 \<ge> 2*x*y"
    by (simp add: sum_squares_bound)
  also have "x^2+y^2+x*y \<ge> 3*x*y"
    using calculation by auto
  have "4*(x^2 + y^2 + x*y) \<ge> 3*(x^2 + y^2 +x*y)+3*x*y" 
    using \<open>3 * x * y \<le> x\<^sup>2 + y\<^sup>2 + x * y\<close> by auto
  also have "4*(x^2 + y^2 + x*y) \<ge> 3*(x+y)^2"
    by (smt \<open>2 * x * y \<le> x\<^sup>2 + y\<^sup>2\<close> distrib_right power2_sum)
  have "(x^2+y^2+z^2)^3 = 8*(x^2+y^2+x*y)^3" using p2
    using assms(2) assms(3) assms(4) by blast
  have "(x^2+y^2+z^2)^3 = 2*(x^2+y^2+x*y)^2*4*(x^2+y^2+x*y)"
proof -
  have f1: "\<forall>r. (r::real) * (r * r) = r ^ 3"
by (simp add: power3_eq_cube)
have f2: "\<forall>r ra rb rc. (r::real) * (rc * (ra * rb)) = rc * ra * (r * rb)"
  by simp
  have "8 * (x * x + (x + y) * y) ^ 3 = (x * x + (y * y + z * z)) ^ 3"
    by (metis (no_types) \<open>(x\<^sup>2 + y\<^sup>2 + z\<^sup>2) ^ 3 = 8 * (x\<^sup>2 + y\<^sup>2 + x * y) ^ 3\<close> add.commute add.left_commute distrib_right power2_eq_square)
  then have "(x * x + (x * y + y * y)) * (2 * (4 * (x * x + (x * y + y * y))\<^sup>2)) = (x * x + (y * y + z * z)) ^ 3"
    using f2 f1 by (metis (no_types) distrib_right mult_2 numeral_plus_numeral power2_eq_square semiring_norm(2) semiring_norm(6))
  then show ?thesis
    by (simp add: add.commute add.left_commute mult.commute power2_eq_square)
qed
  also have "(x^3 + y^3 + z^3)^2 = 9*(x^2)*(y^2)*(x+y)^2"  using p1
    using assms(2) assms(3) assms(4) by blast
  also have "(x^3 + y^3 + z^3)^2 =3^2*(x*y)^2*(x+y)^2"
  proof -
    have f1: "x + y = - z"
      using assms(4) by auto
   have f2: "\<forall>r ra rb. (ra::real) * (rb * r) = r * (ra * rb)"
     by simp
  have f3: "\<forall>r ra. (r::real) * (ra * r) = ra * r\<^sup>2"
    by (simp add: power2_eq_square)
  have "9 * (x * x) * y\<^sup>2 * (x + y)\<^sup>2 = (x ^ 3 + y ^ 3 + z ^ 3)\<^sup>2"
    by (metis (full_types) \<open>(x ^ 3 + y ^ 3 + z ^ 3)\<^sup>2 = 9 * x\<^sup>2 * y\<^sup>2 * (x + y)\<^sup>2\<close> power2_eq_square)
  then have "9 * (x * x) * y\<^sup>2 * (x + y)\<^sup>2 = (y * y * y + (z * z * z + x * x * x))\<^sup>2"
    by (simp add: add.commute add.left_commute power3_eq_cube)
  then have "9 * (x * x) * y\<^sup>2 * (x + y)\<^sup>2 = (x * (x * x) + (y * (y * y) + z * (z * z)))\<^sup>2"
    by (simp add: ab_semigroup_mult_class.mult_ac(1) add.commute add.left_commute)
  then have "9 * (x * x) * y\<^sup>2 * (- z * - z) = (x * (x * x) + (y * (y * y) + z * (z * z)))\<^sup>2"
    using f1 by (simp add: power2_eq_square)
  then have "x * (x * (- z * (- z * (y * (9 * y))))) = (x * (x * x) + (y * (y * y) + z * (z * z)))\<^sup>2"
    using f3 f2 by (metis (no_types) ab_semigroup_mult_class.mult_ac(1))
  then have "\<exists>r. r + (x * (x * x) + (y * (y * y) + z * (z * z)))\<^sup>2 = r + x * (x * (y * (y * ((x + y) * ((x + y) * numeral (num.Bit1 num.One * num.Bit1 num.One))))))"
    using f2 f1 by (simp add: mult.left_commute)
  then have "x * y * (x * y) * 3\<^sup>2 * ((x + y) * (x + y)) = (x * (x * x) + (y * (y * y) + z * (z * z)))\<^sup>2"
    by simp
  then show ?thesis
    by (simp add: add.commute add.left_commute mult.commute power2_eq_square power3_eq_cube)
qed
   also have "(x^3 + y^3 + z^3)^2 =(3*x*y)^2*(x+y)^2"
     by (metis (no_types, hide_lams) \<open>(x ^ 3 + y ^ 3 + z ^ 3)\<^sup>2 = 3\<^sup>2 * (x * y)\<^sup>2 * (x + y)\<^sup>2\<close> mult.assoc mult.left_commute power2_eq_square)
   also have " 6*(x^3+y^3+z^3)^2 = 6*(3*x*y)^2*(x+y)^2"
     by (simp add: \<open>(x ^ 3 + y ^ 3 + z ^ 3)\<^sup>2 = (3 * x * y)\<^sup>2 * (x + y)\<^sup>2\<close>)
  also have " 2*(3*x*y)^2*3*(x+y)^2 = 6*(x^3+y^3+z^3)^2"
    by (simp add: \<open>6 * (x ^ 3 + y ^ 3 + z ^ 3)\<^sup>2 = 6 * (3 * x * y)\<^sup>2 * (x + y)\<^sup>2\<close>)
  also have "2*(x^2+y^2+x*y)^2*4*(x^2+y^2+x*y) \<ge> 2*(3*x*y)^2*3*(x+y)^2"
    sorry
 have "6*(x^3 + y^3 + z^3)^2\<le> (x^2 + y^2 + z^2)^3"
    using \<open>(x\<^sup>2 + y\<^sup>2 + z\<^sup>2) ^ 3 = 2 * (x\<^sup>2 + y\<^sup>2 + x * y)\<^sup>2 * 4 * (x\<^sup>2 + y\<^sup>2 + x * y)\<close> \<open>2 * (3 * x * y)\<^sup>2 * 3 * (x + y)\<^sup>2 = 6 * (x ^ 3 + y ^ 3 + z ^ 3)\<^sup>2\<close> \<open>2 * (3 * x * y)\<^sup>2 * 3 * (x + y)\<^sup>2 \<le> 2 * (x\<^sup>2 + y\<^sup>2 + x * y)\<^sup>2 * 4 * (x\<^sup>2 + y\<^sup>2 + x * y)\<close> by linarith
  then show ?thesis 
    by blast
qed
  
  
end