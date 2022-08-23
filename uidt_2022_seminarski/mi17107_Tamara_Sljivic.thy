theory mi17107_Tamara_Sljivic
  imports Complex_Main 
begin


text\<open>
Link: https://imomath.com/srb/zadaci/2017_egmo-izborno_resenja.pdf
Zadatak: 1. zadatak
Dokazati da za sve nenegativne realne brojeve a,b, i c važi nejednakost
a*sqrt((a+b)*(a+c)) +b*sqrt((b+c)*(b+a)) + c*sqrt((c+a)*(c+b))  \<ge> (a^2+b^2+c^2+3*a*b +3*b*c+3*c*a)/2

\<close>




lemma postavka_seminarski:
   fixes a b c :: "real"
   assumes "a \<ge> 0" "b \<ge> 0" "c \<ge> 0"  "b+c=x^2" "c+a=y^2" "a+b=z^2" "x\<ge>0" "y\<ge>0" "z\<ge>0"
   shows "a*sqrt((a+b)*(a+c)) +b*sqrt((b+c)*(b+a))
        + c*sqrt((c+a)*(c+b))  \<ge> (a^2+b^2+c^2+3*a*b +3*b*c+3*c*a)/2" 
  using assms
proof -
  have "2*a= y^2 +z^2-x^2"
    using assms(4) assms(5) assms(6) by force
  also have "2*b =z^2+x^2-y^2 "
    using assms(4) assms(5) calculation by force
  also have "2*c = x^2+y^2-z^2"
    using assms(5) calculation by force
  also have "a^2+b^2+c^2+3*a*b+3*b*c+3*c*a =a*a+b*b+c*c+3*a*b+3*b*c+3*c*a "
    by (simp add: power2_eq_square)

 (* then have "... = a*b+c*a+a*a+b*c+ b*b+c*c+a*b+a*b+2*b*c+2*c*a" 
    by simp*)
  then have "... = a*b + c*a + b*b + b*c + a*b + c*a + a*a + b*c + a*b + c*a + c*c + b*c"
    by simp
  then have "... = (a*b + c*a + b*b + b*c) + (a*b + c*a + a*a + b*c) + (a*b + c*a + c*c + b*c)"
    by simp
  then have "... =(a+b)*(b+c) +(b+c)*(c+a) + (c+a)*(a+b)"
    by (simp add: mult.commute ring_class.ring_distribs(1))
  then have "... = x*x*y*y+y*y*z*z+z*z*x*x"
    by (simp add: assms(4) assms(5) assms(6) power2_eq_square)
 (* then have "a*sqrt((a+b)*(a+c)) +b*sqrt((b+c)*(b+a)) + c*sqrt((c+a)*(c+b)) =2*(x*x +y*y-z*z)*x*y+2*(y*y+z*z-x*x)*y*z+2*(z*z+x*x-y*y)*z*x "
    using \<open>2*a= y^2 +z^2-x^2\<close> \<open>2*b =z^2+x^2-y^2\<close> \<open>2*c = x^2+y^2-z^2\<close>
sledgehammer
*)
  then have "a*sqrt((a+b)*(a+c)) +b*sqrt((b+c)*(b+a)) + c*sqrt((c+a)*(c+b)) = a*sqrt(z*z*y*y)+b*sqrt(x*x*z*z)+c*sqrt(x*x*y*y)"
   
    by (smt (verit, best) assms(4) assms(5) assms(6) mult.assoc mult.commute power2_eq_square)
  then have "... = (y*y + z*z - x*x)/2*sqrt(z*z*y*y)+b*sqrt(x*x*z*z)+c*sqrt(x*x*y*y)"
    by (smt (z3) calculation field_sum_of_halves power2_eq_square)
  then have  "... = (y*y + z*z - x*x)/2*sqrt(z*z*y*y)+(z*z+x*x-y*y)/2*sqrt(x*x*z*z)+(x*x+y*y-z*z)/2*sqrt(x*x*y*y)"
    by (smt (z3) assms(4) assms(5) calculation field_sum_of_halves power2_eq_square)
  then have "... =((y*y + z*z - x*x)*sqrt(z*z*y*y)+(z*z+x*x-y*y)*sqrt(x*x*z*z)+(x*x+y*y-z*z)*sqrt(x*x*y*y))/2 "
    by simp
  then  have "(x*x +y*y)*x*y\<ge> 2*x*x*y*y"
  proof-
    have "(x*x +y*y)*x*y -2*x*x*y*y=x*y*(x*x-2*x*y+y*y)"
      
      by (smt (verit, del_insts) ab_semigroup_mult_class.mult_ac(1) mult.commute right_diff_distrib)
     then have "... = x*y*(x^2-2*x*y+y^2)"
       by (simp add: power2_eq_square)
     then have "... = x*y*(x-y)^2"
       by (simp add: power2_diff)
     then have "... \<ge> 0"
       by (simp add: assms(7) assms(8))
      show ?thesis
       using \<open>(x * x + y * y) * x * y - 2 * x * x * y * y = x * y * (x * x - 2 * x * y + y * y)\<close> \<open>0 \<le> x * y * (x - y)\<^sup>2\<close> \<open>x * y * (x * x - 2 * x * y + y * y) = x * y * (x\<^sup>2 - 2 * x * y + y\<^sup>2)\<close> \<open>x * y * (x\<^sup>2 - 2 * x * y + y\<^sup>2) = x * y * (x - y)\<^sup>2\<close> by auto

   qed
   then have "(x^2+y^2)*x*y \<ge> 2*x*x*y*y"
     by (simp add: power2_eq_square)
   then have "(x^2+y^2)*x*y*z^2 \<ge> 2*x*x*y*y*z^2"
     by (simp add: mult_right_mono)
then have "(x^2+y^2)*z^2 \<ge> 2*x*y*z^2"
  by (simp add: mult_right_mono sum_squares_bound)
  then have "(x^2*z^2+y^2*z^2) \<ge> 2*x*y*z^2"
    by (simp add: ring_class.ring_distribs(2))
  then have "(x^2*z^2+y^2*z^2)/2 \<ge> x*y*z^2"
    by simp
 then have "(x^2+y^2-z^2)*x*y = (x^2+y^2)*x*y - z^2*x*y" 
   by (simp add: mult.commute right_diff_distrib)
  then have "... \<ge> 2*x*x*y*y - z^2*x*y"
    by (simp add: \<open>2 * x * x * y * y \<le> (x\<^sup>2 + y\<^sup>2) * x * y\<close>)
  then have "... \<ge> 2*x*x*y*y-(x^2*z^2 +y^2*z^2)/2"
    by (smt (verit) \<open>x * y * z\<^sup>2 \<le> (x\<^sup>2 * z\<^sup>2 + y\<^sup>2 * z\<^sup>2) / 2\<close> mult.assoc mult.commute)

 qed



