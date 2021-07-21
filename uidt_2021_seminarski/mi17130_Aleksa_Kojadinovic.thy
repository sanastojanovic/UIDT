theory mi17130_Aleksa_Kojadinovic
  imports Main HOL.Real "HOL-ex.Sqrt"

begin

text \<open>
Link: https://www.imo-official.org/problems/IMO2006SL.pdf
A5. Neka su a b i c stranice trougla. Pokazati:
sqrt (b + c - a) / (sqrt b + sqrt c - sqrt a) + sqrt (c + a - b) / (sqrt c + sqrt a - sqrt b) + sqrt (a + b - c) / (sqrt a + sqrt b - sqrt c) <= 3
\<close>


(*
  Pokazuje da su svi imenioci iz izraza u originalnoj lemi pozitivni.
  Promenljive su ovde nazvane p, q i r da ne bi dolazilo do zabune.

*)

lemma DenPositive:
  fixes p q r :: "real"
  assumes "p > 0" "q > 0" "r > 0"
  assumes "p + q > r"
  shows "sqrt p + sqrt q - sqrt r > 0"
  using assms
proof-
  have "p + q > r"
    using assms(4) by auto
  from this have "sqrt p + sqrt q > sqrt r"
    by (smt (z3) assms(1) assms(2) real_sqrt_less_mono sqrt_add_le_add_sqrt)
  from this show ?thesis
    by simp
qed

lemma UtilSubLemma:
  fixes u :: "real"
  assumes "u > -1/2"
  shows "sqrt (1 + 2*u) \<le> 1 + u"
  using assms
proof-

  have "1 + u > 0"
    using assms
    by auto

  have "sqrt (1 + 2*u) \<le> sqrt (1 + 2*u + u^2)"
    by simp
  also have "... = sqrt ((1 + u)^2)" 
    by (simp add: Power.comm_semiring_1_class.power2_sum)
  also have "... = 1+u"
    using `1 + u > 0` by simp
  finally show ?thesis .
qed

thm "Rings.ring_class.right_diff_distrib"

find_theorems "(_ + _)*_ = _ * _ + _ * _"

(*
  Izraz oblika (sqrt p + sqrt q - sqrt r)^2 se vrlo cesto javlja pa zbog toga uvodim
  lemu koja direktno dokazuje njegov rezultat u najpogodnijem obliku za rad
*)

lemma TrinSquareMinus:
  fixes p q r :: "real"
  assumes "p > 0" "q > 0" "r > 0"
  shows "(sqrt p + sqrt q - sqrt r)^2 = p + q + r + 2*sqrt(p*q) - 2*sqrt(p*r) - 2*sqrt(q*r)"
proof-
  have "(sqrt p + sqrt q - sqrt r)^2 = (sqrt p + sqrt q - sqrt r)*(sqrt p + sqrt q - sqrt r)"
    by (simp add: power2_eq_square)
  also have "... = (sqrt p + sqrt q - sqrt r)*sqrt p + (sqrt p + sqrt q - sqrt r)*(sqrt q - sqrt r)"
    by (metis add_diff_eq distrib_right mult.commute)
  also have "... = sqrt p * sqrt p + sqrt q * sqrt p - sqrt r * sqrt p + (sqrt p + sqrt q - sqrt r)*(sqrt q - sqrt r)"
    by (metis diff_diff_eq2 left_diff_distrib')
  also have "... = sqrt p * sqrt p + sqrt q * sqrt p - sqrt r * sqrt p + (sqrt p + sqrt q - sqrt r)*sqrt q - (sqrt p + sqrt q - sqrt r)*sqrt r"
    using right_diff_distrib by auto
  also have "... = sqrt p * sqrt p + sqrt q * sqrt p - sqrt r * sqrt p + sqrt p * sqrt q + sqrt q * sqrt q - sqrt r * sqrt q - (sqrt p + sqrt q - sqrt r)*sqrt r"
    by (simp add: distrib_right left_diff_distrib)
  also have "... = sqrt p * sqrt p + sqrt q * sqrt p - sqrt r * sqrt p + sqrt p * sqrt q + sqrt q * sqrt q - sqrt r * sqrt q - sqrt p * sqrt r - sqrt q * sqrt r + sqrt r * sqrt r"
    by (simp add: distrib_right left_diff_distrib)  
  also have "... = p + sqrt p * sqrt q - sqrt p * sqrt r + sqrt p * sqrt q + q - sqrt q * sqrt r - sqrt p * sqrt r - sqrt q * sqrt r + r"
    using assms
    using power2_eq_square
    using mult.commute
    by auto
  also have "... = p + sqrt (p*q) - sqrt (p*r) + sqrt (p*q) + q - sqrt(q*r) - sqrt(p*r) - sqrt(q*r) + r"
    using NthRoot.real_sqrt_mult
    by auto
  also have "... = p + q + r + 2*sqrt(p*q) - 2*sqrt(p*r) - 2*sqrt(q*r)"
    by simp
  finally show ?thesis .
qed

(*
  Dve leme o nejednakostima za brzu transformaciju nekih nejednacina
  kasnije.
*)

lemma MultIneqSame:
  fixes a b :: real
  assumes "n > 0"
  shows "a < b \<longleftrightarrow> n*a < n*b"
  using assms
  by simp

lemma SubPosIneq:
  fixes a b n :: "real"
  assumes "n \<ge> 0" "a \<le> b - n"
  shows "a \<le> b"
  using assms
  by simp
  
  
  

(*
  Lema koja omogucava primenu leme UtilSubLemma na 
  prvu XYZ transformaciju
*)

lemma FirstSubViable:
  fixes a b c :: "real"
  assumes "a + b > c" "a + c > b" "b + c > a"
  assumes "a > 0" "b > 0" "c > 0"
  assumes "x = sqrt b + sqrt c - sqrt a"
  assumes "y = sqrt c + sqrt a - sqrt b"
  assumes "z = sqrt a + sqrt b - sqrt c"
  assumes "x > 0" "y > 0" "z > 0"
  shows "-(x-y)*(x-z)/(4*x^2) > -1/2"
proof-
  have "x ^ 2 > 0" 
    using assms(10) by auto

  have "x*z > 0"
    using assms by simp
  have "y*x > 0"
    using assms by simp
  have "y*z > 0"
    using assms by simp

  have "?thesis \<longleftrightarrow> (x-y)*(x-z)/(4*x^2) < 1/2"
    by linarith
  also have "... \<longleftrightarrow> 4*((x-y)*(x-z)/(4*x^2)) < 4*(1/2)" 
    using MultIneqSame
    by linarith
  also have "... \<longleftrightarrow> (x-y)*(x-z)/(x^2) < 2"
    by simp
  also have "... \<longleftrightarrow> (x^2)*((x-y)*(x-z)/(x^2)) < x^2*(2)"
    using MultIneqSame
    by (meson \<open>0 < x\<^sup>2\<close>)
  also have "... \<longleftrightarrow> (x-y)*(x-z) < (x^2)*2"
    using \<open>0 < x\<^sup>2\<close> by auto
  also have "... \<longleftrightarrow> (sqrt b + sqrt c - sqrt a - (sqrt c +  sqrt a - sqrt b))*(sqrt b + sqrt c - sqrt a - (sqrt a + sqrt b - sqrt c)) < 2*x^2"
    using assms
    by auto
  also have "... \<longleftrightarrow> (sqrt b + sqrt c - sqrt a - sqrt c - sqrt a + sqrt b)*(sqrt b + sqrt c - sqrt a - sqrt a - sqrt b + sqrt c) < 2*x^2"
    by simp
  also have "... \<longleftrightarrow> (2*(sqrt b) - 2*sqrt(a))*(2*(sqrt c) - 2*(sqrt a)) < 2*x^2"
    by simp
  also have "... \<longleftrightarrow> 4*(sqrt b - sqrt a)*(sqrt c - sqrt a) < 2*x^2"
    by (metis (mono_tags, hide_lams) mult.commute mult.left_commute mult_numeral_left_semiring_numeral num_double right_diff_distrib')
  also have "... \<longleftrightarrow> 2*(sqrt b - sqrt a)*(sqrt c - sqrt a) < x^2"
    by linarith
  also have "... \<longleftrightarrow> 2*(sqrt b * (sqrt c - sqrt a) - sqrt a *(sqrt c - sqrt a)) < x^2"
    by (simp add: ab_semigroup_mult_class.mult_ac(1) left_diff_distrib')
  also have "... \<longleftrightarrow> 2*(sqrt b * sqrt c - sqrt b * sqrt a - sqrt a * (sqrt c - sqrt a)) < x^2"
    by (smt (verit, del_insts) distrib_left)
  also have "... \<longleftrightarrow> 2*(sqrt b * sqrt c - sqrt b * sqrt a - sqrt a * sqrt c + sqrt a * sqrt a) < x^2"
    apply (subst Rings.ring_class.right_diff_distrib)
    back
    by auto
  also have "... \<longleftrightarrow> 2*(sqrt (b*c) - sqrt (b*a) - sqrt (a*c) + a) < x^2"
    using `x > 0`
    using NthRoot.real_sqrt_mult
    using assms(4) by force
  also have "... \<longleftrightarrow> 2*(sqrt (b*c) - sqrt (b*a) - sqrt (a*c) + a) < (sqrt b + sqrt c - sqrt a)^2"
    using assms
    by auto
  also have "... \<longleftrightarrow> 2*(sqrt (b*c) - sqrt (b*a) - sqrt (a*c) + a) < b + c + a + 2*sqrt(b*c) - 2*sqrt(b*a) - 2*sqrt(c*a)"
    using TrinSquareMinus
    by (metis assms(4) assms(5) assms(6))
  also have "... \<longleftrightarrow> 2*sqrt(b*c) - 2*sqrt(b*a) - 2*sqrt(a*c) + 2*a < b + c + a + 2*sqrt(b*c) - 2*sqrt(b*a) - 2*sqrt(c*a)"
    by simp
  also have "... \<longleftrightarrow> a < b + c"
    by (simp add: mult.commute)
  also have "... \<longleftrightarrow> True"
    using assms
    by simp
  finally show ?thesis 
    by simp
qed


(*
  Lema koja omogucava primenu leme UtilSubLemma na 
  drugu XYZ transformaciju
*)

lemma SecondSubViable:
  fixes a b c :: "real"
  assumes "a + b > c" "a + c > b" "b + c > a"
  assumes "a > 0" "b > 0" "c > 0"
  assumes "x = sqrt b + sqrt c - sqrt a"
  assumes "y = sqrt c + sqrt a - sqrt b"
  assumes "z = sqrt a + sqrt b - sqrt c"
  assumes "x > 0" "y > 0" "z > 0"
  shows "-(z-x)*(z-y)/(4*z^2) > -1/2"
proof-
  have "z ^ 2 > 0" 
    using assms(12) by auto

  have "x*z > 0"
    using assms by simp
  have "y*x > 0"
    using assms by simp
  have "y*z > 0"
    using assms by simp

  have "?thesis \<longleftrightarrow> (z-x)*(z-y)/(4*z^2) < 1/2"
    by linarith
  also have "... \<longleftrightarrow> 4*((z-x)*(z-y)/(4*z^2)) < 4*(1/2)" 
    using MultIneqSame
    by linarith
  also have "... \<longleftrightarrow> (z-x)*(z-y)/(z^2) < 2"
    by simp
  also have "... \<longleftrightarrow> (z^2)*((z-x)*(z-y)/(z^2)) < z^2*(2)"
    using MultIneqSame
    by (meson \<open>0 < z^2\<close>)
  also have "... \<longleftrightarrow> (z-x)*(z-y) < (z^2)*2"
    using \<open>0 < z^2\<close> by auto
  also have "... \<longleftrightarrow> (sqrt a + sqrt b - sqrt c - (sqrt b +  sqrt c - sqrt a))*(sqrt a + sqrt b - sqrt c - (sqrt c + sqrt a - sqrt b)) < 2*z^2"
    using assms
    by auto
  also have "... \<longleftrightarrow> (sqrt a + sqrt b - sqrt c - sqrt b - sqrt c + sqrt a)*(sqrt a + sqrt b - sqrt c - sqrt c - sqrt a + sqrt b) < 2*z^2"
    by simp
  also have "... \<longleftrightarrow> (2*(sqrt a) - 2*sqrt(c))*(2*(sqrt b) - 2*(sqrt c)) < 2*z^2"
    by simp
  also have "... \<longleftrightarrow> 4*(sqrt a - sqrt c)*(sqrt b - sqrt c) < 2*z^2"
    by (metis (mono_tags, hide_lams) mult.commute mult.left_commute mult_numeral_left_semiring_numeral num_double right_diff_distrib')
  also have "... \<longleftrightarrow> 2*(sqrt a - sqrt c)*(sqrt b - sqrt c) < z^2"
    by linarith
  also have "... \<longleftrightarrow> 2*(sqrt a * (sqrt b - sqrt c) - sqrt c *(sqrt b - sqrt c)) < z^2"
    by (simp add: ab_semigroup_mult_class.mult_ac(1) left_diff_distrib')
  also have "... \<longleftrightarrow> 2*(sqrt a * sqrt b - sqrt a * sqrt c - sqrt c * (sqrt b - sqrt c)) < z^2"
    by (smt (verit, del_insts) distrib_left)
  also have "... \<longleftrightarrow> 2*(sqrt a * sqrt b - sqrt a * sqrt c - sqrt c * sqrt b + sqrt c * sqrt c) < z^2"
    apply (subst Rings.ring_class.right_diff_distrib)
    back
    by auto
  also have "... \<longleftrightarrow> 2*(sqrt (a*b) - sqrt (a*c) - sqrt (c*b) + c) < z^2"
    using NthRoot.real_sqrt_mult
    using assms(6) by force
  also have "... \<longleftrightarrow> 2*(sqrt (a*b) - sqrt (a*c) - sqrt (c*b) + c) < (sqrt a + sqrt b - sqrt c)^2"
    using assms
    by auto
  also have "... \<longleftrightarrow> 2*(sqrt (a*b) - sqrt (a*c) - sqrt (c*b) + c) < a + b +  c + 2*sqrt(a*b) - 2*sqrt(a*c) - 2*sqrt(b*c)"
    using TrinSquareMinus
    using assms(4) assms(5) assms(6) by presburger
  also have "... \<longleftrightarrow> 2*sqrt(a*b) - 2*sqrt(a*c) - 2*sqrt(c*b) + 2*c < a + b +  c + 2*sqrt(a*b) - 2*sqrt(a*c) - 2*sqrt(b*c)"
    by simp
  also have "... \<longleftrightarrow> c < a + b"
    by (simp add: mult.commute)
  also have "... \<longleftrightarrow> True"
    using assms
    by simp
  finally show ?thesis 
    by simp
qed

(*
  Lema koja omogucava primenu leme UtilSubLemma na 
  trecu XYZ transformaciju
*)

lemma ThirdSubViable:
  fixes a b c :: "real"
  assumes "a + b > c" "a + c > b" "b + c > a"
  assumes "a > 0" "b > 0" "c > 0"
  assumes "x = sqrt b + sqrt c - sqrt a"
  assumes "y = sqrt c + sqrt a - sqrt b"
  assumes "z = sqrt a + sqrt b - sqrt c"
  assumes "x > 0" "y > 0" "z > 0"
  shows "-(y-z)*(y-x)/(4*y^2) > -1/2"
proof-
  have "y ^ 2 > 0" 
    using assms(11) by auto

  have "x*z > 0"
    using assms by simp
  have "y*x > 0"
    using assms by simp
  have "y*z > 0"
    using assms by simp

  have "?thesis \<longleftrightarrow> (y-z)*(y-x)/(4*y^2) < 1/2"
    by linarith
  also have "... \<longleftrightarrow> 4*((y-z)*(y-x)/(4*y^2)) < 4*(1/2)" 
    using MultIneqSame
    by linarith
  also have "... \<longleftrightarrow> (y-z)*(y-x)/(y^2) < 2"
    by simp
  also have "... \<longleftrightarrow> (y^2)*((y-z)*(y-x)/(y^2)) < y^2*(2)"
    using MultIneqSame
    by (meson \<open>0 < y^2\<close>)
  also have "... \<longleftrightarrow> (y-z)*(y-x) < (y^2)*2"
    using \<open>0 < y^2\<close> by auto
  also have "... \<longleftrightarrow> (sqrt c + sqrt a - sqrt b - (sqrt a +  sqrt b - sqrt c))*(sqrt c + sqrt a - sqrt b - (sqrt b + sqrt c - sqrt a)) < 2*y^2"
    using assms
    by auto
  also have "... \<longleftrightarrow> (sqrt c + sqrt a - sqrt b - sqrt a - sqrt b + sqrt c)*(sqrt c + sqrt a - sqrt b - sqrt b - sqrt c + sqrt a) < 2*y^2"
    by simp
  also have "... \<longleftrightarrow> (2*(sqrt c) - 2*sqrt(b))*(2*(sqrt a) - 2*(sqrt b)) < 2*y^2"
    by simp
  also have "... \<longleftrightarrow> 4*(sqrt c - sqrt b)*(sqrt a - sqrt b) < 2*y^2"
    by (metis (mono_tags, hide_lams) mult.commute mult.left_commute mult_numeral_left_semiring_numeral num_double right_diff_distrib')
  also have "... \<longleftrightarrow> 2*(sqrt c - sqrt b)*(sqrt a - sqrt b) < y^2"
    by linarith
  also have "... \<longleftrightarrow> 2*(sqrt c * (sqrt a - sqrt b) - sqrt b *(sqrt a - sqrt b)) < y^2"
    by (simp add: ab_semigroup_mult_class.mult_ac(1) left_diff_distrib')
  also have "... \<longleftrightarrow> 2*(sqrt c * sqrt a - sqrt c * sqrt b - sqrt b * (sqrt a - sqrt b)) < y^2"
    by (smt (verit, del_insts) distrib_left)
  also have "... \<longleftrightarrow> 2*(sqrt c * sqrt a - sqrt c * sqrt b - sqrt b * sqrt a + sqrt b * sqrt b) < y^2"
    find_theorems "_ * (_ - _)"
    apply (subst Rings.ring_class.right_diff_distrib)
    back
    by auto
  also have "... \<longleftrightarrow> 2*(sqrt (c*a) - sqrt (c*b) - sqrt (b*a) + b) < y^2"
    using NthRoot.real_sqrt_mult
    using assms(5) by auto
  also have "... \<longleftrightarrow> 2*(sqrt (c*a) - sqrt (c*b) - sqrt (b*a) + b) < (sqrt c + sqrt a - sqrt b)^2"
    using assms
    by auto
  also have "... \<longleftrightarrow> 2*(sqrt (c*a) - sqrt (c*b) - sqrt (b*a) + b) < c + a + b + 2*sqrt(c*a) - 2*sqrt(c*b) - 2*sqrt(a*b)"
    using TrinSquareMinus
    using assms(4) assms(5) assms(6) by presburger
  also have "... \<longleftrightarrow> 2*sqrt(c*a) - 2*sqrt(c*b) - 2*sqrt(b*a) + 2*b < c + a + b + 2*sqrt(c*a) - 2*sqrt(c*b) - 2*sqrt(a*b)"
    by simp
  also have "... \<longleftrightarrow> b < c + a"
    by (simp add: mult.commute)
  also have "... \<longleftrightarrow> True"
    using assms
    by simp
  finally show ?thesis 
    by simp
qed






find_theorems "_ / _ \<le> _ / _"

(*
  Pokazuje da je izraz koji se u glavnoj lemi oduzima od trojke uvek nenegativan
  sto ce posle pokazati da je i sam izraz u glavnoj lemi manji ili jednak od 3. 
  Ovde pretpostavljamo da je x \<le> y \<le> z i onda koristmo kasnije za proizvoljan redosled.
*)

lemma FinalIneqUtil:
  fixes x y z :: "real"
  assumes "x > 0" "y > 0" "z > 0"
  assumes "x \<le> y" "y \<le> z"
  shows "(x-y)*(x-z)/x^2 + (z-x)*(z-y)/z^2 + (y-z)*(y-x)/y^2 \<ge> 0" (is "?e1/?d1 + ?e2/?d2 + ?e3/?d3  \<ge> 0")
proof-

  have "?e2 \<ge> 0"
    using assms
    by auto

  have "x^2 \<le> y^2"
    using assms
    by fastforce
    

  have "z - x \<ge> z - y"
    by (simp add: assms(4))

  have "?e1/?d1 = -(y-x)*(-(z-x))/?d1"
    by simp
  also have "... = (y-x)*(z-x)/?d1"
    by linarith

  have "- (y-z)*(y-x)/y^2 \<le> (x-y)*(x-z)/x^2"
    by (smt (z3) \<open>x\<^sup>2 \<le> y\<^sup>2\<close> \<open>z - y \<le> z - x\<close> assms(1) assms(5) frac_le mult.commute mult_le_cancel_right mult_minus_right zero_less_power)

  thm this
  from this have "- (y - z) * (y - x) / y^2 + (y - z) * (y - x) / y^2 \<le> (x - y) * (x - z) / x^2 + (y - z) * (y - x) / y^2"
    by simp
  from this have "0 \<le> (x - y) * (x - z) / x^2 + (y - z) * (y - x) / y^2"
    by (simp only: Groups.group_add_class.left_minus)
  from this have "(x - y) * (x - z) / x^2 + (y - z) * (y - x) / y^2 \<ge> 0"
    by simp

  have "z - x \<ge> 0"
    using assms
    by simp

  have "z - y \<ge> 0"
    using assms
    by simp

  have "z ^ 2 > 0"
    using assms(3) by auto

 
  have "(z-x)*(z-y) \<ge> 0"
    using \<open>0 \<le> z - x\<close> \<open>0 \<le> z - y\<close> by auto

  have "(z-x)*(z-y) / z^2 \<ge> 0"
    by (simp add: \<open>0 \<le> (z - x) * (z - y)\<close>)

  show ?thesis
    using \<open>0 \<le> (x - y) * (x - z) / x\<^sup>2 + (y - z) * (y - x) / y\<^sup>2\<close> \<open>0 \<le> (z - x) * (z - y) / z\<^sup>2\<close> by auto
qed 

(*
  Koristi prethodnu lemu da pokaze da ova nejednakost vazi za proizvoljan redosled.
*)

lemma FinalIneq:
  fixes x y z :: "real"
  assumes "x > 0" "y > 0" "z > 0"
  shows "(x-y)*(x-z)/x^2 + (z-x)*(z-y)/z^2 + (y-z)*(y-x)/y^2 \<ge> 0" (is "?e1/?d1 + ?e2/?d2 + ?e3/?d3  \<ge> 0")
proof(cases "x \<le> y")
  case True
  then show ?thesis
  proof(cases "y \<le> z") 
    case True (*x \<le> y i y \<le> z*)
    then show ?thesis 
      using `x \<le> y` `y \<le> z` assms
      by (simp add: FinalIneqUtil)
  next
    case False (*x \<le> y i y > z*)
    then show ?thesis 
    proof(cases "z \<le> x")
      case True (*x \<le> y i z \<le> x ---> z \<le> x \<le> y*)
      then show ?thesis 
        using `z \<le> x` `x \<le> y`
        using FinalIneqUtil[of z x y] assms
        by simp
    next
      case False (*x \<le> y i z > x \<longrightarrow> x \<le> z \<le> y*)
      then have "x \<le> z" "z \<le> y"
         apply auto[1]
        using `\<not> y \<le> z`
        by auto
      then show ?thesis 
        using `x \<le> z` `z \<le> y`
        using FinalIneqUtil[of x z y] assms
        by (smt (verit, ccfv_SIG) nonzero_divide_eq_eq nonzero_mult_div_cancel_left)
    qed
  qed
next
  case False
  then have "y < x"
    by auto
  then have "y \<le> x"
    by auto
  then show ?thesis 
  proof(cases "z \<ge> x")
    case True
    then have "x \<le> z"
      by simp
    then show ?thesis 
      using `y \<le> x` `x \<le> z`
      using FinalIneqUtil[of y x z] assms
      by (simp add: mult.commute)
  next
    case False
    then have "x > z"
      by auto
    then have "x \<ge> z"
      by auto
    then show ?thesis 
    proof(cases "z \<le> y")
      case True
      then show ?thesis 
        using `z \<le> y` `y \<le> x`
        using FinalIneqUtil[of z y x] assms
        by (simp add: mult.commute)
      next
        case False
        then have "z > y"
          by auto
        then have "z \<ge> y"
          by auto
        then have "y \<le> z"
          by auto
        then show ?thesis 
          using `y \<le> z` `z \<le> x`
          using FinalIneqUtil[of y z x] assms
          by linarith
      qed
  qed
qed

find_theorems "_ / _ / _"

(*
  Wrapper oko prethodne leme zbog pojave cetvorke u imeniocima.
*)

lemma FinalIneqWrapper:
  fixes x y z :: "real"
  assumes "x > 0" "y > 0" "z > 0"
  shows "(x-y)*(x-z)/(4*x^2) + (z-x)*(z-y)/(4*z^2) + (y-z)*(y-x)/(4*y^2) \<ge> 0" (is "?e1/?d1 + ?e2/?d2 + ?e3/?d3  \<ge> 0")
  using assms
proof-
  have "(x-y)*(x-z)/x^2 + (z-x)*(z-y)/z^2 + (y-z)*(y-x)/y^2 \<ge> 0"
    using assms
    using FinalIneq by blast
  from this have "((x-y)*(x-z)/x^2 + (z-x)*(z-y)/z^2 + (y-z)*(y-x)/y^2)/4 \<ge> 0"
    by simp
  from this have "(x-y)*(x-z)/x^2/4 + (z-x)*(z-y)/z^2/4 + (y-z)*(y-x)/y^2/4 \<ge> 0"
    by (simp add: add_divide_distrib)
  from this show ?thesis 
    by simp
    
qed

find_theorems "_*_ /(_*_)"

thm "mult_divide_mult_cancel_left"

(* Transformisanje sabiraka u xyz oblik koriscenjem smena *)

lemma XYZTransform:
  fixes a b c x y z :: "real"
  assumes "a > 0" "b > 0" "c > 0" "x > 0" "y > 0" "z > 0"
  assumes "x = sqrt b + sqrt c - sqrt a"
  assumes "y = sqrt c + sqrt a - sqrt b"
  assumes "z = sqrt a + sqrt b - sqrt c"
  shows "sqrt (1 + 2* (-(x-y)*(x-z) / (4*x^2))) = sqrt(b + c - a) / (sqrt b + sqrt c - sqrt a)" (is "?lhs = ?rhs")
proof-
  have "?lhs = sqrt (1 - (x-y)*(x-z)/(2*x^2))"
    apply simp
    by (smt (verit) mult.commute mult_minus_left times_divide_eq_left)
  also have "... = sqrt (2*x^2 / (2*x^2) -  (x-y)*(x-z)/(2*x^2))"
    apply simp
    using assms(4) by auto
  also have "... = sqrt ((2*x^2 - (x-y)*(x-z))/(2*x^2))"
    by (simp add: diff_divide_distrib)
  also have "... = sqrt ((2*(sqrt b + sqrt c - sqrt a)^2 - (2*sqrt b - 2* sqrt a)*(2*sqrt c - 2* sqrt a))/(2*x^2))"
    using assms
    by simp
  also have "... = sqrt (2*((sqrt b + sqrt c - sqrt a)^2 - 2*(sqrt b - sqrt a)*(sqrt c - sqrt a))/(2*x^2))"
    by simp
  also have "... = sqrt (((sqrt b + sqrt c - sqrt a)^2 - 2*(sqrt b - sqrt a)*(sqrt c - sqrt a))/x^2)"  
    by (simp only: mult_divide_mult_cancel_left)
  also have "... = sqrt ((b + c + a + 2*sqrt (b*c) - 2*sqrt(b*a) - 2*sqrt (c*a) - 2*(sqrt b - sqrt a)*(sqrt c - sqrt a))/x^2)"  
    using TrinSquareMinus
    by (simp add: assms(1) assms(2) assms(3))
  also have "... = sqrt ((b + c + a + 2*sqrt (b*c) - 2*sqrt(b*a) - 2*sqrt (c*a) - 2*(sqrt b * sqrt c - sqrt b * sqrt a - sqrt a * sqrt c + sqrt a * sqrt a))/x^2)"
    by (simp add: algebra_simps)
  also have "... = sqrt ((b + c + a + 2*sqrt (b*c) - 2*sqrt(b*a) - 2*sqrt (c*a) - 2*(sqrt(b*c) - sqrt(b*a) - sqrt(a*c) + a))/x^2)"
    find_theorems "sqrt _ * sqrt _"
    using `a > 0`
    by (simp add: NthRoot.real_sqrt_mult)
  also have "... = sqrt ((b + c + a + 2*sqrt (b*c) - 2*sqrt(b*a) - 2*sqrt (c*a) - 2*sqrt(b*c) + 2*sqrt(b*a) + 2*sqrt(a*c) -2*a)/x^2)"
    by simp
  also have "... = sqrt ((b + c - a)/x^2)"
    by (simp add: mult.commute)
  also have "... = sqrt (b + c - a)/sqrt(x^2)"
    by (simp add: real_sqrt_divide)
  also have "... = sqrt (b + c - a) / x"
    using `x > 0`
    by simp
  finally show ?thesis using assms by simp
  
qed

(*
Glavna lema
Uslov je da su a, b i c stranice trougla sto znaci da su strogo pozitivne
i da je zbir svake dve veci od trece (sto je zapisano putem triang_ineq definicija)
*)

lemma MainProblem:
  fixes a b c :: "real"
  assumes "a > 0" "b > 0" "c > 0"
  assumes "a + b > c" "a + c > b" "b + c > a"
  shows "sqrt(b + c - a) / (sqrt b + sqrt c - sqrt a)
        + sqrt (c + a - b) / (sqrt c + sqrt a - sqrt b)
        + sqrt(a + b - c)/(sqrt a + sqrt b - sqrt c) 
        \<le> 3" (is "?e1/?x + ?e2/?y + ?e3/?z \<le> 3")
  using assms
  
proof-

  (* Pokazujemo da su svi imenioci pozitivni *)
  have "?x > 0"
    using assms
    using DenPositive by blast
  have "?y > 0"
    using assms
    using DenPositive by fastforce
  have "?z > 0"
    using assms
    using DenPositive by auto

  (* Transformisemo sabirke preko XYZ smena *)
  have "?e1/?x = sqrt (1 + 2* (-(?x-?y)*(?x-?z) / (4*?x^2)))"
    using assms
    using XYZTransform
    using \<open>0 < sqrt a + sqrt b - sqrt c\<close> \<open>0 < sqrt b + sqrt c - sqrt a\<close> \<open>0 < sqrt c + sqrt a - sqrt b\<close> by presburger
  have "?e3/?z = sqrt (1 + 2* (-(?z-?x)*(?z-?y) / (4*?z^2)))"
    using assms
    using XYZTransform
    using \<open>0 < sqrt a + sqrt b - sqrt c\<close> \<open>0 < sqrt b + sqrt c - sqrt a\<close> \<open>0 < sqrt c + sqrt a - sqrt b\<close> by presburger
  have "?e2/?y = sqrt (1 + 2* (-(?y-?z)*(?y-?x) / (4*?y^2)))"
    using assms
    using XYZTransform
    using \<open>0 < sqrt a + sqrt b - sqrt c\<close> \<open>0 < sqrt b + sqrt c - sqrt a\<close> \<open>0 < sqrt c + sqrt a - sqrt b\<close> by presburger


  (* Pokazujemo da se UtilSubLemma moze primeniti na svaki sabirak,
     nakon cega je i primenjujemo  *)

  (*Prvi sabirak*)
  have "-(?x-?y)*(?x-?z)/(2*?x^2) = -2*(?x-?y)*(?x-?z)/(4*?x^2)"
    by (simp only: NthRoot.real_divide_square_eq)
  
  have "-(?x-?y)*(?x-?z)/(4*?x^2) > -1/2"
    using assms
    using FirstSubViable \<open>0 < sqrt a + sqrt b - sqrt c\<close> \<open>0 < sqrt b + sqrt c - sqrt a\<close> \<open>0 < sqrt c + sqrt a - sqrt b\<close> by blast

  from this have "?e1/?x \<le> 1 + (-(?x-?y)*(?x-?z)/(4*?x^2))"
    thm UtilSubLemma
    using UtilSubLemma
    using \<open>sqrt (b + c - a) / (sqrt b + sqrt c - sqrt a) = sqrt (1 + 2 * (- (sqrt b + sqrt c - sqrt a - (sqrt c + sqrt a - sqrt b)) * (sqrt b + sqrt c - sqrt a - (sqrt a + sqrt b - sqrt c)) / (4 * (sqrt b + sqrt c - sqrt a)\<^sup>2)))\<close> by presburger

  (*Treci sabirak*)

  have "-(?z-?x)*(?z-?y)/(2*?z^2) = -2*(?z-?x)*(?z-?y)/(4*?z^2)"
    by (simp only: NthRoot.real_divide_square_eq)  

  have "-(?z-?x)*(?z-?y)/(4*?z^2) > -1/2"
    using assms
    using SecondSubViable \<open>0 < sqrt a + sqrt b - sqrt c\<close> \<open>0 < sqrt b + sqrt c - sqrt a\<close> \<open>0 < sqrt c + sqrt a - sqrt b\<close> by blast

  from this have "?e3/?z \<le> 1 + (-(?z-?x)*(?z-?y)/(4*?z^2))"
    using UtilSubLemma
    using \<open>sqrt (a + b - c) / (sqrt a + sqrt b - sqrt c) = sqrt (1 + 2 * (- (sqrt a + sqrt b - sqrt c - (sqrt b + sqrt c - sqrt a)) * (sqrt a + sqrt b - sqrt c - (sqrt c + sqrt a - sqrt b)) / (4 * (sqrt a + sqrt b - sqrt c)\<^sup>2)))\<close> by presburger

  (*Drugi sabirak*)

  have "-(?y-?z)*(?y-?x)/(2*?y^2) = -2*(?y-?z)*(?y-?x)/(4*?y^2)"
    by (simp only: NthRoot.real_divide_square_eq)  

  have "-(?y-?z)*(?y-?x)/(4*?y^2) > -1/2"
    using assms
    using ThirdSubViable \<open>0 < sqrt a + sqrt b - sqrt c\<close> \<open>0 < sqrt b + sqrt c - sqrt a\<close> \<open>0 < sqrt c + sqrt a - sqrt b\<close> by blast

  from this have "?e2/?y \<le> 1 + (-(?y-?z)*(?y-?x)/(4*?y^2))"
    using UtilSubLemma
    using \<open>sqrt (c + a - b) / (sqrt c + sqrt a - sqrt b) = sqrt (1 + 2 * (- (sqrt c + sqrt a - sqrt b - (sqrt a + sqrt b - sqrt c)) * (sqrt c + sqrt a - sqrt b - (sqrt b + sqrt c - sqrt a)) / (4 * (sqrt c + sqrt a - sqrt b)\<^sup>2)))\<close> by presburger

  (* Sada za svaki sabirak imamo gornju granicu, pa je njihov zbir manji od zbira tih granica *)
  have "?e1/?x + ?e2/?y + ?e3/?z \<le>  1 + (-(?x-?y)*(?x-?z)/(4*?x^2)) + 1 + (-(?z-?x)*(?z-?y)/(4*?z^2)) + 1 + (-(?y-?z)*(?y-?x)/(4*?y^2))"
    using \<open>sqrt (a + b - c) / (sqrt a + sqrt b - sqrt c) \<le> 1 + - (sqrt a + sqrt b - sqrt c - (sqrt b + sqrt c - sqrt a)) * (sqrt a + sqrt b - sqrt c - (sqrt c + sqrt a - sqrt b)) / (4 * (sqrt a + sqrt b - sqrt c)\<^sup>2)\<close> \<open>sqrt (b + c - a) / (sqrt b + sqrt c - sqrt a) \<le> 1 + - (sqrt b + sqrt c - sqrt a - (sqrt c + sqrt a - sqrt b)) * (sqrt b + sqrt c - sqrt a - (sqrt a + sqrt b - sqrt c)) / (4 * (sqrt b + sqrt c - sqrt a)\<^sup>2)\<close> \<open>sqrt (c + a - b) / (sqrt c + sqrt a - sqrt b) \<le> 1 + - (sqrt c + sqrt a - sqrt b - (sqrt a + sqrt b - sqrt c)) * (sqrt c + sqrt a - sqrt b - (sqrt b + sqrt c - sqrt a)) / (4 * (sqrt c + sqrt a - sqrt b)\<^sup>2)\<close> by auto
  also have "... = 3 + (-(?x-?y)*(?x-?z)/(4*?x^2)) + (-(?z-?x)*(?z-?y)/(4*?z^2)) + (-(?y-?z)*(?y-?x)/(4*?y^2))"
    by simp
  also have "... = 3 - (?x-?y)*(?x-?z)/(4*?x^2) - (?z-?x)*(?z-?y)/(4*?z^2) - (?y-?z)*(?y-?x)/(4*?y^2)"
    by (simp only: Groups.group_add_class.diff_conv_add_uminus)
  also have "... = 3 - ((?x-?y)*(?x-?z)/(4*?x^2) + (?z-?x)*(?z-?y)/(4*?z^2) + (?y-?z)*(?y-?x)/(4*?y^2))"
    by simp
  finally have "?e1/?x + ?e2/?y + ?e3/?z \<le> 3 - ((?x-?y)*(?x-?z)/(4*?x^2) + (?z-?x)*(?z-?y)/(4*?z^2) + (?y-?z)*(?y-?x)/(4*?y^2))"
    by simp

  (* Znamo da je zbir manji od 3 - nesto. Pokazivanje da je to nesto nenegativno direktno implicira pocetnu tezu *)
  from this have "(?x-?y)*(?x-?z)/(4*?x^2) + (?z-?x)*(?z-?y)/(4*?z^2) + (?y-?z)*(?y-?x)/(4*?y^2) \<ge> 0 \<longrightarrow> ?thesis"
    using assms
    using SubPosIneq by blast

  (* Pokazujemo da je umanjenik nenegativan *)
  have "(?x-?y)*(?x-?z)/(4*?x^2) + (?z-?x)*(?z-?y)/(4*?z^2) + (?y-?z)*(?y-?x)/(4*?y^2) \<ge> 0"
    using FinalIneqWrapper \<open>0 < sqrt a + sqrt b - sqrt c\<close> \<open>0 < sqrt b + sqrt c - sqrt a\<close> \<open>0 < sqrt c + sqrt a - sqrt b\<close> by blast

  (* Iz poslednja dva pokazana tvrdjenja dirketno sledi glavna lema *)
  from this show ?thesis
    using \<open>0 \<le> (sqrt b + sqrt c - sqrt a - (sqrt c + sqrt a - sqrt b)) * (sqrt b + sqrt c - sqrt a - (sqrt a + sqrt b - sqrt c)) / (4 * (sqrt b + sqrt c - sqrt a)\<^sup>2) + (sqrt a + sqrt b - sqrt c - (sqrt b + sqrt c - sqrt a)) * (sqrt a + sqrt b - sqrt c - (sqrt c + sqrt a - sqrt b)) / (4 * (sqrt a + sqrt b - sqrt c)\<^sup>2) + (sqrt c + sqrt a - sqrt b - (sqrt a + sqrt b - sqrt c)) * (sqrt c + sqrt a - sqrt b - (sqrt b + sqrt c - sqrt a)) / (4 * (sqrt c + sqrt a - sqrt b)\<^sup>2) \<longrightarrow> sqrt (b + c - a) / (sqrt b + sqrt c - sqrt a) + sqrt (c + a - b) / (sqrt c + sqrt a - sqrt b) + sqrt (a + b - c) / (sqrt a + sqrt b - sqrt c) \<le> 3\<close> by blast
  
qed
  
  

end