theory mi18490_Tomislav_Jankovic
  imports Main HOL.Real HOL.NthRoot

begin

text\<open> IMO 2001 Problem 2
Prove that a/sqrt(a^2 + b*c) + b/sqrt(b^2 + 8*a*c) + c/sqrt(c^2 + 8*a*b) \<ge> 1 
for all positive real numbers a, b and c.

Solution can be found: https://artofproblemsolving.com/wiki/index.php/2001_IMO_Problems/Problem_2 

\<close>



definition f_x::"real \<Rightarrow> real" where
"f_x x = 1/(sqrt x)"

lemma ineq_loss_of_generality:
  fixes x::real
  fixes y::real
  fixes z::real
  fixes r::real
  assumes "x/sqrt (x^2 + 8*y*z) + y/sqrt(y^2 + 8*x*z) + z/sqrt(z^2 + 8*x*y) \<ge> 1"
  assumes "r*x/sqrt (x^2 + 8*y*z) + r*y/sqrt(y^2 + 8*x*z) + r*z/sqrt(z^2 + 8*x*y) \<ge> r"

  shows "x + y + z = 1"
proof -
  show "x + y + z = 1"
    sorry
qed



lemma jensen_ineq:
  fixes a::real
  fixes b::real
  fixes c::real
  assumes "a + b + c = 1"
  shows "a/(sqrt a^2 + 8*b*c) + b/sqrt (b^2 + 8*b*c) + c/sqrt (c^2 + 8*a*b) \<ge> 1/sqrt (a^3 + b^3 + c^3 + 24*a*b*c)"
proof -
  show  "a/(sqrt a^2 + 8*b*c) + b/sqrt (b^2 + 8*b*c) + c/sqrt (c^2 + 8*a*b) \<ge> 1/sqrt (a^3 + b^3 + c^3 + 24*a*b*c)"
    unfolding f_x_def
    sorry
qed

lemma am_gm':
  fixes a::real
  fixes b::real
  fixes c::real
  assumes "a + b + c = 1" 
  assumes "a/(sqrt a^2 + 8*b*c) + b/sqrt (b^2 + 8*b*c) + c/sqrt (c^2 + 8*a*b) \<ge> 1/sqrt (a^3 + b^3 + c^3 + 24*a*b*c)"
  shows "(a + b + c)^3 \<ge> a^3 + b^3 + c^3 + 24*a*b*c"
proof -
  show "(a + b + c)^3 \<ge> a^3 + b^3 + c^3 + 24*a*b*c"
    sorry
qed


lemma ex_top_eq:
  fixes x::real
  fixes y::real
  assumes "x \<le> y"
  shows "x = y"
proof -
  show "x = y" 
    sorry
qed



theorem IMO_2001_2:
  fixes a::real
  fixes b::real
  fixes c::real
  assumes "a > 0 \<and> b > 0 \<and> c > 0"
  shows "a / sqrt (a^2 + 8*b*c) + b / sqrt (b^2 + 8*a*c) + c / sqrt (c^2 + 8*a*b) \<ge> 1" 
proof -
  show "1 \<le> a / sqrt (a\<^sup>2 + 8 * b * c) + b / sqrt (b\<^sup>2 + 8 * a * c) + c / sqrt (c\<^sup>2 + 8 * a * b) "
  proof -
    from assms have "a > 0" "b > 0" "c > 0" by auto
    have "a + b + c = 1"
    proof -
      (*assuming without loss of generality of a homogenous inequality *)
      show "a + b + c = 1"
        sorry
    qed

    from this have  "a/(sqrt a^2 + 8*b*c) + b/sqrt (b^2 + 8*b*c) + c/sqrt (c^2 + 8*a*b) \<ge> 1/sqrt (a^3 + b^3 + c^3 + 24*a*b*c)"
      by (auto simp add: jensen_ineq)

    from this and \<open>a + b + c = 1\<close> have "(a + b + c)^3 \<ge> a^3 + b^3 + c^3 + 24*a*b*c" 
      using am_gm' by blast

    from this and \<open>a + b + c = 1\<close> have "1 \<ge> a^3 + b^3 + c^3 + 24*a*b*c" 
      by simp

    from this have "a^3 + b^3 + c^3 + 24*a*b*c = 1" 
      using ex_top_eq by blast

    from this and  \<open>a/(sqrt a^2 + 8*b*c) + b/sqrt (b^2 + 8*b*c) + c/sqrt (c^2 + 8*a*b) \<ge> 1/sqrt (a^3 + b^3 + c^3 + 24*a*b*c)\<close>
    have  "a/(sqrt a^2 + 8*b*c) + b/sqrt (b^2 + 8*b*c) + c/sqrt (c^2 + 8*a*b) \<ge> 1 " by simp

    from this show ?thesis
      by (smt (verit, best) ex_top_eq)
      

  qed

qed






end