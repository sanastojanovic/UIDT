theory mi16030_Sandra_Radojevic
  imports Complex_Main
begin

(*
  U pitanju je peti zadatak na linku:
  https://imomath.com/srb/zadaci/BIH_2013_bihmo_resenja.pdf
*)

(*I DEO*)
fun F3::"real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "F3 a b c = a*a + b*b + c*c -2*(a*b + b*c + a*c)"

value "F3 0.3 0.5 0.2"

fun F4::"real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "F4 a b c d = a*a + b*b + c*c +d*d -2*(a*b + b*c + c*d + d*a)"

fun F5::"real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "F5 a b c d e= a*a + b*b + c*c +d*d +e*e -2*(a*b + b*c + c*d + d*e +e*a)"

(*dokazati min f3 -1/3 , min f4 -1/4 , min f5 -1/5*)

lemma minf3:
  fixes a b c :: real
  assumes "a\<ge>0" "b\<ge>0" "c\<ge>0" "a+b+c=1" 
  shows "a*a + b*b + c*c -2*(a*b + b*c + a*c) \<ge> -(1::real)/(3::real)"
  sorry


lemma minf4:
  fixes a b c d:: real
  assumes "a\<ge>0" "b\<ge>0" "c\<ge>0" "d\<ge>0" "a+b+c+d=1" 
  shows "a*a + b*b + c*c +d*d -2*a*b-2*b*c -2*c*d-2*d*a \<ge> -(1::real)/(4::real)"
  sorry
  

lemma minf5:
  fixes a b c d e:: real
  assumes "a\<ge>0 \<and> b\<ge>0 \<and> c\<ge>0 \<and> d\<ge>0 \<and> e\<ge>0 \<and> a+b+c+d+e=1" 
  shows "a*a + b*b + c*c +d*d +e*e -2*(a*b + b*c + c*d + d*e +e*a) \<ge> -(1::real)/(5::real)"
  using assms
  sorry

(*II deo*)

lemma AKnejednakostZa3:
  fixes a b c :: real
  assumes "a\<ge>0" "b\<ge>0" "c\<ge>0"
  shows "(a+b+c)^2\<le>3*(a^2+b^2+c^2)"
  using assms
  by (smt power2_sum semiring_normalization_rules(8) sum_squares_bound)
  
lemma AKnejednakostZa4:
  fixes a b c d:: real
  assumes "a\<ge>0" "b\<ge>0" "c\<ge>0" "d\<ge>0"
  shows "(a+b+c+d)^2\<le>4*(a^2+b^2+c^2+d^2)"
  using assms
  by (smt power2_sum semiring_normalization_rules(8) sum_squares_bound)

lemma AKnejednakostZa5:
  fixes x y z v w:: real
  assumes "x\<ge>0" "y\<ge>0" "z\<ge>0" "v\<ge>0" "w\<ge>0"
  shows "(x+y+z+v+w)^2\<le>5*(x^2+y^2+z^2+v^2+w^2)"
  using assms arith_simps 
  by fastforce

(*pomocne leme za F4*)  
lemma agza4_pom:
  fixes x y:: real
  assumes "x\<ge>0" "y\<ge>0"
  shows "((x+y)^2)/4 \<ge> (x*y)"
  using arith_geo_mean_sqrt assms
  by blast


lemma agza4:
  fixes a b c d:: real
  assumes "a\<ge>0" "b\<ge>0" "c\<ge>0" "d\<ge>0"
  shows "((a+b+c+d)^2)/4 \<ge> (a+c)*(b+d)"
  using assms AKnejednakostZa4 agza4_pom [of "a+c" "b+d"]
  by smt

(*pomocne leme za F5*)

lemma AKpet:
  fixes a b c d e:: real
  assumes "a\<ge>0" "b\<ge>0" "c\<ge>0" "d\<ge>0" "e\<ge>0"
  shows "(a+c+b+d+c+e+d+a+e+b)^2 \<le>5*( (a+c)^2 +(b+d)^2+(c+e)^2+(d+a)^2+(e+b)^2) "
  using assms AKnejednakostZa5 [of "a+c" "b+d" "c+e" "d+a" "e+b"]
  by smt

lemma minf5_pom:
  fixes a b c d e:: real
  assumes "a\<ge>0" "b\<ge>0" "c\<ge>0" "d\<ge>0" "e\<ge>0" "a+b+c+d+e=1" 
  shows "a^2+b^2+c^2+d^2+e^2+a*c+b*d+c*e+d*a+e*b \<ge>2/5"
proof -
  have "a^2+b^2+c^2+d^2+e^2+a*c+b*d+c*e+d*a+e*b = 
                    ((a+c)^2 +(b+d)^2+(c+e)^2+(d+a)^2+(e+b)^2)/2"
    by (auto simp add: algebra_simps power2_eq_square)
  also have " ((a+c)^2 +(b+d)^2+(c+e)^2+(d+a)^2+(e+b)^2)/2 \<ge> (1/2)*(1/5)*(a+c+b+d+c+e+d+a+e+b)^2"
    using AKpet assms
    by (auto simp add:algebra_simps)
  also have "(1/2)*(1/5)*(a+c+b+d+c+e+d+a+e+b)^2 = (1/2)*(1/5)*(a+b+c+d+e+a+b+c+d+e)^2"
    by (auto simp add:algebra_simps)
  also have "... = (1/2)*(1/5)*(2)^2"
    using \<open>a+b+c+d+e=1\<close>
    by (auto simp add:algebra_simps)
  also have "... = (2::real)/(5::real)"
    by auto
  finally show ?thesis
    .
qed

lemma prvaekv:
  fixes a b c d e:: real
  assumes "a\<ge>0" "b\<ge>0" "c\<ge>0" "d\<ge>0" "e\<ge>0" "a+b+c+d+e=1" 
  shows "a*a + b*b + c*c +d*d +e*e-2*a*b-2*b*c -2*c*d-2*d*e -2*e*a = 
         1-4*(a*b+b*c+c*d+d*e+e*a)-2*(a*c+b*d+c*e+d*a+e*b)"
proof -
   have "a*a + b*b + c*c +d*d +e*e-2*a*b-2*b*c -2*c*d-2*d*e -2*e*a = 
        (a^2 + b^2 + c^2 +d^2 +e^2 +2*a*b + 2*a*c +2*a*d + 2*a*e
        +2*b*c+2*b*d+2*b*e+2*c*d +2*c*e +2*d*e) -2*a*b-2*b*c -2*c*d-2*d*e -2*e*a 
        -2*a*b - 2*a*c -2*a*d - 2*a*e-2*b*c-2*b*d-2*b*e-2*c*d -2*c*e -2*d*e"
    by (auto simp add:algebra_simps power2_eq_square)
  also have "... = (a+b+c+d+e)^2 -2*a*b-2*b*c -2*c*d-2*d*e -2*e*a 
        -2*a*b - 2*a*c -2*a*d - 2*a*e-2*b*c-2*b*d-2*b*e-2*c*d -2*c*e -2*d*e"
    by (auto simp add:algebra_simps power2_eq_square)
  also have "... = 1 -2*a*b-2*b*c -2*c*d-2*d*e -2*e*a 
        -2*a*b - 2*a*c -2*a*d - 2*a*e-2*b*c-2*b*d-2*b*e-2*c*d -2*c*e -2*d*e"
    using \<open>a+b+c+d+e=1\<close>
    by auto
  also have "... = 1-4*(a*b+b*c+c*d+d*e+e*a)-2*(a*c+b*d+c*e+d*a+e*b)"
    by (auto simp add:algebra_simps power2_eq_square)
  finally show ?thesis
    .
qed

lemma drugaekv:
  fixes a b c d e:: real
  assumes "a\<ge>0" "b\<ge>0" "c\<ge>0" "d\<ge>0" "e\<ge>0" "a+b+c+d+e=1" 
  shows "(3::real)/(5::real) \<le> (a^2 +b^2+c^2+d^2+e^2)+2*(a*b+b*c+c*d+d*e+e*a)
                +2*(a*c+b*d+c*e+d*a+e*b)-(2::real)/(5::real)"
  using one_le_power
  by blast
  
(*glavni dokazi*)
lemma minf3_raspisan:
  fixes a b c :: real
  assumes "a\<ge>0" "b\<ge>0" "c\<ge>0" "a+b+c=1" 
  shows "a*a + b*b + c*c -2*(a*b + b*c + a*c) \<ge> -(1::real)/(3::real)"
proof -
  have "a*a + b*b + c*c -2*(a*b + b*c + a*c) = a*a + b*b + c*c -2*a*b -2*b*c -2*a*c"
    by auto
  also have "... = 2*(a*a + b*b +c*c) - (a+b+c)*(a+b+c)"
    by (auto simp add:algebra_simps)
  also have "... = 2*(a^2 + b^2 +c^2) - 1*1"
    using \<open>a+b+c=1\<close>
    by (auto simp add: power2_eq_square)
  also have "... \<ge> (2/3)*((a+b+c)^2)-1"
    using AKnejednakostZa3 assms by fastforce
  also have "(2/3)*((a+b+c)^2)-1 = 2/3 * 1 -1"
    using \<open>a+b+c=1\<close>
    by auto
  also have "... = -(1::real)/(3::real)"
    by auto
  finally show ?thesis
    by simp
qed


lemma minf4_raspisan:
  fixes a b c d:: real
  assumes "a\<ge>0" "b\<ge>0" "c\<ge>0" "d\<ge>0" "a+b+c+d=1" 
  shows "a*a + b*b + c*c +d*d -2*a*b-2*b*c -2*c*d-2*d*a \<ge> -(1::real)/(4::real)"
proof-
  have "a*a + b*b + c*c +d*d-2*a*b-2*b*c -2*c*d-2*d*a = a^2+b^2+c^2+d^2-2*a*(b+d)-2*c*(b+d)"
    by (auto simp add:algebra_simps power2_eq_square)
  also have "a^2+b^2+c^2+d^2-2*a*(b+d)-2*c*(b+d) = a^2+b^2+c^2+d^2-2*(a+c)*(b+d)"
    by (auto simp add:algebra_simps)
  also have "a^2+b^2+c^2+d^2-2*(a+c)*(b+d) \<ge> (1/4)*((a+b+c+d)^2)-2*(a+c)*(b+d)"
    using assms AKnejednakostZa4
    by fastforce
  also have "(1/4)*((a+b+c+d)^2)-2*(a+c)*(b+d) = (1/4)*(1^2)-2*(a+c)*(b+d)"
    using \<open>a+b+c+d=1\<close>
    by auto
  also have "(1/4)*(1^2)-2*(a+c)*(b+d) = 1/4 - 2*(a+c)*(b+d)"
    by auto
  also have " 1/4 - 2*(a+c)*(b+d) \<ge> 1/4 - 2*((a+b+c+d)^2)/4"
    using assms agza4
    by fastforce
  then have "1/4 - 2*((a+b+c+d)^2)/4 = 1/4 - 2*1/4"
    using \<open>a+b+c+d=1\<close>
    by auto
  also have "... = -(1::real) / (4::real)"
    by auto
  finally show ?thesis
    using \<open>1 / 4 * (a + b + c + d)\<^sup>2 - 2 * (a + c) * (b + d) \<le> a\<^sup>2 + b\<^sup>2 + c\<^sup>2 + d\<^sup>2 - 2 * (a + c) * (b + d)\<close>
      \<open>1 / 4 - 2 * (a + b + c + d)\<^sup>2 / 4 = 1 / 4 - 2 * 1 / 4\<close>
        \<open>1 / 4 - 2 * (a + b + c + d)\<^sup>2 / 4 \<le> 1 / 4 - 2 * (a + c) * (b + d)\<close>
        \<open>a * a + b * b + c * c + d * d - 2 * a * b - 2 * b * c - 2 * c * d - 2 * d * a = a\<^sup>2 + b\<^sup>2 + c\<^sup>2 + d\<^sup>2 - 2 * a * (b + d) - 2 * c * (b + d)\<close> 
        \<open>a\<^sup>2 + b\<^sup>2 + c\<^sup>2 + d\<^sup>2 - 2 * a * (b + d) - 2 * c * (b + d) = a\<^sup>2 + b\<^sup>2 + c\<^sup>2 + d\<^sup>2 - 2 * (a + c) * (b + d)\<close>
    by auto
qed

lemma minf5_raspisan:
  fixes a b c d e:: real
  assumes "a\<ge>0" "b\<ge>0" "c\<ge>0" "d\<ge>0" "e\<ge>0" "a+b+c+d+e=1" 
  shows "(a^2 + b^2 + c^2 +d^2 +e^2-2*a*b-2*b*c -2*c*d-2*d*e -2*e*a \<ge> -(1::real)/(5::real))"
proof -
  have "(a*a + b*b + c*c +d*d +e*e-2*a*b-2*b*c -2*c*d-2*d*e -2*e*a \<ge> -(1::real)/(5::real))
    \<longleftrightarrow> (1-4*(a*b+b*c+c*d+d*e+e*a)-2*(a*c+b*d+c*e+d*a+e*b) \<ge> -(1::real)/(5::real))"
    using assms
    by (simp add: prvaekv)
  also have "(1-4*(a*b+b*c+c*d+d*e+e*a)-2*(a*c+b*d+c*e+d*a+e*b) \<ge> -(1::real)/(5::real)) 
        \<longleftrightarrow> (-4*(a*b+b*c+c*d+d*e+e*a)-2*(a*c+b*d+c*e+d*a+e*b) \<ge> -(6::real)/(5::real))"
    by linarith
  also have "(-4*(a*b+b*c+c*d+d*e+e*a)-2*(a*c+b*d+c*e+d*a+e*b) \<ge> -(6::real)/(5::real))
        \<longleftrightarrow> (2*(a*b+b*c+c*d+d*e+e*a)+(a*c+b*d+c*e+d*a+e*b) \<le> (3::real)/(5::real))"
    by auto
  also have "(2*(a*b+b*c+c*d+d*e+e*a)+(a*c+b*d+c*e+d*a+e*b) \<le> (3::real)/(5::real))
            \<longleftrightarrow> (2*(a*b+b*c+c*d+d*e+e*a)+(a*c+b*d+c*e+d*a+e*b) \<le> 
                (a^2 +b^2+c^2+d^2+e^2)+2*(a*b+b*c+c*d+d*e+e*a)
                +2*(a*c+b*d+c*e+d*a+e*b)-(2::real)/(5::real)) "
    using minf5_pom assms drugaekv
    by fastforce
  also have "(2*(a*b+b*c+c*d+d*e+e*a)+(a*c+b*d+c*e+d*a+e*b) \<le> 
                (a^2 +b^2+c^2+d^2+e^2)+2*(a*b+b*c+c*d+d*e+e*a)
                +2*(a*c+b*d+c*e+d*a+e*b)-(2::real)/(5::real)) 
              \<longleftrightarrow> ((2::real)/(5::real) \<le> a^2+b^2+c^2+d^2+e^2 + a*c+b*d+c*e+d*a+e*b)"
    using minf5_pom assms
    by smt
  finally show ?thesis
    using assms
    by (metis minf5_pom power2_eq_square)
qed
    
 

end